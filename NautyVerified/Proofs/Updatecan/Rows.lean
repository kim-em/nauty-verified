import NautyVerified.Proofs.Updatecan.Inv
import NautyVerified.Proofs.Permset.Satisfies
import NautyVerified.Proofs.Graph.Rows
import NautyVerified.Spec.Updatecan

/-!
# The row loop of `updatecan`

`wp_rows`: from row `samerows` on, each `permset(GRAPHROW(g, lab[i], M), ph, M, workperm)`
call writes row `i` of `canong` as HexGraphIso's `canStep` does.
-/

namespace NautyVerified.Proofs.Updatecan

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open NautyVerified.Proofs.Graph (GraphAt)
open Hex.GraphIso.Nauty (VSet invPerm Ctx)

variable {xi : ExternalCalls}

/-- What the row loop reads, and the blocks it must not write. -/
structure Frame {n : Nat} (m : mem) (le : temp_env) (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (grows : Array (VSet n)) (bc : block) (cofs : ptrofs)
    (bl : block) (lofs : ptrofs) (lab : Array Nat) (bW : block) (M : Nat) : Prop where
  hg : PTree.get id.g le = some (.Vptr bg gofs)
  hcan : PTree.get id.canong le = some (.Vptr bc cofs)
  hlab : PTree.get id.lab le = some (.Vptr bl lofs)
  hm : PTree.get id.m le = some (.Vint (ir M))
  hn : PTree.get id.n le = some (.Vint (ir n))
  graph : GraphAt m bg gofs gw grows M
  larr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n
  lsmall : ∀ j < n, lab[j]! < n
  warr : ArrayAt m .Mint32 bW 0 (ints (invPerm lab)) n
  wsmall : ∀ p < n, (invPerm lab)[p]! < n
  wptr : 0 < n → Mem.load .Mint64 m Block.naugraphWorkperm (zOfInt 0) = some (.Vptr bW Ptrofs.zero)
  lb : LeftbitTable m
  bit : BitTable m Block.nautilBit
  cg : bc ≠ bg
  cl : bc ≠ bl
  cW : 0 < n → bc ≠ bW
  cbit : bc ≠ Block.nautilBit
  clb : bc ≠ Block.leftbit
  cwp : bc ≠ Block.naugraphWorkperm
  M1 : 0 < M
  Mlt : M < 33554432
  nM : n ≤ 64 * M

theorem Frame.temps {n : Nat} {m : mem} {le le' : temp_env} {bg : block} {gofs : ptrofs}
    {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bc : block} {cofs : ptrofs}
    {bl : block} {lofs : ptrofs} {lab : Array Nat} {bW : block} {M : Nat}
    (h : Frame m le bg gofs gw grows bc cofs bl lofs lab bW M)
    (hle : ∀ x, x ≠ id.i → x ≠ id.ph → PTree.get x le' = PTree.get x le) :
    Frame m le' bg gofs gw grows bc cofs bl lofs lab bW M :=
  { h with
    hg := by rw [hle _ (by decide) (by decide)]; exact h.hg
    hcan := by rw [hle _ (by decide) (by decide)]; exact h.hcan
    hlab := by rw [hle _ (by decide) (by decide)]; exact h.hlab
    hm := by rw [hle _ (by decide) (by decide)]; exact h.hm
    hn := by rw [hle _ (by decide) (by decide)]; exact h.hn }

theorem Frame.unch {n : Nat} {m m' : mem} {le : temp_env} {bg : block} {gofs : ptrofs}
    {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bc : block} {cofs : ptrofs}
    {bl : block} {lofs : ptrofs} {lab : Array Nat} {bW : block} {M : Nat}
    (h : Frame m le bg gofs gw grows bc cofs bl lofs lab bW M) (hu : Unch m m' (· = bc)) :
    Frame m' le bg gofs gw grows bc cofs bl lofs lab bW M :=
  { h with
    graph := ⟨h.graph.arr.unch hu (Ne.symm h.cg), h.graph.rep⟩
    larr := h.larr.unch hu (Ne.symm h.cl)
    warr := by
      by_cases hn : n = 0
      · subst hn; exact ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
      · exact h.warr.unch hu (Ne.symm (h.cW (by omega)))
    wptr := fun hn => by rw [hu.load _ _ _ (Ne.symm h.cwp)]; exact h.wptr hn
    lb := fun i hi => by rw [hu.load _ _ _ (Ne.symm h.clb)]; exact h.lb i hi
    bit := h.bit.unch hu (Ne.symm h.cbit) }

theorem type_permset :
    type_of_fundef (.Internal Source.dense.fn.permset) =
      tfun [tptr tulong, tptr tulong, tint, tptr tint] .Tvoid := rfl

theorem foldl_range'_succ {β : Type} (f : β → Nat → β) (b : β) (a k : Nat) :
    (List.range' a (k + 1)).foldl f b = f ((List.range' a k).foldl f b) (a + k) := by
  rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul]

theorem foldl_canStep_size {n : Nat} (ctx : Ctx n) (lab : Array Nat) :
    ∀ (l : List Nat) (c : Array (VSet n)), (l.foldl (canStep ctx lab) c).size = c.size
  | [], _ => rfl
  | _ :: l, c => by rw [List.foldl_cons, foldl_canStep_size ctx lab l, canStep, Array.size_set!]

theorem wp_rows {Q : Post} {le : temp_env} {m : mem} {n : Nat} {bg : block} {gofs : ptrofs}
    {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bc : block} {cofs : ptrofs}
    {cw : Nat → Lib.Integers.int64} {canong : Array (VSet n)} {bl : block} {lofs : ptrofs}
    {lab : Array Nat} {bW : block} {M samerows : Nat}
    (h : Frame m le bg gofs gw grows bc cofs bl lofs lab bW M)
    (hcg : GraphAt m bc cofs cw canong M) (hcsz : canong.size = n) (hsr : samerows ≤ n)
    (hsrv : PTree.get id.samerows le = some (.Vint (ir samerows)))
    (hQ : ∀ le' m' cw', GraphAt m' bc cofs cw'
        (Hex.GraphIso.Nauty.updatecan ⟨grows⟩ canong lab samerows) M →
      Unch m m' (· = bc) → (∀ x, x ≠ id.i → x ≠ id.ph → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.updatecan rows Q empty_env le m := by
  have hM1 := h.M1
  have hMlt := h.Mlt
  have hnM := h.nM
  let basec := intOfZ (Ptrofs.unsigned cofs)
  let ctx : Ctx n := ⟨grows⟩
  let C := fun c => (List.range' samerows (c - samerows)).foldl (canStep ctx lab) canong
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ c cw', samerows ≤ c ∧ c ≤ n ∧ v = n - c ∧
      PTree.get id.i le' = some (.Vint (ir c)) ∧
      PTree.get id.ph le' = some (.Vptr bc (ptrTo basec 8 (M * c))) ∧
      GraphAt m' bc cofs cw' (C c) M ∧ Unch m m' (· = bc) ∧
      ∀ x, x ≠ id.i → x ≠ id.ph → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ c cw', samerows ≤ c ∧ c < n ∧ v = n - c ∧
      PTree.get id.i le' = some (.Vint (ir c)) ∧
      PTree.get id.ph le' = some (.Vptr bc (ptrTo basec 8 (M * c))) ∧
      GraphAt m' bc cofs cw' (C (c + 1)) M ∧ Unch m m' (· = bc) ∧
      ∀ x, x ≠ id.i → x ≠ id.ph → PTree.get x le' = PTree.get x le
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hsrv]
  apply wp_set_eval
  have hph0 : Exec.evalExpr ge empty_env (PTree.set id.i (.Vint (ir samerows)) le) m
      (row id.canong (tv id.samerows)) = some (.Vptr bc (ptrTo basec 8 (M * samerows))) := by
    simp only [Exec.evalExpr]
    rw [temps_gso _ _ (by decide), h.hcan, temps_gso _ _ (by decide), h.hm, temps_gso _ _ (by decide),
      hsrv]
    simp only [typeof, cop, cast_int_long_ir (a := (samerows : Int)) ⟨by omega, by omega⟩,
      Graph.mul_lr (show M < 2147483648 by omega)]
    rw [show ((M : Int) * (samerows : Int)) = ((M * samerows : Nat) : Int) by push_cast; rfl,
      Graph.add_ptrTo_long]
  rw [hph0]
  simp only [E0_append]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - samerows)
    ⟨rfl, rfl, samerows, cw, Nat.le_refl _, hsr, rfl, by rw [temps_gso _ _ (by decide), temps_gss],
      temps_gss _ _ _, by simpa [C] using hcg, Unch.refl _ _, fun x h1 h2 => by
        rw [temps_gso _ _ h2, temps_gso _ _ h1]⟩
  · rintro v t e' le' m' ⟨rfl, rfl, c, cw', hsc, hcn, rfl, hi, hph, hcg', hu, ho⟩
    have hf := (h.temps ho).unch hu
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' (tv id.i) = _ from hi,
      show Exec.evalExpr ge empty_env le' m' (tv id.n) = _ from hf.hn]
    simp only [typeof, cop]
    rw [ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hc : c < n
    · rw [ite_eq_left (by simpa using hc)]
      apply wp_skip
      have hlc := hf.lsmall c hc
      have hle := eval_at (ge := ge) (e := empty_env) hf.larr (by omega) id.lab hf.hlab (tv id.i) c hc hi rfl
      let baseg := intOfZ (Ptrofs.unsigned gofs)
      have hrowg : Exec.evalExpr ge empty_env le' m' (row id.g (labAt (tv id.i))) =
          some (.Vptr bg (ptrTo baseg 8 (M * lab[c]!))) := by
        have e1 : Exec.evalExpr ge empty_env le' m' (.Ecast (Set.pv id.g) (tptr tulong)) =
            some (.Vptr bg gofs) := by simp only [Exec.evalExpr, hf.hg, typeof, cop]
        have e3 : Exec.evalExpr ge empty_env le' m' (.Ecast (labAt (tv id.i)) tulong) =
            some (.Vlong (lr (lab[c]! : Int))) := by
          rw [Exec.evalExpr, hle]
          simp only [ints, typeof, cop, cast_int_long_ir (a := (lab[c]! : Int)) ⟨by omega, by omega⟩]
        rw [Exec.evalExpr, e1, Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' (tv id.m) = _ from hf.hm, e3]
        simp only [typeof, cop, Graph.mul_lr (show M < 2147483648 by omega)]
        rw [show ((M : Int) * (lab[c]! : Int)) = ((M * lab[c]! : Nat) : Int) by push_cast; rfl,
          Graph.add_ptrTo_long]
      have hcsz' : (C c).size = n := by rw [foldl_canStep_size, hcsz]
      wp_step; wp_step
      refine wp_call (vf := .Vptr Block.permset Ptrofs.zero)
        (targs := [tptr tulong, tptr tulong, tint, tptr tint]) (tres := .Tvoid)
        (cc := Common.AST.cc_default) _
        (Permset.permsetSpec bg (ptrTo baseg 8 (M * lab[c]!)) (fun j => gw (M * lab[c]! + j)) grows[lab[c]!]!
          bc (ptrTo basec 8 (M * c)) (fun j => cw' (M * c + j)) bW Ptrofs.zero (invPerm lab) M)
        (Permset.permset_satisfies _ _ _ _ _ _ _ _ _ _ _) rfl
        (by simp only [Exec.evalExpr, Exec.lvalOfVar,
          show PTree.get Source.dense.id.permset (empty_env : env) = none from rfl,
          find_permset, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
        (by simp only [Exec.evalExprlist]
            rw [hrowg]
            simp only [Exec.evalExpr, hph, hf.hm, Exec.lvalOfVar,
              show PTree.get id.wp (empty_env : env) = none from rfl, find_naugraphWorkperm,
              Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
              show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hf.wptr (by omega), typeof, cop])
        (by simp [Common.Globalenvs.Genv.find_funct, funct_permset]) type_permset
        ⟨rfl, hf.graph.row hlc, hf.graph.rep _ hlc, Graph.GraphAt.row hcg' hc, hf.warr, hf.wsmall,
          hf.lb, hf.bit, hf.cg, hf.cW (by omega), hf.cbit, hf.clb, hM1, hMlt⟩ ?_
      rintro t r m2 ⟨rfl, w2', harr2, hrep2, hu2, hout2⟩
      refine ⟨by simp, rfl, c, Graph.rowSet cw' M c w2', hsc, hc, rfl, hi, hph, ?_, hu.trans hu2, ho⟩
      have := Graph.GraphAt.setRow hcg' hc hcsz' harr2 hrep2 hout2
      have hC : C (c + 1) = (C c).set! c (grows[lab[c]!]!.permset (invPerm lab)) := by
        simp only [C]
        rw [show c + 1 - samerows = (c - samerows) + 1 by omega, foldl_range'_succ,
          show samerows + (c - samerows) = c by omega]
        rfl
      rw [hC]; exact this
    · rw [ite_eq_right (by simpa using hc)]
      apply wp_break
      have hcn' : c = n := by omega
      subst hcn'
      have hC : C c = Hex.GraphIso.Nauty.updatecan ⟨grows⟩ canong lab samerows := by
        simp only [C]; rw [updatecan_eq]
      rw [hC] at hcg'
      simpa using hQ le' m' cw' hcg' hu ho
  · rintro v t e' le' m' ⟨rfl, rfl, c, cw', hsc, hcn, rfl, hi, hph, hcg', hu, ho⟩
    have hf := (h.temps ho).unch hu
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' (tv id.i) = _ from hi]
    simp only [Exec.evalExpr, typeof, cop, ir_add]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    rw [temps_gso _ _ (by decide), hph, temps_gso _ _ (by decide), hf.hm]
    simp only [typeof, cop]
    rw [Prune.Long.add_ptrTo8 _ _ _ _ (by omega)]
    refine ⟨n - (c + 1), by omega, by simp, rfl, c + 1, cw', by omega, by omega, rfl,
      by rw [temps_gso _ _ (by decide), temps_gss]; rfl, by rw [temps_gss, Nat.mul_succ], hcg', hu,
      fun x h1 h2 => by rw [temps_gso _ _ h2, temps_gso _ _ h1, ho x h1 h2]⟩

end NautyVerified.Proofs.Updatecan

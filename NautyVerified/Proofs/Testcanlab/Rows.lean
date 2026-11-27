import NautyVerified.Proofs.Testcanlab.Cmp
import NautyVerified.Proofs.Updatecan.Rows
import NautyVerified.Proofs.Alloc.Keep
import NautyVerified.Spec.Testcanlab

/-!
# The row loop of `testcanlab`

`wp_rows`: row by row, `permset` writes row `lab[i]` of `g` renamed into
`workset`, and the word comparison with row `i` of `canong` either returns
(as HexGraphIso's `tclGo` stops) or moves on.
-/

namespace NautyVerified.Proofs.Testcanlab

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Alloc (Keep)
open NautyVerified.Proofs.Updatecan (tv labAt row)
open Hex.GraphIso.Nauty (VSet invPerm Ctx)

variable {xi : ExternalCalls}

/-- What `testcanlab`'s row loop reads, and the blocks `workset` must avoid. -/
structure Frame {n : Nat} (m : mem) (le : temp_env) (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (grows : Array (VSet n)) (bc : block) (cofs : ptrofs)
    (cw : Nat → Lib.Integers.int64) (canong : Array (VSet n)) (bl : block) (lofs : ptrofs)
    (lab : Array Nat) (bW bWS bs : block) (so : ptrofs) (M : Nat) : Prop where
  hg : PTree.get id.g le = some (.Vptr bg gofs)
  hcan : PTree.get id.canong le = some (.Vptr bc cofs)
  hlab : PTree.get Updatecan.id.lab le = some (.Vptr bl lofs)
  hsr : PTree.get id.samerows le = some (.Vptr bs so)
  hm : PTree.get id.m le = some (.Vint (ir M))
  hn : PTree.get id.n le = some (.Vint (ir n))
  graph : GraphAt m bg gofs gw grows M
  cgraph : GraphAt m bc cofs cw canong M
  larr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n
  lsmall : ∀ j < n, lab[j]! < n
  warr : ArrayAt m .Mint32 bW 0 (ints (invPerm lab)) n
  wsmall : ∀ p < n, (invPerm lab)[p]! < n
  wptr : 0 < n → Mem.load .Mint64 m Block.naugraphWorkperm (zOfInt 0) = some (.Vptr bW Ptrofs.zero)
  wsptr : Mem.load .Mint64 m Block.naugraphWorkset (zOfInt 0) = some (.Vptr bWS Ptrofs.zero)
  lb : LeftbitTable m
  bit : BitTable m Block.nautilBit
  sg : bWS ≠ bg
  sc : bWS ≠ bc
  sl : bWS ≠ bl
  sW : 0 < n → bWS ≠ bW
  sbit : bWS ≠ Block.nautilBit
  slb : bWS ≠ Block.leftbit
  swp : bWS ≠ Block.naugraphWorkperm
  sws : bWS ≠ Block.naugraphWorkset
  M1 : 0 < M
  Mlt : M < 33554432
  nM : n ≤ 64 * M

theorem Frame.temps {n : Nat} {m : mem} {le le' : temp_env} {bg : block} {gofs : ptrofs}
    {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bc : block} {cofs : ptrofs}
    {cw : Nat → Lib.Integers.int64} {canong : Array (VSet n)} {bl : block} {lofs : ptrofs}
    {lab : Array Nat} {bW bWS bs : block} {so : ptrofs} {M : Nat}
    (h : Frame m le bg gofs gw grows bc cofs cw canong bl lofs lab bW bWS bs so M)
    (hle : ∀ x, x ≠ id.i → x ≠ id.ph → x ≠ id.j → PTree.get x le' = PTree.get x le) :
    Frame m le' bg gofs gw grows bc cofs cw canong bl lofs lab bW bWS bs so M :=
  { h with
    hg := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hg
    hcan := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hcan
    hlab := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hlab
    hsr := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hsr
    hm := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hm
    hn := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hn }

theorem Frame.unch {n : Nat} {m m' : mem} {le : temp_env} {bg : block} {gofs : ptrofs}
    {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bc : block} {cofs : ptrofs}
    {cw : Nat → Lib.Integers.int64} {canong : Array (VSet n)} {bl : block} {lofs : ptrofs}
    {lab : Array Nat} {bW bWS bs : block} {so : ptrofs} {M : Nat}
    (h : Frame m le bg gofs gw grows bc cofs cw canong bl lofs lab bW bWS bs so M)
    (hu : Unch m m' (· = bWS)) :
    Frame m' le bg gofs gw grows bc cofs cw canong bl lofs lab bW bWS bs so M :=
  { h with
    graph := ⟨h.graph.arr.unch hu (Ne.symm h.sg), h.graph.rep⟩
    cgraph := ⟨h.cgraph.arr.unch hu (Ne.symm h.sc), h.cgraph.rep⟩
    larr := h.larr.unch hu (Ne.symm h.sl)
    warr := by
      by_cases hn : n = 0
      · subst hn; exact ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
      · exact h.warr.unch hu (Ne.symm (h.sW (by omega)))
    wptr := fun hn => by rw [hu.load _ _ _ (Ne.symm h.swp)]; exact h.wptr hn
    wsptr := by rw [hu.load _ _ _ (Ne.symm h.sws)]; exact h.wsptr
    lb := fun i hi => by rw [hu.load _ _ _ (Ne.symm h.slb)]; exact h.lb i hi
    bit := h.bit.unch hu (Ne.symm h.sbit) }

theorem tclGo_range'_succ {n : Nat} (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat)
    (c k : Nat) :
    tclGo ctx canong lab (List.range' c (k + 1)) =
      match (ctx.g[lab[c]!]!.permset (invPerm lab)).rowCmp canong[c]! with
      | .lt => (-1, c)
      | .gt => (1, c)
      | .eq => tclGo ctx canong lab (List.range' (c + 1) k) := by
  rw [List.range'_succ, tclGo]
  rfl

theorem wp_rows {Q : Post} {le : temp_env} {m : mem} {n : Nat} {bg : block} {gofs : ptrofs}
    {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bc : block} {cofs : ptrofs}
    {cw : Nat → Lib.Integers.int64} {canong : Array (VSet n)} {bl : block} {lofs : ptrofs}
    {lab : Array Nat} {bW bWS bs : block} {so : ptrofs} {M : Nat} {ws0 : Nat → val}
    {vals : Nat → val}
    (h : Frame m le bg gofs gw grows bc cofs cw canong bl lofs lab bW bWS bs so M)
    (hws0 : ArrayAt m .Mint64 bWS 0 ws0 M)
    (hsarr : ArrayAt m .Mint32 bs (intOfZ (Ptrofs.unsigned so)) vals 1) (hsW : bs ≠ bWS)
    (hQn : tclGo ⟨grows⟩ canong lab (List.range n) = (0, n) → ∀ le' m' (ws' : Nat → val),
      ArrayAt m' .Mint64 bWS 0 ws' M → Unch m m' (· = bWS) → Keep m m' bWS →
      (∀ x, x ≠ id.i → x ≠ id.ph → x ≠ id.j → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m')
    (hQr : ∀ m' (r : Int) c, tclGo ⟨grows⟩ canong lab (List.range n) = (r, c) →
      ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so)) (fun _ => .Vint (ir c)) 1 →
      Unch m m' (fun z => z = bWS ∨ z = bs) → Keep m m' bWS → Q.ret E0 (.Vint (ir r)) m') :
    Wp xi ge Source.dense.fn.testcanlab rows Q empty_env le m := by
  have hM1 := h.M1
  have hMlt := h.Mlt
  have hnM := h.nM
  have hn : n < 2147483648 := by omega
  let basec := intOfZ (Ptrofs.unsigned cofs)
  let baseg := intOfZ (Ptrofs.unsigned gofs)
  let ctx : Ctx n := ⟨grows⟩
  let T := tclGo ctx canong lab (List.range n)
  let Oth := fun le' : temp_env => ∀ x, x ≠ id.i → x ≠ id.ph → x ≠ id.j → PTree.get x le' = PTree.get x le
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ (c : Nat) (ws' : Nat → val), c ≤ n ∧ v = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
      PTree.get id.ph le' = some (.Vptr bc (ptrTo basec 8 (M * c))) ∧
      T = tclGo ctx canong lab (List.range' c (n - c)) ∧
      ArrayAt m' .Mint64 bWS 0 ws' M ∧ Unch m m' (· = bWS) ∧ Keep m m' bWS ∧ Oth le'
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ (c : Nat) (ws' : Nat → val), c < n ∧ v = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
      PTree.get id.ph le' = some (.Vptr bc (ptrTo basec 8 (M * c))) ∧
      T = tclGo ctx canong lab (List.range' (c + 1) (n - (c + 1))) ∧
      ArrayAt m' .Mint64 bWS 0 ws' M ∧ Unch m m' (· = bWS) ∧ Keep m m' bWS ∧ Oth le'
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  apply wp_set_eval
  simp only [Exec.evalExpr]
  rw [temps_gso _ _ (by decide), h.hcan]
  simp only [E0_append]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0)
    ⟨rfl, rfl, 0, ws0, Nat.zero_le _, rfl, by rw [temps_gso _ _ (by decide), temps_gss]; rfl,
      by rw [temps_gss, Nat.mul_zero, Graph.ptrTo_zero], by simp [T, List.range_eq_range'], hws0,
      Unch.refl _ _, Keep.refl _ _, fun x h1 h2 _ => by rw [temps_gso _ _ h2, temps_gso _ _ h1]⟩
  · rintro v t e' le' m' ⟨rfl, rfl, c, ws', hcn, rfl, hi, hph, hT, harr', hu, hk, ho⟩
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
      have hle := eval_at (ge := ge) (e := empty_env) hf.larr hn Updatecan.id.lab hf.hlab (tv id.i) c hc hi rfl
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
      wp_step; wp_step; wp_step
      refine wp_call (vf := .Vptr Block.permset Ptrofs.zero)
        (targs := [tptr tulong, tptr tulong, tint, tptr tint]) (tres := .Tvoid)
        (cc := Common.AST.cc_default) _
        (Permset.permsetSpec bg (ptrTo baseg 8 (M * lab[c]!)) (fun j => gw (M * lab[c]! + j)) grows[lab[c]!]!
          bWS Ptrofs.zero ws' bW Ptrofs.zero (invPerm lab) M)
        (Permset.permset_satisfies _ _ _ _ _ _ _ _ _ _ _) rfl
        (by simp only [Exec.evalExpr, Exec.lvalOfVar,
          show PTree.get Source.dense.id.permset (empty_env : env) = none from rfl,
          find_permset, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
        (by simp only [Exec.evalExprlist]
            rw [hrowg]
            simp only [Exec.evalExpr, hf.hm, Exec.lvalOfVar,
              show PTree.get id.wp (empty_env : env) = none from rfl,
              show PTree.get id.ws (empty_env : env) = none from rfl, find_naugraphWorkperm,
              find_naugraphWorkset, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
              show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hf.wptr (by omega), hf.wsptr, typeof, cop])
        (by simp [Common.Globalenvs.Genv.find_funct, funct_permset]) Updatecan.type_permset
        ⟨rfl, hf.graph.row hlc, hf.graph.rep _ hlc, harr', hf.warr, hf.wsmall, hf.lb, hf.bit, hf.sg,
          hf.sW (by omega), hf.sbit, hf.slb, hM1, hMlt⟩ ?_
      rintro t r m2 ⟨rfl, ws'', harr2, hrep2, hu2, hout2⟩
      have hk2 : Keep m' m2 bWS := Keep.of_outside (hi := 0 + 8 * M) hout2
      have hf2 := hf.unch hu2
      have hsarr2 := (hsarr.unch hu hsW).unch hu2 hsW
      have hrowc := hf2.cgraph.rep c hc
      have hcmp : wordScan (fun w => bv64 (ws'' w)) (fun w => bv64 (cw (M * c + w))) M 0 =
          (grows[lab[c]!]!.permset (invPerm lab)).rowCmp canong[c]! :=
        wordScan_eq hrep2 hrowc M 0 (by omega) (fun w hw => absurd hw (by omega))
      have hTc : T = match (grows[lab[c]!]!.permset (invPerm lab)).rowCmp canong[c]! with
          | .lt => (-1, c) | .gt => (1, c)
          | .eq => tclGo ctx canong lab (List.range' (c + 1) (n - (c + 1))) := by
        rw [hT, show n - c = (n - (c + 1)) + 1 by omega, tclGo_range'_succ]
      simp only [set_opttemp]
      refine wp_cmp (fun _ => hf2.wsptr) harr2 hph
        (Graph.GraphAt.row hf2.cgraph hc) hf2.hsr hsarr2 hi hf2.hm (by omega) ?_ ?_
      · intro heq le2 ho2
        rw [hcmp] at heq
        rw [heq] at hTc
        refine ⟨by simp, rfl, c, longs ws'', hc, rfl, by rw [ho2 _ (by decide)]; exact hi,
          by rw [ho2 _ (by decide)]; exact hph, hTc, harr2, hu.trans hu2, hk.trans hk2,
          fun x h1 h2 h3 => by rw [ho2 x h3, ho x h1 h2 h3]⟩
      · intro m3 harr3 hu3
        have hU : Unch m m3 (fun z => z = bWS ∨ z = bs) :=
          ((hu.trans hu2).mono fun z hz => .inl hz).trans (hu3.mono fun z hz => .inr hz)
        have hK : Keep m m3 bWS := (hk.trans hk2).trans (Keep.unch hu3 (Ne.symm hsW))
        refine ⟨fun hlt => ?_, fun hgt => ?_⟩
        · rw [hcmp] at hlt
          rw [hlt] at hTc
          exact hQr m3 (-1) c hTc harr3 hU hK
        · rw [hcmp] at hgt
          rw [hgt] at hTc
          exact hQr m3 1 c hTc harr3 hU hK
    · rw [ite_eq_right (by simpa using hc)]
      apply wp_break
      have hcn' : n - c = 0 := by omega
      have hT0 : T = (0, n) := by rw [hcn'] at hT; exact hT
      exact hQn hT0 le' m' ws' harr' hu hk ho
  · rintro v t e' le' m' ⟨rfl, rfl, c, ws', hcn, rfl, hi, hph, hT, harr', hu, hk, ho⟩
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
    refine ⟨n - (c + 1), by omega, by simp, rfl, c + 1, ws', by omega, rfl,
      by rw [temps_gso _ _ (by decide), temps_gss]; rfl, by rw [temps_gss, Nat.mul_succ], hT, harr', hu, hk,
      fun x h1 h2 h3 => by rw [temps_gso _ _ h2, temps_gso _ _ h1, ho x h1 h2 h3]⟩

end NautyVerified.Proofs.Testcanlab

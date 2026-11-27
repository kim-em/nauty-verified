import NautyVerified.Proofs.Isautom.Syntax
import NautyVerified.Proofs.Graph.Rows
import NautyVerified.Logic.Ints

/-!
# The row scan of `isautom`

`wp_scan`: for row `i` of the graph (at `pg`) and row `perm[i]` (at `pgp`),
the loop over the members of row `i` above `i` returns `FALSE` if one of
them is not mapped into row `perm[i]`, and otherwise ends normally.
-/

namespace NautyVerified.Proofs.Isautom

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs BitTable)
open NautyVerified.Proofs.Graph (GraphAt)
open Hex.GraphIso.Nauty (VSet)

variable {xi : ExternalCalls}

/-- Row `v` maps into row `perm[v]` at every member above `v`. -/
def RowOK {n : Nat} (rows : Array (VSet n)) (perm : Array Nat) (v : Nat) : Prop :=
  ∀ pos, rows[v]!.mem pos = true → v < pos → rows[perm[v]!]!.mem perm[pos]! = true

/-- What `isautom` reads. -/
structure Frame {n : Nat} (m : mem) (le : temp_env) (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (rows : Array (VSet n)) (bpm : block) (pofs : ptrofs)
    (perm : Array Nat) (M : Nat) : Prop where
  hg : PTree.get id.g le = some (.Vptr bg gofs)
  hperm : PTree.get id.perm le = some (.Vptr bpm pofs)
  hm : PTree.get id.m le = some (.Vint (ir M))
  hn : PTree.get id.n le = some (.Vint (ir n))
  hdig : PTree.get id.digraph le = some (.Vint (ir 0))
  graph : GraphAt m bg gofs gw rows M
  parr : ArrayAt m .Mint32 bpm (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n
  psmall : ∀ x, x < n → perm[x]! < n
  bit : BitTable m Block.naugraphBit
  lb : Nextelement.LeftbitTable m
  M1 : 1 ≤ M
  M64 : 64 * M < 2147483648
  nM : n ≤ 64 * M

theorem Frame.temps {n : Nat} {m : mem} {le le' : temp_env} {bg : block} {gofs : ptrofs}
    {gw : Nat → Lib.Integers.int64} {rows : Array (VSet n)} {bpm : block} {pofs : ptrofs}
    {perm : Array Nat} {M : Nat} (h : Frame m le bg gofs gw rows bpm pofs perm M)
    (hle : ∀ x, x ≠ id.pg → x ≠ id.pos → x ≠ id.pgp → x ≠ id.posp → x ≠ id.i → x ≠ id.t1 →
      x ≠ id.t2 → x ≠ id.t3 → PTree.get x le' = PTree.get x le) :
    Frame m le' bg gofs gw rows bpm pofs perm M :=
  { h with
    hg := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.hg
    hperm := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.hperm
    hm := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.hm
    hn := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.hn
    hdig := by rw [hle _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.hdig }

theorem type_nextelement :
    type_of_fundef (.Internal Source.dense.fn.nextelement) =
      tfun [tptr tulong, tint, tint] tint := rfl

theorem inSet_iff {n M v : Nat} {ws : Nat → Lib.Integers.int64} {s : VSet n}
    (hs : SetRep (fun w => bv64 (ws w)) M s) :
    Nextelement.InSet (fun w => bv64 (ws w)) M v ↔ s.mem v = true := by
  constructor
  · rintro ⟨hv, hb⟩
    rw [← hs.2 v hv]; exact hb
  · intro hm
    have hvn := VSet.mem_lt hm
    have hv : v < 64 * M := Nat.lt_of_lt_of_le hvn hs.1
    exact ⟨hv, by rw [← hs.2 v hv] at hm; exact hm⟩

theorem wp_scan {Q : Post} {le : temp_env} {m : mem} {bg : block} {gofs : ptrofs}
    {gw : Nat → Lib.Integers.int64} {n : Nat} {rows : Array (VSet n)} {bpm : block} {pofs : ptrofs}
    {perm : Array Nat} {M v : Nat} (h : Frame m le bg gofs gw rows bpm pofs perm M) (hv : v < n)
    (hpg : PTree.get id.pg le =
      some (.Vptr bg (ptrTo (intOfZ (Ptrofs.unsigned gofs)) 8 (M * v))))
    (hpgp : PTree.get id.pgp le =
      some (.Vptr bg (ptrTo (intOfZ (Ptrofs.unsigned gofs)) 8 (M * perm[v]!))))
    (hpos : PTree.get id.pos le = some (.Vint (ir v)))
    (hQn : RowOK rows perm v → ∀ le', (∀ x, x ≠ id.pos → x ≠ id.posp → x ≠ id.t2 → x ≠ id.t3 →
      PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m)
    (hQr : ¬ RowOK rows perm v → Q.ret E0 (.Vint (ir 0)) m) :
    Wp xi ge Source.dense.fn.isautom scan Q empty_env le m := by
  have hM1 := h.M1
  have hM64 := h.M64
  have hnM := h.nM
  have hpv := h.psmall v hv
  let base := intOfZ (Ptrofs.unsigned gofs)
  let ws : Nat → Lib.Integers.int64 := fun w => gw (M * v + w)
  let wsp : Nat → Lib.Integers.int64 := fun w => gw (M * perm[v]! + w)
  have hrow := h.graph.row hv
  have hrowp := h.graph.row hpv
  have hrep : SetRep (fun w => bv64 (ws w)) M rows[v]! := h.graph.rep v hv
  have hrepp : SetRep (fun w => bv64 (wsp w)) M rows[perm[v]!]! := h.graph.rep _ hpv
  have hwords := Graph.wordsAt_of hrow
  let Oth := fun le' : temp_env => ∀ x, x ≠ id.pos → x ≠ id.posp → x ≠ id.t2 → x ≠ id.t3 →
    PTree.get x le' = PTree.get x le
  let Checked := fun p : Int => ∀ q : Nat, (v : Int) < q → (q : Int) ≤ p → rows[v]!.mem q = true →
    rows[perm[v]!]!.mem perm[q]! = true
  let I := fun (k : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ p : Int, (v : Int) ≤ p ∧ p < 64 * M ∧ k = (64 * M - p).toNat ∧
      PTree.get id.pos le' = some (.Vint (ir p)) ∧ Checked p ∧ Oth le'
  refine wp_loop (I := I) (J := fun k t e' le' m' => ∃ k', k' < k ∧ I k' t e' le' m') ?_ ?_
    (n := (64 * M - (v : Int)).toNat)
    ⟨rfl, rfl, rfl, v, Int.le_refl _, by omega, rfl, hpos, fun q h1 h2 _ => absurd h2 (by omega),
      fun _ _ _ _ _ => rfl⟩
  · rintro k t e' le' m' ⟨rfl, rfl, rfl, p, hp1, hp2, rfl, hposp, hchk, ho⟩
    have hf := h.temps fun x _ h2 h3 h4 _ _ h7 h8 => ho x h2 h4 h7 h8
    have hpg' : PTree.get id.pg le' = some (.Vptr bg (ptrTo base 8 (M * v))) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide)]; exact hpg
    have hpgp' : PTree.get id.pgp le' = some (.Vptr bg (ptrTo base 8 (M * perm[v]!))) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide)]; exact hpgp
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr Block.nextelement Ptrofs.zero) (targs := [tptr tulong, tint, tint])
      (tres := tint) (cc := Common.AST.cc_default) _ (Nextelement.nextSpec bg (ptrTo base 8 (M * v)) M p ws)
      (Nextelement.nextelement_satisfies _ _ _ _ _) rfl
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
        show PTree.get Source.dense.id.nextelement (empty_env : env) = none from rfl,
        find_nextelement, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
      (by simp only [Exec.evalExprlist, Exec.evalExpr, hpg', hf.hm, hposp, typeof, cop])
      (by simp [Common.Globalenvs.Genv.find_funct, funct_nextelement]) type_nextelement
      ⟨rfl, by omega, hp2, hM1, hM64, hwords, hf.lb⟩ ?_
    rintro t r m2 ⟨rfl, rfl, r, rfl, hspec⟩
    dsimp only [set_opttemp]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    apply wp_if_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss, typeof, cop]
    rcases hspec with ⟨rfl, hnone⟩ | ⟨w, rfl, hpw, hin, hmin⟩
    · rw [ir_lt (a := -1) (b := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
      try simp only [cop]
      rw [ite_eq_right (by decide)]
      apply wp_break
      refine hQn ?_ _ ?_
      · intro q hq hvq
        apply hchk q (by omega) ?_ hq
        apply Classical.byContradiction
        intro hgt
        exact hnone q (by omega) ((inSet_iff hrep).2 hq)
      · intro x h1 h2 h3 h4
        rw [temps_gso _ _ h1, temps_gso _ _ h4, temps_gso _ _ h3, ho x h1 h2 h3 h4]
    · have hwm : rows[v]!.mem w = true := (inSet_iff hrep).1 hin
      have hwn := VSet.mem_lt hwm
      rw [ir_lt (a := (w : Int)) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
      try simp only [cop]
      rw [ite_eq_left (by simp)]
      apply wp_skip
      let le2 := PTree.set id.pos (.Vint (ir (w : Int))) (PTree.set id.t3 (.Vint (ir (w : Int)))
        (PTree.set id.t2 (.Vint (ir (w : Int))) le'))
      have ho2 : ∀ x, x ≠ id.pos → x ≠ id.t3 → x ≠ id.t2 → PTree.get x le2 = PTree.get x le' :=
        fun x h1 h2 h3 => by simp only [le2]; rw [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3]
      have hpermw := eval_at (ge := ge) (e := empty_env) (le := le2) h.parr (by omega) id.perm
        (by rw [ho2 _ (by decide) (by decide) (by decide)]; exact hf.hperm) (tv id.pos) w hwn
        (by simp only [Exec.evalExpr, le2]; rw [temps_gss]) rfl
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [hpermw]
      simp only [ints]
      have hpw := h.psmall w hwn
      let le3 := PTree.set id.posp (.Vint (ir (perm[w]! : Int))) le2
      have hmemp : SetwordsMem (fun x => bv64 (wsp x)) perm[w]! = rows[perm[v]!]!.mem perm[w]! :=
        hrepp.2 _ (by omega)
      have hel := Set.eval_isElement (e := empty_env) (le := le3) (s := id.pgp) (bitId := id.bit)
        (a := tv id.posp) hrowp (by omega)
        (by simp only [le3]; rw [temps_gso _ _ (by decide), ho2 _ (by decide) (by decide) (by decide)]
            exact hpgp')
        (by simp only [Exec.evalExpr, le3]; rw [temps_gss]) rfl (by omega) (by omega) hf.bit rfl
        find_naugraphBit
      rw [hmemp] at hel
      wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hel]
      by_cases hok : rows[perm[v]!]!.mem perm[w]! = true
      · rw [hok]
        simp only [Val.of_bool, ite_true, Vtrue, typeof, cop]
        simp (config := {decide := true}) only [ite_false, Vfalse, cop]
        apply wp_skip
        refine ⟨(64 * M - (w : Int)).toNat, by omega, rfl, rfl, rfl, w, by omega, by omega, rfl,
          by rw [temps_gso _ _ (by decide), temps_gss], ?_, ?_⟩
        · intro q h1 h2 hq
          rcases Int.lt_or_le p q with h3 | h3
          · rcases Nat.lt_or_ge q w with h4 | h4
            · exact absurd ((inSet_iff hrep).2 hq) (hmin q h3 (by omega))
            · rw [show q = w by omega]; exact hok
          · exact hchk q h1 h3 hq
        · intro x h1 h2 h3 h4
          rw [temps_gso _ _ h2, temps_gso _ _ h1, temps_gso _ _ h4, temps_gso _ _ h3, ho x h1 h2 h3 h4]
      · have hf' : rows[perm[v]!]!.mem perm[w]! = false := by simpa using hok
        rw [hf']
        simp (config := {decide := true}) only [Val.of_bool, ite_false, Vfalse,
          typeof, cop, ite_true]
        wp_step; wp_step
        apply wp_return_some_eval
        simp only [Exec.evalExpr, typeof, cop, Source.dense.fn.isautom.fn_return_eq,
          Nextelement.free_empty]
        exact hQr fun hrow => hok (hrow w hwm (by omega))
  · rintro k t e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Isautom

import NautyVerified.Proofs.Refine1.Syntax
import NautyVerified.Proofs.Refine.Pop
import NautyVerified.Proofs.Graph.Rows

/-!
# `refine1`'s neighbour count

`refine1` keeps the splitter set in the one-word temporary `workset0` and
counts a member's neighbours in it with
`if ((x = workset0 & g[lab[i]]) != 0) cnt = POPCOUNT(x); else cnt = 0;`.
`wp_cnt1`: that sets `cnt` to HexGraphIso's `VSet.cardInter`, as `refine`'s
word loop does.
-/

namespace NautyVerified.Proofs.Refine1

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs
open NautyVerified.Proofs.Set (sk pv longs)
open NautyVerified.Proofs.Refine (tv ix popcount)
open NautyVerified.Proofs.Init (BytecountTable)
open NautyVerified.Proofs.Graph (GraphAt)
open Hex.GraphIso.Nauty (VSet popCount)

variable {xi : ExternalCalls}

/-- `if ((x = workset0 & g[lab[i]]) != 0) cnt = POPCOUNT(x); else cnt = 0;`, with
SimplExpr's temporary `t`. -/
abbrev cnt1 (t : Common.AST.ident) : statement :=
  .Ssequence
    (.Ssequence
      (sk (.Sset t (.Ecast (.Ebinop .Oand (.Etempvar dense.id.workset0 tulong)
        (.Ederef (.Ebinop .Oadd (pv dense.id.g) (ix dense.id.lab (tv dense.id.i)) (tptr tulong))
          tulong) tulong) tulong)))
      (.Sset dense.id.x (.Etempvar t tulong)))
    (.Sifthenelse (.Ebinop .One (.Etempvar t tulong) (ci 0 tint) tint)
      (sk (.Sset dense.id.cnt popcount)) (sk (.Sset dense.id.cnt (ci 0 tint))))

theorem wp_cnt1 {f : function} {Q : Post} {le : temp_env} {m : mem} {n : Nat} {t : Common.AST.ident}
    (htx : t ≠ dense.id.x) {w : Lib.Integers.int64} {ws : VSet n}
    (hw : PTree.get dense.id.workset0 le = some (.Vlong w))
    (hrep : SetRep (fun _ => bv64 w) 1 ws)
    {bg : block} {gofs : ptrofs} {gw : Nat → Lib.Integers.int64} {rows : Array (VSet n)}
    (hg : GraphAt m bg gofs gw rows 1) (hgp : PTree.get dense.id.g le = some (.Vptr bg gofs))
    {bl : block} {lofs : ptrofs} {lab : Array Nat}
    (hlab : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n)
    (hlp : PTree.get dense.id.lab le = some (.Vptr bl lofs)) {k : Nat} (hk : k < n)
    (hlk : lab[k]! < n) (hi : PTree.get dense.id.i le = some (.Vint (ir k)))
    (hn : n < 2147483648) (hbt : BytecountTable m)
    (hQ : ∀ le', PTree.get dense.id.cnt le' = some (.Vint (ir (ws.cardInter rows[lab[k]!]! : Nat))) →
      (∀ y, y ≠ t → y ≠ dense.id.x → y ≠ dense.id.cnt → PTree.get y le' = PTree.get y le) →
      Q.normal E0 empty_env le' m) :
    Wp xi ge f (cnt1 t) Q empty_env le m := by
  have hrow := hg.arr
  rw [Nat.one_mul] at hrow
  have hlk' := eval_at (ge := ge) (e := empty_env) hlab hn dense.id.lab hlp (tv dense.id.i) k hk hi rfl
  have hgw := Set.eval_word (e := empty_env) (le := le) (m := m) hrow hn dense.id.g hgp
    (ix dense.id.lab (tv dense.id.i)) lab[k]! hlk hlk' rfl
  -- the count is `cardInter`
  have hcard : popCount (bv64 (Int64.and w (gw lab[k]!))).toNat = ws.cardInter rows[lab[k]!]! := by
    have := Refine.cardInter_words (M := 1) (a := fun _ => w) (b := fun j => gw (1 * lab[k]! + j))
      hrep (hg.rep _ hlk)
    simpa using this
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, Exec.evalExpr, show Exec.evalExpr ge empty_env le m (.Etempvar dense.id.workset0 tulong) = _ from hw, hgw]
  simp only [typeof, cop]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss]
  apply wp_if_eval
  simp only [Exec.evalExpr]
  rw [temps_gso _ _ htx, temps_gss]
  simp only [typeof, cop]
  let le2 := PTree.set dense.id.x (.Vlong (Int64.and w (gw lab[k]!)))
    (PTree.set t (.Vlong (Int64.and w (gw lab[k]!))) le)
  have ho2 : ∀ y, y ≠ t → y ≠ dense.id.x → PTree.get y le2 = PTree.get y le := fun y h1 h2 => by
    simp only [le2]; rw [temps_gso _ _ h2, temps_gso _ _ h1]
  by_cases hz : Int64.eq (Int64.and w (gw lab[k]!)) (Cfrontend.Cop.cast_int_long .Signed (ir 0)) = true
  · rw [hz]
    simp only [Bool.not_true, cop, Bool.false_eq_true, ite_false]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, cop]
    refine hQ _ ?_ fun y h1 h2 h3 => by rw [temps_gso _ _ h3, ho2 y h1 h2]
    rw [temps_gss, ← hcard]
    have h0 : Int64.and w (gw lab[k]!) = lr 0 := by
      have := (bv64_eq _ _).symm.trans hz
      simp only [decide_eq_true_eq] at this
      exact bv64_inj.1 (this.trans (by rfl))
    rw [h0, show bv64 (lr 0) = 0 by simp [intOfZ_zOfInt]]
    rfl
  · rw [show Int64.eq (Int64.and w (gw lab[k]!)) (Cfrontend.Cop.cast_int_long .Signed (ir 0)) = false by
      simpa using hz]
    simp only [Bool.not_false, cop, ite_true]
    wp_step; wp_step
    apply wp_set_eval
    rw [Refine.eval_popcount (e := empty_env) (le := le2) (m := m) _ (by simp only [le2]; rw [temps_gss])
      hbt rfl]
    refine hQ _ ?_ fun y h1 h2 h3 => by rw [temps_gso _ _ h3, ho2 y h1 h2]
    rw [temps_gss, hcard]

/-! ## The splitter set -/

/-- `workset0 = 0; for (i = split1; i <= split2; ++i) workset0 |= bit[lab[i]]; rest` -/
abbrev fill1 (rest : statement) : statement :=
  .Ssequence (sk (.Sset dense.id.workset0 (.Ecast (ci 0 tint) tulong)))
    (.Ssequence (.Ssequence (sk (.Sset dense.id.i (tv dense.id.split1)))
      (.Sloop
        (.Ssequence
          (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.i) (tv dense.id.split2) tint) .Sskip .Sbreak))
          (sk (.Sset dense.id.workset0 (.Ebinop .Oor (.Etempvar dense.id.workset0 tulong)
            (Set.bit1 dense.id.«naugraph:bit» (ix dense.id.lab (tv dense.id.i))) tulong))))
        (sk (.Sset dense.id.i (.Ebinop .Oadd (tv dense.id.i) (ci 1 tint) tint))))) rest)

theorem worksetOf_succ {n : Nat} (lab : Array Nat) (lo k : Nat) :
    (List.range (k + 1)).foldl (fun w o => w.insert lab[lo + o]!) (VSet.empty : VSet n) =
      ((List.range k).foldl (fun w o => w.insert lab[lo + o]!) (VSet.empty : VSet n)).insert
        lab[lo + k]! := by
  rw [List.range_succ, List.foldl_append]; rfl

/-- One word `w` with bit `c` added, as nauty's `bit[c]` adds it. -/
theorem setRep_or1 {n c : Nat} {w : Lib.Integers.int64} {s : VSet n}
    (h : SetRep (fun _ => bv64 w) 1 s) (hc : c < n) :
    SetRep (fun _ => bv64 (Int64.or w (lr ((2 ^ (63 - c) : Nat) : Int)))) 1 (s.insert c) := by
  have hc64 : c < 64 := by have := h.1; omega
  have := Set.setRep_add (ws := fun _ => w) h hc
  refine Graph.setRep_congr this fun i hi => ?_
  have hi0 : i = 0 := by omega
  subst hi0
  simp [Set.addW, upd, show c / 64 = 0 by omega, show c % 64 = c by omega]

theorem wp_fill1 {f : function} {Q : Post} {le : temp_env} {m : mem} {n : Nat} {rest : statement}
    {bl : block} {lofs : ptrofs} {lab : Array Nat}
    (hlab : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n)
    (hlp : PTree.get dense.id.lab le = some (.Vptr bl lofs)) (hls : ∀ j < n, lab[j]! < n)
    (hn64 : n ≤ 64) {s1 s2 : Nat} (h12 : s1 ≤ s2) (h2n : s2 < n)
    (hs1 : PTree.get dense.id.split1 le = some (.Vint (ir s1)))
    (hs2 : PTree.get dense.id.split2 le = some (.Vint (ir s2)))
    (hbit : Set.BitTable m Block.naugraphBit)
    (hQ : ∀ le' (w : Lib.Integers.int64), PTree.get dense.id.workset0 le' = some (.Vlong w) →
      SetRep (fun _ => bv64 w) 1 (Hex.GraphIso.Nauty.worksetOf n lab s1 s2) →
      (∀ y, y ≠ dense.id.workset0 → y ≠ dense.id.i → PTree.get y le' = PTree.get y le) →
      Wp xi ge f rest Q empty_env le' m) :
    Wp xi ge f (fill1 rest) Q empty_env le m := by
  have hn : n < 2147483648 := by omega
  let W := fun k => (List.range k).foldl (fun w o => w.insert lab[s1 + o]!) (VSet.empty : VSet n)
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ j w, s1 ≤ j ∧ j ≤ s2 + 1 ∧ v = s2 + 1 - j ∧
      PTree.get dense.id.i le' = some (.Vint (ir j)) ∧
      PTree.get dense.id.workset0 le' = some (.Vlong w) ∧ SetRep (fun _ => bv64 w) 1 (W (j - s1)) ∧
      ∀ y, y ≠ dense.id.workset0 → y ≠ dense.id.i → PTree.get y le' = PTree.get y le
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop]
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gso _ _ (show dense.id.split1 ≠ dense.id.workset0 by decide), hs1]
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ j w, s1 ≤ j ∧ j ≤ s2 ∧ v = s2 + 1 - j ∧
      PTree.get dense.id.i le' = some (.Vint (ir j)) ∧
      PTree.get dense.id.workset0 le' = some (.Vlong w) ∧ SetRep (fun _ => bv64 w) 1 (W (j + 1 - s1)) ∧
      ∀ y, y ≠ dense.id.workset0 → y ≠ dense.id.i → PTree.get y le' = PTree.get y le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := s2 + 1 - s1)
    ⟨rfl, rfl, rfl, s1, lr 0, Nat.le_refl _, by omega, rfl, temps_gss _ _ _,
      by rw [temps_gso _ _ (by decide), temps_gss]; rfl,
      by simpa [W] using Set.setRep_zero (n := n) (M := 1) (by omega),
      fun y h1 h2 => by rw [temps_gso _ _ h2, temps_gso _ _ h1]⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, w, hj1, hj2, rfl, hij, hwj, hrep, ho⟩
    have hs2' : PTree.get dense.id.split2 le' = some (.Vint (ir s2)) := by
      rw [ho _ (by decide) (by decide)]; exact hs2
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hij, hs2', typeof, cop]
    rw [ir_lt (a := (s2 : Int)) (b := (j : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hjs : j ≤ s2
    · rw [show (!decide ((s2 : Int) < j)) = true by simp; omega]
      apply wp_skip
      have hjn : j < n := by omega
      have hlj := hls j hjn
      have hle := eval_at (ge := ge) (e := empty_env) hlab hn dense.id.lab
        (by rw [ho _ (by decide) (by decide)]; exact hlp) (tv dense.id.i) j hjn hij rfl
      wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' (.Etempvar dense.id.workset0 tulong) = _
        from hwj, Set.eval_bit1 (c := lab[j]!) hle rfl (by omega) hbit rfl find_naugraphBit]
      simp only [typeof, cop]
      refine ⟨by simp, rfl, rfl, j, _, hj1, hjs, rfl, ?_, temps_gss _ _ _, ?_, fun y h1 h2 => ?_⟩
      · rw [temps_gso _ _ (by decide)]; exact hij
      · have e1 : W (j + 1 - s1) = (W (j - s1)).insert lab[s1 + (j - s1)]! := by
          rw [show j + 1 - s1 = (j - s1) + 1 by omega]; exact worksetOf_succ lab s1 (j - s1)
        rw [e1, show s1 + (j - s1) = j by omega]
        exact setRep_or1 hrep hlj
      · rw [temps_gso _ _ h1, ho y h1 h2]
    · rw [show (!decide ((s2 : Int) < j)) = false by simp; omega]
      apply wp_break
      have hj : j = s2 + 1 := by omega
      subst hj
      simp only [E0_append]
      refine hQ le' w hwj ?_ ho
      simpa [W, Hex.GraphIso.Nauty.worksetOf, show s2 + 1 - s1 = s2 + 1 - s1 from rfl] using hrep
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, w, hj1, hj2, rfl, hij, hwj, hrep, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hij, typeof, cop, ir_add]
    refine ⟨s2 + 1 - (j + 1), by omega, by simp, rfl, rfl, j + 1, w, by omega, by omega, rfl, ?_, ?_,
      by simpa [show j + 1 - s1 = j + 1 - s1 from rfl] using hrep, fun y h1 h2 => ?_⟩
    · rw [temps_gss]; push_cast; rfl
    · rw [temps_gso _ _ (by decide)]; exact hwj
    · rw [temps_gso _ _ h2, ho y h1 h2]

theorem nontrivial_fill : Refine1.nontrivial = fill1
    (.Ssequence (sk (Refine.mash (.Ebinop .Oadd (.Ebinop .Osub (tv dense.id.split2) (tv dense.id.split1)
      tint) (ci 1 tint) tint))) (.Ssequence (sk (.Sset dense.id.cell1 (ci 0 tint))) Refine1.cellLoopN)) :=
  rfl

end NautyVerified.Proofs.Refine1

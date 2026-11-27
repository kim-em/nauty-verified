import NautyVerified.Proofs.Breakout.Syntax
import NautyVerified.Proofs.Set.Add
import NautyVerified.Logic.Ints
import HexGraphIso.Nauty.Search.Refine

/-!
# The rotation loop of `breakout`

`wp_rotate`: `do { next = lab[i]; lab[i++] = prev; prev = next; } while (prev != tv);`,
started at `i = tc`, `prev = tv`, with `tv` at some position `J ≥ tc` of `lab`,
leaves `lab` holding HexGraphIso's `breakout.go tv (n + 1) lab tc tv`.
-/

namespace NautyVerified.Proofs.Breakout

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word

variable {xi : ExternalCalls}

/-- The state of the rotation loop when `i` holds `i`, `prev` holds `p`, `lab`
holds `o`, and `v` more iterations reach position `J` (which holds `tv`).
`R` is the final array HexGraphIso computes. -/
structure RotInv (m0 : mem) (le0 : temp_env) (bl : block) (lofs : ptrofs) (n x J : Nat)
    (R : Array Nat) (v : Nat) (o : Array Nat) (i p : Nat) (le : temp_env) (m : mem) : Prop where
  size : o.size = n
  hJ : i + v = J
  Jlt : J < n
  atJ : o[J]! = x
  small : ∀ x < n, o[x]! < n
  plt : p < n
  go : ∃ F, v + 1 ≤ F ∧ Hex.GraphIso.Nauty.breakout.go x F o i p = R
  arr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints o) n
  unch : Unch m0 m (· = bl)
  hi : PTree.get id.i le = some (.Vint (ir i))
  hp : PTree.get id.prev le = some (.Vint (ir p))
  other : ∀ k, k ≠ id.i → k ≠ id.prev → k ≠ id.next → k ≠ id.t2 → PTree.get k le = PTree.get k le0

theorem wp_rotate {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bl : block}
    {lofs : ptrofs} {o : Array Nat} {n x tc jt : Nat}
    (harr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints o) n)
    (hn : n < 2147483648) (hsize : o.size = n)
    (hlab : PTree.get id.lab le = some (.Vptr bl lofs))
    (htv : PTree.get id.tv le = some (.Vint (ir x)))
    (hi : PTree.get id.i le = some (.Vint (ir tc)))
    (hp : PTree.get id.prev le = some (.Vint (ir x)))
    (htc : tc ≤ jt) (hjt : jt < n) (hat : o[jt]! = x) (hsmall : ∀ x < n, o[x]! < n)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bl (intOfZ (Ptrofs.unsigned lofs))
        (ints (Hex.GraphIso.Nauty.breakout.go x (n + 1) o tc x)) n →
      Unch m m' (· = bl) →
      (∀ k, k ≠ id.i → k ≠ id.prev → k ≠ id.next → k ≠ id.t2 → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m') :
    Wp xi ge f rotate Q e le m := by
  let R := Hex.GraphIso.Nauty.breakout.go x (n + 1) o tc x
  have htvn : x < n := hat ▸ hsmall jt hjt
  refine wp_loop
    (I := fun v t e' le' m' => t = E0 ∧ e = e' ∧
      ∃ o' i p, RotInv m le bl lofs n x jt R v o' i p le' m')
    (J := fun v t e' le' m' => t = E0 ∧ e = e' ∧ ∃ o' i p,
      (p = x ∧ o' = R ∧ ArrayAt m' .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints o') n ∧
        Unch m m' (· = bl) ∧ PTree.get id.prev le' = some (.Vint (ir p)) ∧
        ∀ k, k ≠ id.i → k ≠ id.prev → k ≠ id.next → k ≠ id.t2 → PTree.get k le' = PTree.get k le) ∨
      (p ≠ x ∧ 0 < v ∧ RotInv m le bl lofs n x jt R (v - 1) o' i p le' m'))
    ?_ ?_ (n := jt - tc)
    ⟨rfl, rfl, o, tc, x, ⟨hsize, by omega, hjt, hat, hsmall, htvn, ⟨n + 1, by omega, rfl⟩, harr,
      Unch.refl _ _, hi, hp, fun _ _ _ _ _ => rfl⟩⟩
  · rintro v t e' le' m' ⟨rfl, rfl, o', i, p, h⟩
    have hlab' : PTree.get id.lab le' = some (.Vptr bl lofs) := by
      rw [h.other _ (by decide) (by decide) (by decide) (by decide)]; exact hlab
    have hil : i < n := by have := h.hJ; have := h.Jlt; omega
    have hoi := eval_at (ge := ge) (e := e) h.arr hn id.lab hlab' (tv id.i) i hil h.hi rfl
    have hsi := h.small i hil
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [hoi]
    simp only [ints, E0_append]
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, h.hi]
    simp only [E0_append]
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]
    simp only [E0_append]
    have hil' : i < o'.size := by rw [h.size]; exact hil
    refine wp_store (ge := ge) h.arr hn id.lab (by simp (config := {decide := true}) only [temps_gso]; exact hlab')
      (tv id.t2) i hil (by simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss]) rfl
      (tv id.prev) p (by simp (config := {decide := true}) only [Exec.evalExpr, temps_gso]; exact h.hp) rfl ?_
    intro m'' harr' hu
    rw [← ints_set hil'] at harr'
    wp_step; wp_step
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss]
    have hother : ∀ k, k ≠ id.i → k ≠ id.prev → k ≠ id.next → k ≠ id.t2 →
        PTree.get k (PTree.set id.prev (.Vint (ir (o'[i]! : Int))) (PTree.set id.i (.Vint (ir ((i : Int) + 1)))
          (PTree.set id.t2 (.Vint (ir (i : Int))) (PTree.set id.next (.Vint (ir (o'[i]! : Int))) le')))) =
          PTree.get k le := by
      intro k h1 h2 h3 h4
      rw [temps_gso _ _ h2, temps_gso _ _ h1, temps_gso _ _ h4, temps_gso _ _ h3, h.other k h1 h2 h3 h4]
    obtain ⟨F, hF, hgo⟩ := h.go
    obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    refine ⟨trivial, trivial, o'.set! i p, i + 1, o'[i]!, ?_⟩
    by_cases hr : o'[i]! = x
    · refine .inl ⟨hr, ?_, harr', h.unch.trans hu, rfl, hother⟩
      rw [← hgo, Hex.GraphIso.Nauty.breakout.go]
      simp [hr]
    · have hne : i ≠ jt := fun h' => hr (h' ▸ h.atJ)
      have hv : 0 < v := by have := h.hJ; omega
      refine .inr ⟨hr, hv, ⟨by rw [Array.size_set!, h.size], by have := h.hJ; omega, h.Jlt,
        by rw [Array.getElem!_set!_ne _ _ _ _ hne, h.atJ], ?_, hsi, ⟨F, by omega, ?_⟩, harr',
        h.unch.trans hu, by rw [temps_gso _ _ (by decide), temps_gss]; congr, temps_gss _ _ _,
        hother⟩⟩
      · intro y hy
        by_cases hyi : y = i
        · subst hyi; rw [Array.getElem!_set!_self _ _ _ hil']; exact h.plt
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hyi)]; exact h.small y hy
      · rw [← hgo, Hex.GraphIso.Nauty.breakout.go]
        simp [hr]
  · rintro v t e' le' m' ⟨rfl, rfl, o', i, p, hcase⟩
    have key : ∀ le', (∀ k, k ≠ id.i → k ≠ id.prev → k ≠ id.next → k ≠ id.t2 →
        PTree.get k le' = PTree.get k le) → PTree.get id.prev le' = some (.Vint (ir p)) → p < n →
        Exec.evalExpr ge e le' m' (.Ebinop .One (tv id.prev) (tv id.tv) tint) =
          some (Val.of_bool (decide (p ≠ x))) := by
      intro le' ho hp' hpn
      have hx : PTree.get id.tv le' = some (.Vint (ir x)) := by
        rw [ho id.tv (by decide) (by decide) (by decide) (by decide)]; exact htv
      simp only [Exec.evalExpr, hp', hx,
        typeof, cop, ir_eq (a := p) (b := x) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hpx : p = x
      · simp [hpx]
      · have : ¬ (p : Int) = x := by omega
        simp [hpx, this]
    wp_step; wp_step
    apply wp_if_eval
    rcases hcase with ⟨rfl, rfl, harr', hu, hp', ho⟩ | ⟨hne, hv, h⟩
    · rw [key le' ho hp' htvn]
      simp only [ne_eq, not_true_eq_false, decide_false, cop]
      apply wp_break
      exact hQ le' m' harr' hu ho
    · rw [key le' h.other h.hp h.plt]
      simp only [ne_eq, hne, not_false_eq_true, decide_true, cop]
      apply wp_skip
      exact ⟨v - 1, by omega, by simp, rfl, o', i, p, h⟩

end NautyVerified.Proofs.Breakout

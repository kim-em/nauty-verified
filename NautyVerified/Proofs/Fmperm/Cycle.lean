import NautyVerified.Program.Env
import NautyVerified.Proofs.Fmperm.Clear
import NautyVerified.Proofs.Set.Add
import NautyVerified.Spec.Fmperm
import NautyVerified.Spec.Cycle

/-!
# The cycle walk of `fmperm`

`workperm` holds HexGraphIso's `seen` array as 0/1 (`seenVals`).
`wp_walk`: `do { k = l; l = perm[l]; workperm[k] = 1; } while (l != i);`
started at `l = i` marks the cycle of `i` exactly as HexGraphIso's `mark`.
-/

namespace NautyVerified.Proofs.Fmperm

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Spec
open NautyVerified.Proofs.Alloc (gat eval_gat wp_gstore)

variable {xi : ExternalCalls}

/-- `workperm` holding `seen` as 0/1. -/
def seenVals (seen : Array Bool) (k : Nat) : val := .Vint (ir (if seen[k]! then 1 else 0))

theorem seenVals_set {seen : Array Bool} {l : Nat} (hl : l < seen.size) :
    seenVals (seen.set! l true) = upd (seenVals seen) l (.Vint (ir 1)) := by
  funext k
  simp only [seenVals, upd]
  by_cases h : k = l
  · subst h; simp [hl]
  · rw [ite_eq_right h, Array.getElem!_set!_ne _ _ _ _ (Ne.symm h)]

theorem seenVals_replicate (n : Nat) : seenVals (Array.replicate n false) = fun _ => .Vint (ir 0) := by
  funext k
  simp only [seenVals]
  by_cases h : k < n <;> simp [h]

/-- What `fmperm` reads throughout. -/
structure Frame (m : mem) (le : temp_env) (bpm : block) (pofs : ptrofs) (b : block)
    (perm : Array Nat) (n : Nat) : Prop where
  hperm : PTree.get id.perm le = some (.Vptr bpm pofs)
  hn : PTree.get id.n le = some (.Vint (ir n))
  parr : ArrayAt m .Mint32 bpm (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n
  wpPtr : 0 < n → Mem.load .Mint64 m E.nautilWorkperm (zOfInt 0) = some (.Vptr b Ptrofs.zero)
  psize : perm.size = n
  psmall : ∀ x, x < n → perm[x]! < n
  pinj : ∀ x y, x < n → y < n → perm[x]! = perm[y]! → x = y
  nlt : n < 2147483648
  bpm_b : 0 < n → bpm ≠ b
  wp_b : 0 < n → E.nautilWorkperm ≠ b

/-- The `do … while` loop of the cycle walk. -/
abbrev walk : statement :=
  .Sloop
    (.Ssequence (Set.sk (.Sset id.k (tv id.l)))
      (.Ssequence (Set.sk (.Sset id.l (permAt (tv id.l))))
        (Set.sk (.Sassign (wpAt (tv id.k)) (ci 1 tint)))))
    (Set.sk (.Sifthenelse (.Ebinop .One (tv id.l) (tv id.i) tint) .Sskip .Sbreak))

theorem cycle_eq : cycle = .Ssequence (Set.sk (.Sset id.l (tv id.i)))
    (.Ssequence walk (Set.addElement id.mcr (tv id.i))) := rfl

theorem wp_walk {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bpm : block}
    {pofs : ptrofs} {b : block} {perm : Array Nat} {n i0 : Nat} {seen : Array Bool}
    (h : Frame m le bpm pofs b perm n) (hge : PTree.get id.wp e = none)
    (warr : ArrayAt m .Mint32 b 0 (seenVals seen) n) (hsz : seen.size = n)
    (hi : PTree.get id.i le = some (.Vint (ir i0))) (hl : PTree.get id.l le = some (.Vint (ir i0)))
    (hi0 : i0 < n)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 b 0 (seenVals (mark perm i0 (List.range n) seen i0)) n →
      Unch m m' (· = b) → Alloc.Keep m m' b →
      (∀ x, x ≠ id.k → x ≠ id.l → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f walk Q e le m := by
  let p : Nat → Nat := fun x => perm[x]!
  have hp : ∀ x, x < n → p x < n := h.psmall
  obtain ⟨r, hr1, hrn, hret⟩ := cycle_return hp h.pinj hi0
  let R := mark perm i0 (List.range n) seen i0
  have hnlt := h.nlt
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ j sj F, j < r ∧ v = r - j ∧ (∀ k, 1 ≤ k → k ≤ j → iter p k i0 ≠ i0) ∧
      PTree.get id.l le' = some (.Vint (ir (iter p j i0 : Nat))) ∧
      ArrayAt m' .Mint32 b 0 (seenVals sj) n ∧ sj.size = n ∧ r - j ≤ F.length ∧
      mark perm i0 F sj (iter p j i0) = R ∧ Unch m m' (· = b) ∧ Alloc.Keep m m' b ∧
      ∀ x, x ≠ id.k → x ≠ id.l → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ j sj F, j < r ∧ v = r - j ∧ (∀ k, 1 ≤ k → k ≤ j → iter p k i0 ≠ i0) ∧
      PTree.get id.l le' = some (.Vint (ir (iter p (j + 1) i0 : Nat))) ∧
      ArrayAt m' .Mint32 b 0 (seenVals (sj.set! (iter p j i0) true)) n ∧ sj.size = n ∧
      r - j ≤ F.length ∧ mark perm i0 F sj (iter p j i0) = R ∧ Unch m m' (· = b) ∧
      Alloc.Keep m m' b ∧ ∀ x, x ≠ id.k → x ≠ id.l → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := r - 0)
    ⟨rfl, rfl, 0, seen, List.range n, by omega, rfl, fun k h1 h2 => absurd h2 (by omega), hl,
      warr, hsz, by simp; omega, rfl, Unch.refl _ _, Alloc.Keep.refl _ _, fun _ _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, j, sj, F, hj, rfl, hfirst, hlj, harr, hsj, hF, hmark, hu, hk,
      ho⟩
    have hcur := iter_lt hp j i0 hi0
    have hf := h
    have hperm' : PTree.get id.perm le' = some (.Vptr bpm pofs) := by
      rw [ho _ (by decide) (by decide)]; exact h.hperm
    have hparr := h.parr.unch hu (h.bpm_b (by omega))
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [show Exec.evalExpr ge e le' m' (tv id.l) = _ from hlj]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    have hpl := eval_at (ge := ge) (e := e)
      (le := PTree.set id.k (.Vint (ir (iter p j i0 : Nat))) le') hparr h.nlt id.perm (by
        rw [temps_gso _ _ (by decide)]; exact hperm') (tv id.l) (iter p j i0) hcur
      (by simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide)]; exact hlj) rfl
    rw [hpl]
    simp only [ints, E0_append]
    wp_step; wp_step
    refine wp_gstore hge E.find_nautilWorkperm (by rw [hu.load _ _ _ (h.wp_b (by omega))]; exact h.wpPtr (by omega))
      harr h.nlt (tv id.k) (iter p j i0) hcur
      (by simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide), temps_gss]) rfl
      (ci 1 tint) 1 rfl rfl ?_
    intro m'' harr' hu' hk'
    rw [← seenVals_set (by rw [hsj]; exact hcur)] at harr'
    refine ⟨by simp, rfl, j, sj, F, hj, rfl, hfirst, ?_, harr', hsj, hF, hmark, hu.trans hu',
      hk.trans hk', ?_⟩
    · rw [temps_gss]; rfl
    · intro x h1 h2
      rw [temps_gso _ _ h2, temps_gso _ _ h1, ho x h1 h2]
  · rintro v t e' le' m' ⟨rfl, rfl, j, sj, F, hj, rfl, hfirst, hlj, harr, hsj, hF, hmark, hu, hk,
      ho⟩
    have hnext := iter_lt hp (j + 1) i0 hi0
    have hi' : PTree.get id.i le' = some (.Vint (ir i0)) := by
      rw [ho _ (by decide) (by decide)]; exact hi
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m' (tv id.l) = _ from hlj,
      show Exec.evalExpr ge e le' m' (tv id.i) = _ from hi']
    simp only [typeof, cop]
    rw [ir_eq (a := ((iter p (j + 1) i0 : Nat) : Int)) (b := (i0 : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    obtain ⟨f0, F', rfl⟩ : ∃ f0 F', F = f0 :: F' := by
      cases F with
      | nil => simp at hF; omega
      | cons f0 F' => exact ⟨f0, F', rfl⟩
    have hstep : iter p (j + 1) i0 = perm[iter p j i0]! := rfl
    by_cases hback : iter p (j + 1) i0 = i0
    · rw [ite_eq_right (by simp [hback])]
      apply wp_break
      have hb' : perm[iter p j i0]! = i0 := hstep ▸ hback
      rw [mark, hb', beq_self_eq_true, ite_eq_left rfl] at hmark
      rw [hmark] at harr
      simpa using hQ le' m' harr hu hk ho
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      have hj1 : j + 1 < r := by
        rcases Nat.lt_or_ge (j + 1) r with h1 | h1
        · exact h1
        · have : j + 1 = r := by omega
          exact absurd (this ▸ hret) hback
      rw [mark, ite_eq_right (by simpa [← hstep] using hback)] at hmark
      refine ⟨r - (j + 1), by omega, by simp, rfl, j + 1, sj.set! (iter p j i0) true, F', hj1, rfl,
        fun k h1 h2 => ?_, hlj, harr, by rw [Array.size_set!, hsj], by simp at hF; omega,
        by rw [hstep]; exact hmark, hu, hk, ho⟩
      rcases Nat.lt_or_ge k (j + 1) with h3 | h3
      · exact hfirst k h1 (by omega)
      · rw [show k = j + 1 by omega]; exact hback

end NautyVerified.Proofs.Fmperm

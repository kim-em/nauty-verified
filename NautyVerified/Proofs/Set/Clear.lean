import NautyVerified.Program.Env
import NautyVerified.Proofs.Set.Syntax
import NautyVerified.Logic.PtrArith
import NautyVerified.Logic.Wp
import NautyVerified.Logic.Simp
import NautyVerified.Program.Dense

/-!
# `EMPTYSET`

`wp_emptySet`: `EMPTYSET(s, m)` sets all `m` words of the set `s` to zero,
changing only its block and the temporaries `es` and `tmp`.
-/

namespace NautyVerified.Proofs.Set

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word

variable {xi : ExternalCalls}

/-- The values of an array of `long`s. -/
def longs (ws : Nat → Lib.Integers.int64) (i : Nat) : val := .Vlong (ws i)

/-- Words below `k` as in `ws`, the rest zero. -/
def clearedFrom (ws : Nat → Lib.Integers.int64) (k : Nat) (w : Nat) : Lib.Integers.int64 :=
  if w < k then ws w else lr 0

theorem sizeof_tulong : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong) = 8 := rfl

theorem cmplu_ptrTo {m : mem} {ba : block} {base : Int} {vals : Nat → val} {M : Nat}
    (harr : ArrayAt m .Mint64 ba base vals M) (hM : 0 < M) {k : Nat} (hk : k ≤ M)
    {ofs : ptrofs} (hofs : intOfZ (Ptrofs.unsigned ofs) = base) :
    Val.cmplu_bool (Mem.valid_pointer m) .Cgt (.Vptr ba (ptrTo base 8 k)) (.Vptr ba ofs) =
      some (decide (0 < k)) := by
  have hf := harr.fits
  have hb := harr.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  have hu : intOfZ (Ptrofs.unsigned (ptrTo base 8 k)) = base + 8 * k := by
    apply unsigned_ptrTo <;> omega
  have hz1 : Ptrofs.unsigned (ptrTo base 8 k) = zOfInt (base + 8 * k) := by
    rw [← hu, zOfInt_intOfZ]
  have hz2 : Ptrofs.unsigned ofs = zOfInt base := by rw [← hofs, zOfInt_intOfZ]
  rw [cmplu_same _ _ _ _ _ (by rw [hz1]; exact harr.weak_valid hM (by omega) (by rw [h8]; omega))
    (by rw [hz2]; exact harr.weak_valid hM (by omega) (by rw [h8]; omega)), cmpu_gt]
  congr 1
  rw [intOfZ_Ptrofs_unsigned] at hu hofs
  apply decide_eq_decide.2
  omega

/-- Values below `k` as in `vals`, the rest zero words. -/
def clearedFromV (vals : Nat → val) (k : Nat) (w : Nat) : val :=
  if w < k then vals w else .Vlong (lr 0)

theorem clearedFromV_succ (vals : Nat → val) (k : Nat) :
    upd (clearedFromV vals (k + 1)) k (.Vlong (lr 0)) = clearedFromV vals k := by
  funext w
  simp only [upd, clearedFromV]
  by_cases h : w = k
  · subst h; simp
  · rw [ite_eq_right h]
    by_cases hw : w < k
    · rw [ite_eq_left hw, ite_eq_left (by omega)]
    · rw [ite_eq_right hw, ite_eq_right (by omega)]

theorem clearedFrom_succ (ws : Nat → Lib.Integers.int64) (k : Nat) :
    upd (longs (clearedFrom ws (k + 1))) k (.Vlong (lr 0)) = longs (clearedFrom ws k) := by
  funext w
  simp only [upd, longs, clearedFrom]
  by_cases h : w = k
  · subst h; simp
  · rw [ite_eq_right h]
    by_cases hw : w < k
    · rw [ite_eq_left hw, ite_eq_left (by omega)]
    · rw [ite_eq_right hw, ite_eq_right (by omega)]

theorem sub_ptrTo8 (ce : Cfrontend.Ctypes.composite_env) (base : Int) (k : Nat) :
    Ptrofs.sub (ptrTo base 8 (k + 1)) (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ce tulong)) (Ptrofs.of_ints (ir 1))) = ptrTo base 8 k := by
  have h : intOfZ (Cfrontend.Ctypes.sizeof ce tulong) = 8 := rfl
  have := sub_ptrTo base (Cfrontend.Ctypes.sizeof ce tulong) k
  rw [h] at this
  exact this

theorem wp_emptySet' {s mv es tmp : Common.AST.ident} (hs1 : s ≠ es) (hs2 : s ≠ tmp)
    (het : es ≠ tmp) {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {ba : block}
    {ofs : ptrofs} {vals : Nat → val} {M : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) vals M) (hM : 0 < M)
    (hM2 : M < 2147483648) (hact : PTree.get s le = some (.Vptr ba ofs))
    (hm : PTree.get mv le = some (.Vint (ir M)))
    (hQ : ∀ le' m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs fun _ => lr 0) M →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * M) →
      (∀ k, k ≠ es → k ≠ tmp → PTree.get k le' = PTree.get k le) → Q.normal E0 e le' m') :
    Wp xi ge f (emptySet s mv es tmp) Q e le m := by
  have hf := harr.fits
  have hb := harr.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  simp only [emptySet, sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hact, hm, typeof, cop]
  rw [add_ptrTo ofs _ M (by omega), sizeof_tulong]
  simp only [E0_append]
  let base := intOfZ (Ptrofs.unsigned ofs)
  refine wp_loop (I := fun k t e' le' m' => t = E0 ∧ e = e' ∧ k ≤ M ∧
      PTree.get es le' = some (.Vptr ba (ptrTo base 8 k)) ∧
      ArrayAt m' .Mint64 ba base (clearedFromV vals k) M ∧ Unch m m' (· = ba) ∧
      Outside m m' ba base (base + 8 * M) ∧
      ∀ k', k' ≠ es → k' ≠ tmp → PTree.get k' le' = PTree.get k' le)
    (J := fun k t e' le' m' => ∃ k' < k, t = E0 ∧ e = e' ∧ k' ≤ M ∧
      PTree.get es le' = some (.Vptr ba (ptrTo base 8 k')) ∧
      ArrayAt m' .Mint64 ba base (clearedFromV vals k') M ∧ Unch m m' (· = ba) ∧
      Outside m m' ba base (base + 8 * M) ∧
      ∀ k'', k'' ≠ es → k'' ≠ tmp → PTree.get k'' le' = PTree.get k'' le) ?_ ?_ (n := M)
    ⟨rfl, rfl, Nat.le_refl _, temps_gss _ _ _, by
      refine ⟨hb, by rw [h8]; omega, fun i hi => ?_, fun i hi => harr.writable i hi⟩
      simp only [clearedFromV, ite_eq_left hi]; exact harr.load i hi,
      Unch.refl _ _, Outside.refl _ _ _ _, fun k' hk _ => temps_gso _ _ hk⟩
  · rintro k t e' le' m' ⟨rfl, rfl, hk, hes, harr', hu, hout, hother⟩
    have hact' : PTree.get s le' = some (.Vptr ba ofs) := by
      rw [hother _ hs1 hs2]; exact hact
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hes, hact', typeof, cop]
    rw [cmplu_ptrTo harr' hM hk rfl]
    simp only [Option.map, cop]
    rcases k with _ | j
    · rw [ite_eq_right (by decide)]
      apply wp_break
      have h0 : clearedFromV vals 0 = longs fun _ => lr 0 := by funext w; simp [clearedFromV, longs]
      rw [h0] at harr'
      exact hQ le' m' harr' hu hout hother
    · rw [ite_eq_left (by simp)]
      apply wp_skip
      simp only [E0_append]
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hes, typeof, cop, sub_ptrTo8]
      simp only [E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss, E0_append]
      have hj : j < M := by omega
      have hu8 : intOfZ (Ptrofs.unsigned (ptrTo base 8 j)) = base + 8 * j := by
        apply unsigned_ptrTo <;> omega
      obtain ⟨m'', hst, harr'', -⟩ := store_array harr' hj (.Vlong (lr 0)) rfl
      apply wp_assign_eval
      simp only [Exec.evalLvalue, Exec.evalExpr, temps_gss, temps_gso _ _ het.symm, typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode,
        cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
      show match Mem.store .Mint64 m' ba (Ptrofs.unsigned _) _ with
        | some m' => _ | none => False
      rw [show Ptrofs.unsigned (ptrTo base 8 j) = elemOfs .Mint64 base j by
        rw [← zOfInt_intOfZ (Ptrofs.unsigned _), hu8]; rfl, hst]
      refine ⟨j, by omega, trivial, trivial, by omega, ?_, ?_, hu.trans (Unch.store hst rfl),
        hout.trans (Outside.store harr' hj hst (Int.le_refl _) (by rw [h8]; exact Int.le_refl _)), ?_⟩
      · rfl
      · rw [← clearedFromV_succ]; exact harr''
      · intro k'' h1 h2
        rw [temps_gso _ _ h1, temps_gso _ _ h2, hother _ h1 h2]
  · rintro k t e' le' m' ⟨k', hk', h⟩
    apply wp_skip
    exact ⟨k', hk', by simpa using h⟩


theorem wp_emptySet {s mv es tmp : Common.AST.ident} (hs1 : s ≠ es) (hs2 : s ≠ tmp)
    (het : es ≠ tmp) {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {ba : block}
    {ofs : ptrofs} {ws : Nat → Lib.Integers.int64} {M : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M) (hM : 0 < M)
    (hM2 : M < 2147483648) (hact : PTree.get s le = some (.Vptr ba ofs))
    (hm : PTree.get mv le = some (.Vint (ir M)))
    (hQ : ∀ le' m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs fun _ => lr 0) M →
      Unch m m' (· = ba) → (∀ k, k ≠ es → k ≠ tmp → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m') :
    Wp xi ge f (emptySet s mv es tmp) Q e le m :=
  wp_emptySet' (vals := longs ws) hs1 hs2 het harr hM hM2 hact hm fun le' m' ha hu _ ho => hQ le' m' ha hu ho

end NautyVerified.Proofs.Set

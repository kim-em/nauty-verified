import NautyVerified.Proofs.Top.NautyInit

/-!
# `nauty()`'s initial orbits (`tOrbits`)

`for (i = 0; i < n; ++i) orbits[i] = i;` through the static `orbits` pointer.
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (FieldAt IntAt PtrAt)

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- `*(pe + a) = rhs` for an `int *` expression `pe`. -/
theorem wp_storeE {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bo : block}
    {ofs : ptrofs} {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) vals n)
    (hn : n < 2147483648) (pe : expr) (hp : Exec.evalExpr ge e le m pe = some (.Vptr bo ofs))
    (hpt : typeof pe = tptr tint)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (x : Int) (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (upd vals c (.Vint (ir x))) n →
      Unch m m' (· = bo) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (.Ebinop .Oadd pe a (tptr tint)) tint) rhs) Q e le m := by
  have haddr : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tint)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint32 (intOfZ (Ptrofs.unsigned ofs)) c := by
    apply addr_elem ofs _ .Mint32 rfl rfl (by omega)
    have hf := harr.fits
    have h4 : csize .Mint32 = 4 := rfl
    rw [h4] at hf ⊢
    omega
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hrhs, hrty, hpt]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint32 m bo (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [haddr, hst]
  exact hQ m' harr' (Unch.store hst rfl) (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

/-- The first `k` entries set to their index. -/
def idFrom (v : Nat → val) (k : Nat) : Nat → val := fun j => if j < k then .Vint (ir j) else v j

theorem idFrom_succ (v : Nat → val) (k : Nat) :
    upd (idFrom v k) k (.Vint (ir k)) = idFrom v (k + 1) := by
  funext j
  simp only [upd, idFrom]
  by_cases h : j = k
  · subst h; simp
  · by_cases h2 : j < k
    · simp [h, h2, show j < k + 1 by omega]
    · simp [h, h2, show ¬ j < k + 1 by omega]

theorem idFrom_all (v : Nat → val) (n : Nat) :
    ∀ j < n, idFrom v n j = ints (Array.ofFn (n := n) fun i => i.val) j := by
  intro j hj
  simp [idFrom, ints, hj]

/-- `orbits[i] = i` for `i < n` (`tOrbits`). -/
theorem wp_tOrbits {Q : Post} {le : temp_env} {m : mem} {bo : block} {n : Nat} {v : Nat → val}
    (hn : n < 1073741824)
    (hO : FieldAt m .Mint64 Search.Block.orbits 0 (.Vptr bo Ptrofs.zero))
    (hN : IntAt m Search.Block.n n)
    (harr : ArrayAt m .Mint32 bo 0 v n)
    (hsep : bo ≠ Search.Block.orbits ∧ bo ≠ Search.Block.n)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bo 0 (ints (Array.ofFn (n := n) fun i => i.val)) n →
      Unch m m' (· = bo) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.«i» → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tStats Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.tOrbits Q (nEnv bI) le m := by
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k ≤ n ∧ PTree.get dense.id.«i» le' = some (.Vint (ir k)) ∧
    ArrayAt m' .Mint32 bo 0 (idFrom v k) n ∧ Unch m m' (· = bo) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    (∀ x, x ≠ dense.id.«i» → PTree.get x le' = PTree.get x le)
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) => k < n ∧
    PTree.get dense.id.«i» le' = some (.Vint (ir k)) ∧
    ArrayAt m' .Mint32 bo 0 (idFrom v (k + 1)) n ∧ Unch m m' (· = bo) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    (∀ x, x ≠ dense.id.«i» → PTree.get x le' = PTree.get x le)
  simp only [Nauty.tOrbits]
  wp_step
  refine wp_forLoopC (Inv := Inv) (Mid := Mid) dense.id.«i» _ rfl _ n (by omega) ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, -, hu, -, -⟩
    refine ⟨hk, hi, ?_⟩
    rw [Exec.evalExpr, show Exec.evalExpr ge (nEnv bI) le' m' (Refine.tv dense.id.«i») = _ from hi,
      Search.eval_gint (e := nEnv bI) rfl Search.find_n (hN.unch hu (Ne.symm hsep.2))]
    simp only [typeof, cop]
    rw [ir_lt (a := k) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, ?_, Unch.refl _ _, fun _ h => h,
      fun x hx => temps_gso _ _ hx⟩
    have : idFrom v 0 = v := funext fun j => by simp [idFrom]
    rw [this]; exact harr
  · rintro k le' m' hk ⟨-, hi, harr', hu, hg, ho⟩
    have hO' := hO.unch hu (Ne.symm hsep.1)
    simp only [Set.sk]
    wp_step; wp_step
    refine wp_storeE (ofs := Ptrofs.zero) harr' (by omega) _ ?_ rfl (Refine.tv dense.id.«i») k hk hi rfl
      (Refine.tv dense.id.«i») k hi rfl ?_
    · simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get dense.id.«nauty:orbits» (nEnv bI) = none
        from rfl, Search.find_orbits, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
        Alloc.Mptr_eq, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hO'.load]
    intro m'' harr'' hu'' hg''
    rw [idFrom_succ] at harr''
    exact ⟨rfl, hk, hi, harr'', hu.trans hu'', fun z hz => hg'' _ (hg z hz), ho⟩
  · rintro k le' m' ⟨hk, hi, harr', hu, hg, ho⟩
    refine ⟨hi, by omega, temps_gss _ _ _, harr', hu, hg, fun x hx => ?_⟩
    rw [temps_gso _ _ hx, ho x hx]
  · rintro le' m' ⟨-, -, harr', hu, hg, ho⟩
    simp only [seqPost, Post.after, E0_append]
    refine hQ le' m' ⟨harr'.base_nonneg, harr'.fits, fun j hj => ?_, harr'.writable⟩ hu hg ho
    rw [← idFrom_all v n j hj]; exact harr'.load j hj

end NautyVerified.Proofs.Top

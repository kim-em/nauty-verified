import NautyVerified.Proofs.Sparse.Testcanlab.Loops

/-!
# Pieces of `testcanlab_sg` outside the rows

`wp_scatter`: `for (i = 0; i < n; ++i) INVLAB[lab[i]] = i;` leaves `work1`
holding HexGraphIso's `inverse n lab` when `lab` is a permutation.
`wp_setSame`: `*samerows = x;`. `scan_eq`, `scan_end`: the first row with
an outcome determines `Scan`'s result.
-/

namespace NautyVerified.Proofs.Sparse.Testcanlab

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat mat)
open Hex.GraphIso.Nauty.Sparse (Graph Rows inverse inverse_get)

variable {xi : ExternalCalls}

theorem scan_eq {n : Nat} {f : Nat → Option Int} {r : Int × Nat} (h : Scan n f r) {i : Nat} {c : Int}
    (hi : i < n) (hpre : ∀ i' < i, f i' = none) (hc : f i = some c) : r = (c, i) := by
  rcases h with ⟨-, hall⟩ | ⟨hr, hpr, hfr⟩
  · rw [hall i hi] at hc; cases hc
  · rcases Nat.lt_trichotomy r.2 i with h | h | h
    · rw [hpre _ h] at hfr; cases hfr
    · rw [h, hc] at hfr; cases hfr
      exact Prod.ext rfl h
    · rw [hpr _ h] at hc; cases hc

theorem scan_end {n : Nat} {f : Nat → Option Int} {r : Int × Nat} (h : Scan n f r)
    (hall : ∀ i < n, f i = none) : r = (0, n) := by
  rcases h with ⟨h, -⟩ | ⟨hr, -, hfr⟩
  · exact h
  · rw [hall _ hr] at hfr; cases hfr

/-- `work1` after writing `lab[0 .. k-1]`. -/
def written (lab : Array Nat) (n : Nat) (vals : Nat → val) (k p : Nat) : val :=
  if ∃ j < k, lab[j]! = p then .Vint (ir (((inverse n lab)[p]! : Nat) : Int)) else vals p

theorem written_succ (lab : Array Nat) (n : Nat) (vals : Nat → val) (k : Nat) (hk : k < n)
    (hsz : lab.size = n) (hls : ∀ j < n, lab[j]! < n)
    (hinj : ∀ a b, a < n → b < n → lab[a]! = lab[b]! → a = b) :
    upd (written lab n vals k) lab[k]! (.Vint (ir (k : Int))) = written lab n vals (k + 1) := by
  funext p
  simp only [upd, written]
  by_cases hp : p = lab[k]!
  · subst hp
    rw [ite_eq_left rfl, ite_eq_left ⟨k, by omega, rfl⟩, inverse_get hsz hinj hk (hls k hk)]
  · rw [ite_eq_right hp]
    have : (∃ j < k + 1, lab[j]! = p) ↔ (∃ j < k, lab[j]! = p) :=
      ⟨fun ⟨j, hj, he⟩ => ⟨j, by
        rcases Nat.lt_or_ge j k with h | h
        · exact h
        · exact absurd (show j = k by omega ▸ he).symm hp, he⟩,
       fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩⟩
    by_cases hex : ∃ j < k, lab[j]! = p
    · rw [ite_eq_left (this.2 hex), ite_eq_left hex]
    · rw [ite_eq_right (fun h => hex (this.1 h)), ite_eq_right hex]

theorem eval_work1 {le : temp_env} {m : mem} {bW : block}
    (h : Mem.load .Mint64 m Block.work1 (zOfInt 0) = some (.Vptr bW Ptrofs.zero)) :
    Exec.evalExpr sge empty_env le m (.Evar id.work1 (tptr tint)) = some (.Vptr bW Ptrofs.zero) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.work1 (empty_env : env) = none from rfl,
    find_work1, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq]
  exact h

/-- The scatter loop. -/
theorem wp_scatter {f : function} {n : Nat} {Q : Post} {le : temp_env} {m : mem} {bl : block} {lofs : ptrofs}
    {bW : block} {lab : Array Nat} {vals : Nat → val}
    (hl : PTree.get id.lab le = some (.Vptr bl lofs))
    (hlarr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n)
    (hsz : lab.size = n) (hls : ∀ j < n, lab[j]! < n)
    (hinj : ∀ a b, a < n → b < n → lab[a]! = lab[b]! → a = b)
    (hsurj : ∀ p < n, ∃ j < n, lab[j]! = p)
    (hnv : PTree.get id.n le = some (.Vint (ir n))) (hn : n < 2147483648)
    (hwp : Mem.load .Mint64 m Block.work1 (zOfInt 0) = some (.Vptr bW Ptrofs.zero))
    (hwarr : ArrayAt m .Mint32 bW 0 vals n) (hbl : bl ≠ bW) (hbw : Block.work1 ≠ bW)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bW 0 (fun p => .Vint (ir (((inverse n lab)[p]! : Nat) : Int))) n →
      Unch m m' (· = bW) → Alloc.Keep m m' bW → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge f (iloop scatter) Q empty_env le m := by
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) => k ≤ n ∧
    PTree.get id.i le' = some (.Vint (ir k)) ∧ PTree.get id.n le' = some (.Vint (ir n)) ∧
    ArrayAt m' .Mint32 bW 0 (written lab n vals k) n ∧ Unch m m' (· = bW) ∧
    Alloc.Keep m m' bW ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    PTree.get id.i le' = some (.Vint (ir k)) ∧ k < n ∧ PTree.get id.n le' = some (.Vint (ir n)) ∧
    ArrayAt m' .Mint32 bW 0 (written lab n vals (k + 1)) n ∧ Unch m m' (· = bW) ∧
    Alloc.Keep m m' bW ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le
  refine wp_forLoop id.i id.n _ n hn Inv Mid ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, hn', -⟩
    exact ⟨hk, hi, hn'⟩
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hnv,
      hwarr.congr fun p _ => by simp [written], Unch.refl _ _, Alloc.Keep.refl _ _, fun _ h => h,
      fun x hx => temps_gso _ _ hx⟩
  · rintro k le' m' hk ⟨-, hi, hn', harr, hu, hkp, hg, ho⟩
    have hlk := hls k hk
    have hlarr' := hlarr.unch hu hbl
    have hl' : PTree.get id.lab le' = some (.Vptr bl lofs) := by
      rw [ho _ (by decide)]; exact hl
    have hwp' : Mem.load .Mint64 m' Block.work1 (zOfInt 0) = some (.Vptr bW Ptrofs.zero) := by
      rw [hu.load _ _ _ hbw]; exact hwp
    wp_step; wp_step
    refine wp_idx_store (chunk := .Mint32) (bo := bW) (ofs := Ptrofs.zero) harr hn (eval_work1 hwp')
      rfl rfl rfl (iat id.lab (tv id.i)) lab[k]! hlk
      (eval_tidx hlarr' hn hl' rfl rfl (tv id.i) k hk hi rfl) rfl (tv id.i) tint rfl
      (.Vint (ir k)) (.Vint (ir k)) hi rfl rfl ?_
    intro m'' harr'' hu' hk' hg'
    refine ⟨by simp, hi, hk, hn', ?_, hu.trans hu', hkp.trans hk', fun z h => hg' _ (hg _ h), ho⟩
    rw [← written_succ lab n vals k hk hsz hls hinj]
    exact harr''
  · rintro k le' m' ⟨hi, hk, hn', harr, hu, hkp, hg, ho⟩
    exact ⟨hi, by omega, temps_gss _ _ _,
      by rw [temps_gso _ _ (by decide)]; exact hn', harr, hu, hkp, hg,
      fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩
  · rintro le' m' ⟨-, -, -, harr, hu, hkp, hg, ho⟩
    refine hQ le' m' (harr.congr fun p hp => ?_) hu hkp hg ho
    obtain ⟨j, hj, he⟩ := hsurj p hp
    simp only [written]
    rw [ite_eq_left ⟨j, hj, he⟩]

/-- `*samerows = x;` -/
theorem wp_setSame {Q : Post} {le : temp_env} {m : mem} {x : ident} {c : Int} {bs : block}
    {so : ptrofs} {vals : Nat → val}
    (hsr : PTree.get id.samerows le = some (.Vptr bs so)) (hx : PTree.get x le = some (.Vint (ir c)))
    (hsarr : ArrayAt m .Mint32 bs (intOfZ (Ptrofs.unsigned so)) vals 1)
    (hQ : ∀ m', ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so)) (fun _ => .Vint (ir c)) 1 →
      Unch m m' (· = bs) → Alloc.Keep m m' bs → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 empty_env le m') :
    Wp xi sge F (setSame x) Q empty_env le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array hsarr (show 0 < 1 by decide) (.Vint (ir c)) rfl
  have harr'' : ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so)) (fun _ => .Vint (ir c)) 1 :=
    harr'.congr fun i hi => by simp [upd, show i = 0 by omega]
  have hKs : Alloc.Keep m m' bs := Alloc.Keep.store hst (by
    have := hsarr.base_nonneg
    simp only [elemOfs, intOfZ_zOfInt]; omega)
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hsr, hx, typeof, cop, Exec.assignLoc,
    Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [show Ptrofs.unsigned so = elemOfs .Mint32 (intOfZ (Ptrofs.unsigned so)) 0 by
    unfold elemOfs
    rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ], hst]
  exact hQ m' harr'' (Unch.store hst rfl) hKs (fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ h)

end NautyVerified.Proofs.Sparse.Testcanlab

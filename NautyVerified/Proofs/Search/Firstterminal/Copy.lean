import NautyVerified.Proofs.Search.Firstterminal.Syntax

/-!
# The copy loops of `firstterminal`

`wp_copyIntsG`: `for (i = 0; i < n; ++i) dst[i] = src[i];` with `n` nauty.c's
global, `dst` an `int *` global and `src` an `int *` temporary, in any program
with a `NautyEnv`; `wp_copyInts` is the dense instance.
`wp_copyShorts`: `for (i = 0; i <= level; ++i) dst[i] = src[i];` with both
`short *` globals.
-/

namespace NautyVerified.Proofs.Search.Firstterminal

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv ix)
open NautyVerified.Proofs.Alloc (gat Keep)
open NautyVerified.Proofs.Search

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

section Generic

variable {ge : genv} [E : NautyEnv ge]

theorem wp_copyIntsG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {dst src : ident} {bgD bD bs : block} {sofs : ptrofs} {vals : Nat → val} {o : Array Nat}
    {N : Nat} (hN : N < 2147483648)
    (hdE : PTree.get dst e = none) (hnE : PTree.get dense.id.«nauty:n» e = none) (hgD : Genv.find_symbol ge.genv_genv dst = some bgD)
    (hpD : Mem.load .Mint64 m bgD (zOfInt 0) = some (.Vptr bD Ptrofs.zero))
    (harr : ArrayAt m .Mint32 bD 0 vals N)
    (hsrc : PTree.get src le = some (.Vptr bs sofs))
    (hsa : ArrayAt m .Mint32 bs (intOfZ (Ptrofs.unsigned sofs)) (ints o) N)
    (hn : IntAt m E.n N) (hsi : src ≠ dense.id.i)
    (hDn : bD ≠ E.n) (hDg : bD ≠ bgD) (hDs : bD ≠ bs)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bD 0 (ints o) N → Unch m m' (· = bD) → Keep m m' bD →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (forLoopC dense.id.i
      (.Ebinop .Olt (tv dense.id.i) (.Evar dense.id.«nauty:n» tint) tint)
      (sk (.Sassign (gat dst (tv dense.id.i)) (ix src (tv dense.id.i))))) Q e le m := by
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k ≤ N ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
    (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) ∧
    ArrayAt m' .Mint32 bD 0 (fun j => if j < k then ints o j else vals j) N ∧
    Unch m m' (· = bD) ∧ Keep m m' bD ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k < N ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
    (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) ∧
    ArrayAt m' .Mint32 bD 0 (fun j => if j < k + 1 then ints o j else vals j) N ∧
    Unch m m' (· = bD) ∧ Keep m m' bD ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  refine wp_forLoopC (Inv := Inv) (Mid := Mid)
    dense.id.i _ rfl _ N hN ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, -, -, hu, -, -⟩
    refine ⟨hk, hi, ?_⟩
    rw [Exec.evalExpr, eval_gint (le := le') hnE E.find_n (hn.unch hu (Ne.symm hDn)),
      show Exec.evalExpr ge e le' m' (tv dense.id.i) = _ from hi]
    simp only [typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := (N : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, fun x hx => temps_gso _ _ hx,
      harr.congr fun j _ => by simp, Unch.refl _ _, Keep.refl _ _, fun _ h => h⟩
  · rintro k le' m' hk ⟨-, hi, ho, ha, hu, hkp, hv⟩
    have hs' : PTree.get src le' = some (.Vptr bs sofs) := by rw [ho _ hsi]; exact hsrc
    have hsv := eval_at (ge := ge) (e := e) (hsa.unch hu (Ne.symm hDs)) hN src hs'
      (tv dense.id.i) k hk hi rfl
    wp_step; wp_step
    refine wp_gstoreV hdE hgD (by rw [hu.load _ _ _ (Ne.symm hDg)]; exact hpD) ha hN
      (tv dense.id.i) k hk hi rfl (ix src (tv dense.id.i)) (o[k]! : Int) hsv rfl ?_
    intro m'' ha' hu' hk' hv'
    refine ⟨rfl, hk, hi, ho, ha'.congr fun j hj => ?_, hu.trans hu', hkp.trans hk',
      fun z hz => hv' z (hv z hz)⟩
    simp only [upd]
    split
    · rename_i h; subst h; simp [ints]
    · rename_i h
      by_cases hj : j < k
      · rw [ite_eq_left hj, ite_eq_left (by omega)]
      · rw [ite_eq_right hj, ite_eq_right (by omega)]
  · rintro k le' m' ⟨hk, hi, ho, ha, hu, hkp, hv⟩
    exact ⟨hi, hk, temps_gss _ _ _, fun x hx => by rw [temps_gso _ _ hx, ho x hx], ha, hu, hkp, hv⟩
  · rintro le' m' ⟨-, -, ho, ha, hu, hkp, hv⟩
    exact hQ le' m' (ha.congr fun j hj => by simp [hj]) hu hkp hv ho

theorem wp_copyShorts {f : function} {Q : Post} {le : temp_env} {m : mem}
    {dst src : ident} {bgD bD bgS bS : block} {vals : Nat → val} {o : Array Nat}
    {N L : Nat} (hN : N < 2147483648) (hL : L + 1 ≤ N)
    (hdE : PTree.get dst empty_env = none) (hgD : Genv.find_symbol ge.genv_genv dst = some bgD)
    (hpD : Mem.load .Mint64 m bgD (zOfInt 0) = some (.Vptr bD Ptrofs.zero))
    (harr : ArrayAt m .Mint16signed bD 0 vals N)
    (hsE : PTree.get src empty_env = none) (hgS : Genv.find_symbol ge.genv_genv src = some bgS)
    (hpS : Mem.load .Mint64 m bgS (zOfInt 0) = some (.Vptr bS Ptrofs.zero))
    (hsa : ArrayAt m .Mint16signed bS 0 (shorts o) N) (hos : ∀ j < N, o[j]! < 32768)
    (hlev : PTree.get dense.id.level le = some (.Vint (ir L)))
    (hDg : bD ≠ bgD) (hDs : bD ≠ bS) (hDgs : bD ≠ bgS)
    (hQ : ∀ le' m', ArrayAt m' .Mint16signed bD 0
        (fun j => if j < L + 1 then shorts o j else vals j) N → Unch m m' (· = bD) →
        Keep m m' bD → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi ge f (forLoopC dense.id.i
      (.Ebinop .Ole (tv dense.id.i) (tv dense.id.level) tint)
      (sk (.Sassign (gats dst (tv dense.id.i)) (gats src (tv dense.id.i))))) Q empty_env le m := by
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k ≤ L + 1 ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
    (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) ∧
    ArrayAt m' .Mint16signed bD 0 (fun j => if j < k then shorts o j else vals j) N ∧
    Unch m m' (· = bD) ∧ Keep m m' bD ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k < L + 1 ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
    (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) ∧
    ArrayAt m' .Mint16signed bD 0 (fun j => if j < k + 1 then shorts o j else vals j) N ∧
    Unch m m' (· = bD) ∧ Keep m m' bD ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  refine wp_forLoopC (Inv := Inv) (Mid := Mid)
    dense.id.i _ rfl _ (L + 1) (by omega) ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, ho, -, -, -, -⟩
    refine ⟨hk, hi, ?_⟩
    have hl' : PTree.get dense.id.level le' = some (.Vint (ir L)) := by
      rw [ho _ (by decide)]; exact hlev
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' (tv dense.id.i) = _ from hi,
      show Exec.evalExpr ge empty_env le' m' (tv dense.id.level) = _ from hl']
    simp only [typeof, cop]
    rw [ir_lt (a := (L : Int)) (b := (k : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    rw [show (!decide ((L : Int) < k)) = decide (k < L + 1) by
      by_cases h : k < L + 1
      · simp only [h, decide_true]; simp; omega
      · simp only [h, decide_false]; simp; omega]
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, fun x hx => temps_gso _ _ hx,
      harr.congr fun j _ => by simp, Unch.refl _ _, Keep.refl _ _, fun _ h => h⟩
  · rintro k le' m' hk ⟨-, hi, ho, ha, hu, hkp, hv⟩
    have hkN : k < N := by omega
    have hsv := eval_gats (e := empty_env) (le := le') hsE hgS
      (by rw [hu.load _ _ _ (Ne.symm hDgs)]; exact hpS) (hsa.unch hu (Ne.symm hDs)) hN
      (tv dense.id.i) k hkN hi rfl
    wp_step; wp_step
    refine wp_gstoreS hdE hgD (by rw [hu.load _ _ _ (Ne.symm hDg)]; exact hpD) ha hN
      (tv dense.id.i) k hkN hi rfl (gats src (tv dense.id.i)) o[k]! (hos k hkN) hsv (.inr rfl) ?_
    intro m'' ha' hu' hk' hv'
    refine ⟨rfl, hk, hi, ho, ha'.congr fun j hj => ?_, hu.trans hu', hkp.trans hk',
      fun z hz => hv' z (hv z hz)⟩
    simp only [upd]
    split
    · rename_i h; subst h; simp [shorts]
    · rename_i h
      by_cases hj : j < k
      · rw [ite_eq_left hj, ite_eq_left (by omega)]
      · rw [ite_eq_right hj, ite_eq_right (by omega)]
  · rintro k le' m' ⟨hk, hi, ho, ha, hu, hkp, hv⟩
    exact ⟨hi, hk, temps_gss _ _ _, fun x hx => by rw [temps_gso _ _ hx, ho x hx], ha, hu, hkp, hv⟩
  · rintro le' m' ⟨-, -, ho, ha, hu, hkp, hv⟩
    exact hQ le' m' ha hu hkp hv ho

end Generic

theorem wp_copyInts {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {dst src : ident} {bgD bD bs : block} {sofs : ptrofs} {vals : Nat → val} {o : Array Nat}
    {N : Nat} (hN : N < 2147483648)
    (hdE : PTree.get dst e = none) (hnE : PTree.get dense.id.«nauty:n» e = none) (hgD : Genv.find_symbol ge.genv_genv dst = some bgD)
    (hpD : Mem.load .Mint64 m bgD (zOfInt 0) = some (.Vptr bD Ptrofs.zero))
    (harr : ArrayAt m .Mint32 bD 0 vals N)
    (hsrc : PTree.get src le = some (.Vptr bs sofs))
    (hsa : ArrayAt m .Mint32 bs (intOfZ (Ptrofs.unsigned sofs)) (ints o) N)
    (hn : IntAt m Block.n N) (hsi : src ≠ dense.id.i)
    (hDn : bD ≠ Block.n) (hDg : bD ≠ bgD) (hDs : bD ≠ bs)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bD 0 (ints o) N → Unch m m' (· = bD) → Keep m m' bD →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (forLoopC dense.id.i
      (.Ebinop .Olt (tv dense.id.i) (.Evar dense.id.«nauty:n» tint) tint)
      (sk (.Sassign (gat dst (tv dense.id.i)) (ix src (tv dense.id.i))))) Q e le m :=
  wp_copyIntsG hN hdE hnE hgD hpD harr hsrc hsa hn hsi hDn hDg hDs hQ

end NautyVerified.Proofs.Search.Firstterminal

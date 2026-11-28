import NautyVerified.Proofs.Search.Processnode.Syntax
import NautyVerified.Proofs.Search.Step
import NautyVerified.Spec.Processnode
import NautyVerified.Proofs.Search.Processnode.Classifier

/-!
# `processnode`'s scatter loops

`wp_scatter`: `for (i = 0; i < n; ++i) workperm[ref[i]] = lab[i];` with `ref`
an `int *` global holding `R`, leaves `workperm` holding `scatterW R lab w n`.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv ix)
open NautyVerified.Proofs.Alloc (gat Keep eval_gat)
open NautyVerified.Proofs.Search

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {ge : genv} [E : NautyEnv ge]

theorem wp_scatter {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {ref : ident} {bgW bW bgR bR bl : block} {lofs : ptrofs} {R lab w : Array Nat} {N : Nat}
    (hN : N < 2147483648) (hwsz : w.size = N) (hR : ∀ i < N, R[i]! < N)
    (hwE : PTree.get dense.id.«nauty:workperm» e = none)
    (hgW : Genv.find_symbol ge.genv_genv dense.id.«nauty:workperm» = some bgW)
    (hpW : Mem.load .Mint64 m bgW (zOfInt 0) = some (.Vptr bW Ptrofs.zero))
    {vals : Nat → val} (harr : ArrayAt m .Mint32 bW 0 vals N)
    (hRs : ∀ j < N, ∃ i < N, R[i]! = j)
    (hrE : PTree.get ref e = none) (hgR : Genv.find_symbol ge.genv_genv ref = some bgR)
    (hpR : Mem.load .Mint64 m bgR (zOfInt 0) = some (.Vptr bR Ptrofs.zero))
    (hra : ArrayAt m .Mint32 bR 0 (ints R) N)
    (hlab : PTree.get dense.id.lab le = some (.Vptr bl lofs))
    (hla : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) N)
    (hnE : PTree.get dense.id.«nauty:n» e = none) (hn : IntAt m E.n N)
    (hWn : bW ≠ E.n) (hWg : bW ≠ bgW) (hWl : bW ≠ bl) (hWR : bW ≠ bR) (hWgR : bW ≠ bgR)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bW 0 (ints (scatterW R lab w N)) N → Unch m m' (· = bW) →
      Keep m m' bW → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f (forLoopC dense.id.i
      (.Ebinop .Olt (tv dense.id.i) (.Evar dense.id.«nauty:n» tint) tint)
      (sk (.Sassign (gat dense.id.«nauty:workperm» (gat ref (tv dense.id.i)))
        (ix dense.id.lab (tv dense.id.i))))) Q e le m := by
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k ≤ N ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
    (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) ∧
    ArrayAt m' .Mint32 bW 0
      (fun j => if ∃ i < k, R[i]! = j then ints (scatterW R lab w k) j else vals j) N ∧
    Unch m m' (· = bW) ∧ Keep m m' bW ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k < N ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
    (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) ∧
    ArrayAt m' .Mint32 bW 0
      (fun j => if ∃ i < k + 1, R[i]! = j then ints (scatterW R lab w (k + 1)) j else vals j) N ∧
    Unch m m' (· = bW) ∧ Keep m m' bW ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  refine wp_forLoopC (Inv := Inv) (Mid := Mid)
    dense.id.i _ rfl _ N hN ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, -, -, hu, -, -⟩
    refine ⟨hk, hi, ?_⟩
    rw [Exec.evalExpr, eval_gint (le := le') hnE E.find_n (hn.unch hu (Ne.symm hWn)),
      show Exec.evalExpr ge e le' m' (tv dense.id.i) = _ from hi]
    simp only [typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := (N : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, fun x hx => temps_gso _ _ hx,
      harr.congr fun j _ => by simp, Unch.refl _ _, Keep.refl _ _, fun _ h => h⟩
  · rintro k le' m' hk ⟨-, hi, ho, ha, hu, hkp, hv⟩
    have hs' : PTree.get dense.id.lab le' = some (.Vptr bl lofs) := by
      rw [ho _ (by decide)]; exact hlab
    have hsv := eval_at (ge := ge) (e := e) (hla.unch hu (Ne.symm hWl)) hN dense.id.lab hs'
      (tv dense.id.i) k hk hi rfl
    have hrv := eval_gat (le := le') hrE hgR (by rw [hu.load _ _ _ (Ne.symm hWgR)]; exact hpR)
      (hra.unch hu (Ne.symm hWR)) hN (tv dense.id.i) k hk hi rfl
    have hRk := hR k hk
    wp_step; wp_step
    refine wp_gstoreV hwE hgW (by rw [hu.load _ _ _ (Ne.symm hWg)]; exact hpW) ha hN
      (gat ref (tv dense.id.i)) R[k]! hRk hrv rfl (ix dense.id.lab (tv dense.id.i)) (lab[k]! : Int)
      hsv rfl ?_
    intro m'' ha' hu' hk' hv'
    refine ⟨rfl, hk, hi, ho, ?_, hu.trans hu', hkp.trans hk', fun z hz => hv' z (hv z hz)⟩
    have : scatterW R lab w (k + 1) = (scatterW R lab w k).set! R[k]! lab[k]! := by
      simp only [scatterW, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ha'.congr fun j hj => ?_
    rw [this, ints_set (by rw [scatterW_size, hwsz]; exact hRk)]
    simp only [upd]
    by_cases hjk : j = R[k]!
    · subst hjk
      rw [ite_eq_left rfl, ite_eq_left ⟨k, by omega, rfl⟩, ite_eq_left rfl]
    · rw [ite_eq_right hjk, ite_eq_right hjk]
      have hiff : (∃ i < k + 1, R[i]! = j) ↔ (∃ i < k, R[i]! = j) :=
        ⟨fun ⟨i, hi, he⟩ => ⟨i, by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
          · exact h
          · exact absurd (h ▸ he).symm hjk, he⟩, fun ⟨i, hi, he⟩ => ⟨i, by omega, he⟩⟩
      by_cases hex : ∃ i < k, R[i]! = j
      · rw [ite_eq_left hex, ite_eq_left (hiff.2 hex)]
      · rw [ite_eq_right hex, ite_eq_right (fun h => hex (hiff.1 h))]
  · rintro k le' m' ⟨hk, hi, ho, ha, hu, hkp, hv⟩
    exact ⟨hi, hk, temps_gss _ _ _, fun x hx => by rw [temps_gso _ _ hx, ho x hx], ha, hu, hkp, hv⟩
  · rintro le' m' ⟨-, -, ho, ha, hu, hkp, hv⟩
    exact hQ le' m' (ha.congr fun j hj => by rw [ite_eq_left (hRs j hj)]) hu hkp hv ho

end NautyVerified.Proofs.Search.Processnode

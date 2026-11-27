import NautyVerified.Proofs.Fmperm.Loop
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# `fmperm` meets its specification

`fmpermSpec`: called with a permutation `perm` of `0 .. n-1` and sets `fix`,
`mcr` of `M` words, nauty's `fmperm` leaves in `fix` and `mcr` words
representing HexGraphIso's `fmperm perm n`. Along the way `DYNALLOC1` may
replace nautil.c's `workperm` array (`DynAt`); nothing else changes.
-/

namespace NautyVerified.Proofs.Fmperm

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Spec
open NautyVerified.Proofs.Set (longs addW BitTable)
open NautyVerified.Proofs.Alloc (DynAt)
open Hex.GraphIso.Nauty (VSet)

/-- The blocks nautil.c's `workperm` pair occupies. -/
abbrev WP := Block.nautilWorkperm
abbrev WPS := Block.nautilWorkpermSz

/-- The specification of `fmperm`. -/
def fmpermSpec (bpm : block) (pofs : ptrofs) (bf : block) (fofs : ptrofs) (bm : block)
    (mofs : ptrofs) (perm : Array Nat) (n M : Nat) (wf wm : Nat → Lib.Integers.int64)
    (cap : Nat) (b0 : block) : FunSpec where
  pre args m := args = [.Vptr bpm pofs, .Vptr bf fofs, .Vptr bm mofs, .Vint (ir M), .Vint (ir n)] ∧
    ArrayAt m .Mint32 bpm (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n ∧
    ArrayAt m .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf) M ∧
    ArrayAt m .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm) M ∧
    BitTable m Block.nautilBit ∧ DynAt m WP WPS 4 cap b0 ∧
    Mem.valid_block m bpm ∧ Mem.valid_block m bf ∧ Mem.valid_block m bm ∧
    bf ≠ bm ∧ bf ≠ bpm ∧ bm ≠ bpm ∧
    (∀ z, z = WP ∨ z = WPS ∨ z = Block.nautilBit → z ≠ bpm ∧ z ≠ bf ∧ z ≠ bm) ∧
    (0 < cap → b0 ≠ bpm ∧ b0 ≠ bf ∧ b0 ≠ bm ∧ b0 ≠ Block.nautilBit) ∧
    perm.size = n ∧ (∀ x, x < n → perm[x]! < n) ∧
    (∀ x y, x < n → y < n → perm[x]! = perm[y]! → x = y) ∧
    n < 2147483648 ∧ 0 < M ∧ M < 2147483648 ∧ n ≤ 64 * M
  post _ m t _ m' := t = E0 ∧ ∃ wf' wm' cap' b',
    ArrayAt m' .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf') M ∧
    ArrayAt m' .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm') M ∧
    SetRep (fun w => bv64 (wf' w)) M (Hex.GraphIso.Nauty.fmperm perm n).1 ∧
    SetRep (fun w => bv64 (wm' w)) M (Hex.GraphIso.Nauty.fmperm perm n).2 ∧
    DynAt m' WP WPS 4 cap' b' ∧ n ≤ cap' ∧ ((cap' = cap ∧ b' = b0) ∨ ¬ Mem.valid_block m b') ∧
    Unch m m' (fun z => z = bf ∨ z = bm ∨ z = WPS ∨ z = WP ∨ (0 < cap ∧ z = b0) ∨
      (¬ Mem.valid_block m b' ∧ z = b'))

/-- The temporaries on entry. -/
def entryTemps (bpm : block) (pofs : ptrofs) (bf : block) (fofs : ptrofs) (bm : block)
    (mofs : ptrofs) (n M : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.mcr (.Vptr bm mofs) (PTree.set id.fix (.Vptr bf fofs)
      (PTree.set id.perm (.Vptr bpm pofs) (create_undef_temps Source.dense.fn.fmperm.fn_temps)))))

theorem fmperm_satisfies {xi : ExternalCalls} (bpm : block) (pofs : ptrofs) (bf : block)
    (fofs : ptrofs) (bm : block) (mofs : ptrofs) (perm : Array Nat) (n M : Nat)
    (wf wm : Nat → Lib.Integers.int64) (cap : Nat) (b0 : block) :
    Satisfies xi ge (.Internal Source.dense.fn.fmperm)
      (fmpermSpec bpm pofs bf fofs bm mofs perm n M wf wm cap b0) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bpm pofs bf fofs bm mofs n M ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bpm pofs bf fofs bm mofs n M, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hparr, hfarr, hmarr, hbit, hD, hvp, hvf, hvm, hfm, hfp, hmp, hglob, hb0,
      hps, hpl, hpi, hn, hM, hM2, hnM⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.fmperm.fn_body_eq, body_eq]
    simp only [body]
    have hnil : ∀ i, PTree.get i (empty_env : env) = none := fun _ => rfl
    have hc4 : 4 * n < 2 ^ 62 := by omega
    wp_step
    refine Alloc.wp_dynalloc1 find_nautilWorkpermSz find_nautilWorkperm rfl hD
      (by simp (config := {decide := true}) only [entryTemps, temps_gss]) hn hc4 ?_
    intro le1 m1 cap' b' hD' hcap hu1 hb' ho1
    -- the caller's blocks are outside what `DYNALLOC1` changed
    have hout : ∀ z, Mem.valid_block m z → z ≠ WPS → z ≠ WP → ¬ (0 < cap ∧ z = b0) →
        ¬ (z = WPS ∨ z = WP ∨ (0 < cap ∧ z = b0) ∨ (¬ Mem.valid_block m b' ∧ z = b')) := by
      rintro z hv h1 h2 h3 (h | h | h | ⟨hb, rfl⟩)
      · exact h1 h
      · exact h2 h
      · exact h3 h
      · exact hb hv
    sorry

end NautyVerified.Proofs.Fmperm

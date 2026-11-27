import NautyVerified.Proofs.Permset.Word
import NautyVerified.Proofs.Set.Clear

/-!
# The general case of `permset`

`wp_many`: for `m > 1`, `EMPTYSET(set2, m)` followed by the loop over the
words of `set1` leaves `set2` representing HexGraphIso's `s.permset perm`.
-/

namespace NautyVerified.Proofs.Permset

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs)
open Hex.GraphIso.Nauty (VSet)

variable {xi : ExternalCalls}

theorem wp_many {Q : Post} {f : function} {le : temp_env} {m : mem} {n : Nat} {b1 : block}
    {o1 : ptrofs} {w1 : Nat → Lib.Integers.int64} {s : VSet n} {bp : block} {po : ptrofs}
    {perm : Array Nat} {b2 : block} {o2 : ptrofs} {M : Nat} {w2 : Nat → Lib.Integers.int64}
    (h : Frame m le b1 o1 w1 s bp po perm b2 o2 M) (hM : 0 < M)
    (harr2 : ArrayAt m .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2) M)
    (hQ : ∀ le' m' w2', ArrayAt m' .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2') M →
      SetRep (fun w => bv64 (w2' w)) M (s.permset perm) → Unch m m' (· = b2) →
      Outside m m' b2 (intOfZ (Ptrofs.unsigned o2)) (intOfZ (Ptrofs.unsigned o2) + 8 * M) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f many Q empty_env le m := by
  have hMlt := h.Mlt
  have hnM := h.rep1.1
  wp_step
  refine Set.wp_emptySet' (by decide) (by decide) (by decide) harr2 hM (by omega) h.hset2 h.hm ?_
  intro le1 m1 harr1 hu1 hout1 ho1
  have hf1 := (h.temps fun y _ _ _ _ h5 _ h7 _ => ho1 y h5 h7).unch hu1
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) => k ≤ M ∧
    PTree.get id.w le' = some (.Vint (ir k)) ∧ ∃ w2' acc, Frame m' le' b1 o1 w1 s bp po perm b2 o2 M ∧
      ArrayAt m' .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2') M ∧
      SetRep (fun w => bv64 (w2' w)) M acc ∧ Covers acc s perm (fun u => u < 64 * k) ∧
      Unch m m' (· = b2) ∧
      Outside m m' b2 (intOfZ (Ptrofs.unsigned o2)) (intOfZ (Ptrofs.unsigned o2) + 8 * M)
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    PTree.get id.w le' = some (.Vint (ir k)) ∧ k < M ∧ ∃ w2' acc,
      Frame m' le' b1 o1 w1 s bp po perm b2 o2 M ∧
      ArrayAt m' .Mint64 b2 (intOfZ (Ptrofs.unsigned o2)) (longs w2') M ∧
      SetRep (fun w => bv64 (w2' w)) M acc ∧ Covers acc s perm (fun u => u < 64 * (k + 1)) ∧
      Unch m m' (· = b2) ∧
      Outside m m' b2 (intOfZ (Ptrofs.unsigned o2)) (intOfZ (Ptrofs.unsigned o2) + 8 * M)
  refine wp_forLoop id.w id.m word M (by omega) Inv Mid ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hw, w2', acc, hf, -⟩
    exact ⟨hk, hw, hf.hm⟩
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, _, VSet.empty,
      hf1.temps fun y _ _ _ h4 _ _ _ _ => temps_gso _ _ h4, harr1, Set.setRep_zero hnM,
      covers_empty s perm, hu1, hout1⟩
  · rintro k le' m' hk ⟨-, hw, w2', acc, hf, harr', hrep', hcov', hu, hout⟩
    refine wp_word hf w2' acc harr' hrep' hcov' hw hk ?_
    intro le2 m2 w2'' acc' harr2 hrep2 hcov2 hu2 hout2 ho2
    exact ⟨rfl, by rw [ho2 _ (by decide) (by decide) (by decide) (by decide)]; exact hw, hk, w2'', acc',
      (hf.temps fun y h1 h2 h3 _ _ _ _ h8 => ho2 y h1 h2 h3 h8).unch hu2, harr2, hrep2, hcov2, hu.trans hu2,
      hout.trans hout2⟩
  · rintro k le' m' ⟨hw, hk, w2', acc, hf, harr', hrep', hcov', hu, hout⟩
    exact ⟨hw, by omega, temps_gss _ _ _, w2', acc, hf.temps fun y _ _ _ h4 _ _ _ _ => temps_gso _ _ h4,
      harr', hrep', hcov', hu, hout⟩
  · rintro le' m' ⟨-, -, w2', acc, hf, harr', hrep', hcov', hu, hout⟩
    refine hQ le' m' w2' harr' ?_ hu hout
    rw [← covers_image (hcov'.congr fun u hu => ⟨fun _ => trivial, fun _ => by
      have := VSet.mem_lt hu; omega⟩) h.psmall]
    exact hrep'

end NautyVerified.Proofs.Permset

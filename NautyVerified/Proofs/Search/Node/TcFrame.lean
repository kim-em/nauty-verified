import NautyVerified.Proofs.Search.Node.Tc
import NautyVerified.Proofs.Search.Node.Prune

/-!
# The target-cell list across a node's own steps

- `TcChain.setCell`: after a change to some blocks outside the list, and to
  one target cell `c` that still holds `M` words, the list is unchanged;
- `TcOk.mono`: the list's blocks stay valid and apart from `S` and from the
  work arrays when every new work block was a work block or not valid before.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program

theorem TcChain.setCell {m m' : mem} {M : Nat} {W : block → Prop} (hu : Unch m m' W) {c : block}
    (hc : ∃ vals, ArrayAt m' .Mint64 c 0 vals M) :
    ∀ {prev : block} {chain : List (block × block)}, TcChain m M prev chain →
      (∀ z ∈ tcBlocks prev chain, z ≠ c → ¬ W z) → prev ≠ c →
      (∀ p ∈ chain, p.1 ≠ c) → TcChain m' M prev chain
  | _, [], h, hS, hp, _ => h.unch' hu (hS _ (.head _) hp)
  | prev, (nd, tc) :: rest, h, hS, hp, h1 => by
    obtain ⟨f1, f2, ⟨vals, f3⟩, f4⟩ := h
    have hnd : nd ≠ c := h1 (nd, tc) (.head _)
    have mnd : nd ∈ tcBlocks prev ((nd, tc) :: rest) := by simp [tcBlocks]
    have mtc : tc ∈ tcBlocks prev ((nd, tc) :: rest) := by simp [tcBlocks]
    refine ⟨f1.unch' hu (hS _ (.head _) hp), f2.unch' hu (hS nd mnd hnd), ?_,
      TcChain.setCell hu hc f4 (fun z hz hzc => hS z ?_ hzc) hnd
        (fun p hp' => h1 p (.tail _ hp'))⟩
    · by_cases htc : tc = c
      · subst htc; exact hc
      · exact ⟨vals, f3.unch hu (hS tc mtc htc)⟩
    · simp only [tcBlocks, List.mem_cons, List.flatMap_cons, List.mem_append] at hz ⊢
      rcases hz with rfl | hz
      · exact .inr (.inl (.inl rfl))
      · exact .inr (.inr hz)

theorem TcOk.mono {m m' : mem} {S : SLoc} {chain : List (block × block)} (h : TcOk m S chain)
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    (hw : ∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z) : TcOk m' S chain where
  pairwise := h.pairwise
  valid := fun p hp => ⟨hg _ (h.valid p hp).1, hg _ (h.valid p hp).2⟩
  apart := fun p hp => by
    obtain ⟨a1, a2, a3, a4⟩ := h.apart p hp
    obtain ⟨v1, v2⟩ := h.valid p hp
    refine ⟨a1, a2, fun hz => ?_, fun hz => ?_⟩
    · rcases hw _ hz with hz' | hz'
      · exact a3 hz'
      · exact hz' v1
    · rcases hw _ hz with hz' | hz'
      · exact a4 hz'
      · exact hz' v2

end NautyVerified.Proofs.Search

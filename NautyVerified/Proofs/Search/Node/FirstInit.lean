import NautyVerified.Proofs.Search.Node.FirstEntry

/-!
# `firstpathnode0`'s memory after its prologue

`HeadAt.init`: after the locals are allocated and the prologue has found or
allocated this level's target-cell entry (`wp_nodePrologue`), memory is in
`HeadAt`. `HeadAt.stepS`: a step that changes only blocks of `S`, blocks new
since the last step and work blocks keeps `HeadAt`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty

variable {n : Nat}

theorem HeadAt.init {L : LCtx n} {mA m₁ : mem} {st : Search n} {pre : Bool}
    {chain' : List (block × block)}
    (h0 : SearchAt L.m₀ L.S L.ctx st pre false) (hTo0 : TcOk L.m₀ L.S L.chain₀)
    (hl1 : 1 ≤ L.level) (hlen : L.level - 1 ≤ L.chain₀.length)
    (huaV : Mem.valid_block L.m₀ L.S.bUA) (huaP : Mem.perm L.m₀ L.S.bUA (zOfInt 0) .Cur .Nonempty)
    (hLF : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z) (hLS : ∀ z ∈ L.locals, z ∉ L.S.blocks)
    (huA : Unch L.m₀ mA (fun z => ¬ Mem.valid_block L.m₀ z))
    (hgA : ∀ z, Mem.valid_block L.m₀ z → Mem.valid_block mA z) (hwmA : WorkMono L.m₀ mA)
    (haccA : ∀ z ∈ L.locals, Mem.valid_access mA .Mint32 z (zOfInt 0) .Freeable)
    (hwkA : ∀ z ∈ L.locals, ¬ IsWork mA z)
    (hcA : ∀ z ∈ L.locals, ∀ p ∈ L.chain₀, p.1 ≠ z ∧ p.2 ≠ z)
    (hS1 : SearchAt m₁ L.S L.ctx st pre false)
    (hTc1 : TcChain m₁ L.S.M Block.tcnode0 chain') (hTo1 : TcOk m₁ L.S chain')
    (hown : chain'[L.level - 1]? = some (L.bnd, L.btc))
    (htake : chain'.take (L.level - 1) = L.chain₀.take (L.level - 1))
    (hold : ∀ p ∈ chain', p ∈ L.chain₀ ∨ (¬ Mem.valid_block mA p.1 ∧ ¬ Mem.valid_block mA p.2))
    (hcell : ∃ vals, ArrayAt m₁ .Mint64 L.btc 0 vals L.S.M)
    (hU1 : Unch mA m₁ (fun z => z = L.bnc ∨ z = tcParent L.chain₀ L.level ∨
      ¬ Mem.valid_block mA z))
    (hg1 : ∀ z, Mem.valid_block mA z → Mem.valid_block m₁ z) (hwm1 : WorkMono mA m₁)
    (hK1 : Keep mA m₁ L.bnc) :
    HeadAt L m₁ st pre false chain' := by
  have hd := h0.distinct
  have hpT := tcParent_mem hl1 hlen
  have hlocP : ∀ z ∈ L.locals, z ≠ tcParent L.chain₀ L.level := by
    intro z hz e
    have := hpT; rw [← e] at this
    simp only [tcBlocks, List.mem_cons] at this
    rcases this with e' | hz'
    · exact hLS z hz (e' ▸ by simp [SLoc.blocks])
    · obtain ⟨p, hp, hz'⟩ := List.mem_flatMap.1 hz'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz'
      rcases hz' with e' | e'
      · exact (hcA z hz p hp).1 e'.symm
      · exact (hcA z hz p hp).2 e'.symm
  have hout : ∀ z ∈ L.locals, z ≠ L.bnc →
      ¬ (z = L.bnc ∨ z = tcParent L.chain₀ L.level ∨ ¬ Mem.valid_block mA z) := by
    intro z hz hb
    rintro (e | e | e)
    · exact hb e
    · exact hlocP z hz e
    · exact e (Alloc.valid_of_access (haccA z hz))
  have hkl : ∀ z ∈ L.locals, Keep mA m₁ z := fun z hz => by
    by_cases hb : z = L.bnc
    · subst hb; exact hK1
    · exact Keep.unch hU1 (hout z hz hb)
  have hvA : ∀ z ∈ L.locals, Mem.valid_block mA z := fun z hz => Alloc.valid_of_access (haccA z hz)
  have hpar : L.S.bUA ≠ tcParent L.chain₀ L.level := by
    intro e
    rw [tcParent_eq hl1 hlen] at e
    rcases prevAt_mem_nodes Block.tcnode0 L.chain₀ (L.level - 1) with h' | ⟨p, hp, h'⟩
    · exact (show L.S.bUA ≠ Block.tcnode0 by sep_ne hd) (e.trans h')
    · exact (hTo0.apart p hp).1 (h' ▸ e ▸ by simp [SLoc.blocks])
  have hlen' : L.level ≤ chain'.length := by
    have := hown; rw [List.getElem?_eq_some_iff] at this; obtain ⟨h1, -⟩ := this; omega
  refine
    { search := hS1
      cellv := hcell
      locA := fun z hz => by
        obtain ⟨_, -, hv⟩ := arrayAt_of_access (Search.Keep.access (hkl z hz) (haccA z hz))
        exact hv
      chain :=
        { chain := hTc1, ok := hTo1, len := hlen', own := hown, take := htake
          fresh := fun p hp => by
            rcases hold p hp with hp' | ⟨h1, h2⟩
            · exact .inl hp'
            · exact .inr ⟨fun hv => h1 (hgA _ hv), fun hv => h2 (hgA _ hv)⟩
          apart := fun p hp => by
            rcases hold p hp with hp' | ⟨h1, h2⟩
            · exact ⟨fun hz => (hcA _ hz p hp').1 rfl, fun hz => (hcA _ hz p hp').2 rfl⟩
            · exact ⟨fun hz => h1 (hvA _ hz), fun hz => h2 (hvA _ hz)⟩
          lvl := hl1 }
      frame := ⟨(huA.mono fun z hz => .inr (.inl hz)).trans (hU1.mono fun z hz => by
          rcases hz with e | e | e
          · rw [e]; exact .inr (.inl (hLF _ (by simp [LCtx.locals])))
          · rw [e]; exact nset_parent hlen
          · exact .inr (.inl fun hv => e (hgA _ hv))), fun z hz => hg1 z (hgA z hz)⟩
      work := fun z hz => by
        rcases hwm1 z hz with h1 | h1
        · rcases hwmA z h1 with h2 | h2
          · exact .inl h2
          · exact .inr h2
        · exact .inr fun hv => h1 (hgA _ hv)
      locals := fun z hz => ⟨hg1 z (hvA z hz), hLS z hz, fun hw => by
          rcases hwm1 z hw with h1 | h1
          · exact hwkA z hz h1
          · exact h1 (hvA z hz)⟩
      fre := fun z hz => Search.Keep.access (hkl z hz) (haccA z hz)
      vU := hg1 _ (hgA _ huaV)
      pU := perm_unch hU1 (by
          rintro (e | e | e)
          · apply hLS L.bnc (by simp [LCtx.locals]); rw [← e]; simp [SLoc.blocks]
          · exact hpar e
          · exact e (hgA _ huaV))
        (perm_unch huA (fun e => e huaV) huaP) }

/-- A step that changes only blocks of `S`, new blocks and work blocks keeps `HeadAt`. -/
theorem HeadAt.stepS {L : LCtx n} {m : mem} {st : Search n} {pre nsp : Bool}
    {ch : List (block × block)} (h : HeadAt L m st pre nsp ch)
    (hfresh : ∀ z ∈ L.locals, ¬ Mem.valid_block L.m₀ z)
    {m' : mem} {st' : Search n} {pre' nsp' : Bool} {W : block → Prop}
    (hS : SearchAt m' L.S L.ctx st' pre' nsp') (hu : Unch m m' W)
    (hW : ∀ z, W z → L.S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z)
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) (hwm : WorkMono m m') :
    HeadAt L m' st' pre' nsp' ch := by
  have hmem := List.mem_of_getElem? h.chain.own
  obtain ⟨-, b2, -, b4⟩ := h.chain.ok.apart _ hmem
  have nbt : ¬ W L.btc := fun hz => by
    rcases hW _ hz with h1 | h1 | h1
    · exact b2 h1.1
    · exact h1 (h.chain.ok.valid _ hmem).2
    · exact b4 h1
  have nloc : ∀ z ∈ L.locals, ¬ W z := fun z hz hw => by
    obtain ⟨a, b, c⟩ := h.locals z hz
    rcases hW _ hw with h1 | h1 | h1
    · exact b h1.1
    · exact h1 a
    · exact c h1
  obtain ⟨cv, hcv⟩ := h.cellv
  exact h.step hfresh hS (hu.mono fun z hz => by
      rcases hW z hz with h1 | h1 | h1
      · exact .inl (.inl h1)
      · exact .inl (.inr (.inl h1))
      · exact .inl (.inr (.inr (.inl h1)))) hg hwm ⟨cv, hcv.unch hu nbt⟩ (Keep.unch hu nbt)
    (fun z hz => by obtain ⟨v, hv⟩ := h.locA z hz; exact ⟨v, hv.unch hu (nloc z hz)⟩)
    (fun z hz => Keep.unch hu (nloc z hz))

end NautyVerified.Proofs.Search

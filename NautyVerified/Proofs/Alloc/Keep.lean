import NautyVerified.Proofs.Alloc.Dyn

/-!
# Keeping a `malloc`ed block allocated

`Keep m m' b`: `b`'s bytes below offset 0 (the `malloc` header) and its
permissions are as before. Stores into `b` at offsets `≥ 0` keep it, and so
does any change outside `b`; `Malloced` and `DynAt` survive it.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word

structure Keep (m m' : mem) (b : block) : Prop where
  low : ∀ chunk (ofs : Int), ofs + csize chunk ≤ 0 →
    Mem.load chunk m' b (zOfInt ofs) = Mem.load chunk m b (zOfInt ofs)
  perm : ∀ ofs p, Mem.perm m b ofs .Cur p → Mem.perm m' b ofs .Cur p

theorem Keep.refl (m : mem) (b : block) : Keep m m b := ⟨fun _ _ _ => rfl, fun _ _ h => h⟩

theorem Keep.trans {m₁ m₂ m₃ : mem} {b : block} (h₁ : Keep m₁ m₂ b) (h₂ : Keep m₂ m₃ b) :
    Keep m₁ m₃ b :=
  ⟨fun c o h => by rw [h₂.low c o h, h₁.low c o h], fun _ _ h => h₂.perm _ _ (h₁.perm _ _ h)⟩

/-- A store into `b` at an offset `≥ 0`. -/
theorem Keep.store {m m' : mem} {chunk : memory_chunk} {b : block} {ofs : Z} {v : val}
    (h : Mem.store chunk m b ofs v = some m') (hofs : 0 ≤ intOfZ ofs) : Keep m m' b :=
  ⟨fun c o hco => by
    apply Mem.load_store_other _ _ _ _ _ _ h
    right; left
    change intOfZ _ ≤ intOfZ _
    simp only [intOfZ_add, intOfZ_zOfInt]
    have : intOfZ (size_chunk c) = csize c := rfl
    omega,
   fun _ _ hp => Mem.perm_store_1 _ _ _ _ _ _ h _ _ _ _ hp⟩

/-- A change outside `b`. -/
theorem Keep.unch {m m' : mem} {S : block → Prop} {b : block} (hu : Unch m m' S) (hb : ¬ S b) :
    Keep m m' b :=
  ⟨fun c o _ => hu.load _ _ _ hb, fun ofs p hp => by
    have hva : Mem.valid_access m .Mint8unsigned b ofs p := by
      refine ⟨fun o ho => ?_, ⟨ofs, by
        apply intOfZ_injective
        simp [show intOfZ (align_chunk .Mint8unsigned) = 1 from rfl]⟩⟩
      have h1 : intOfZ ofs ≤ intOfZ o := ho.1
      have h2 : intOfZ o < intOfZ ofs + 1 := by
        have := ho.2; change intOfZ _ < intOfZ _ at this
        simpa [intOfZ_add, show intOfZ (size_chunk .Mint8unsigned) = 1 from rfl] using this
      rw [show o = ofs by apply intOfZ_injective; omega]
      exact hp
    have := hu.access _ _ _ _ hb hva
    exact this.1 ofs ⟨by change intOfZ _ ≤ intOfZ _; exact Int.le_refl _, by
      change intOfZ _ < intOfZ _
      simp only [intOfZ_add, show intOfZ (size_chunk .Mint8unsigned) = 1 from rfl]; omega⟩⟩

/-- `b`'s bytes below offset 0 are as before and every access to `b` survives. -/
theorem Keep.of_access {m m' : mem} {b : block}
    (hl : ∀ chunk (ofs : Int), ofs + csize chunk ≤ 0 →
      Mem.load chunk m' b (zOfInt ofs) = Mem.load chunk m b (zOfInt ofs))
    (ha : ∀ chunk ofs p, Mem.valid_access m chunk b ofs p → Mem.valid_access m' chunk b ofs p) :
    Keep m m' b :=
  ⟨hl, fun ofs p hp => by
    have hva : Mem.valid_access m .Mint8unsigned b ofs p := by
      refine ⟨fun o ho => ?_, ⟨ofs, by
        apply intOfZ_injective
        simp [show intOfZ (align_chunk .Mint8unsigned) = 1 from rfl]⟩⟩
      have h1 : intOfZ ofs ≤ intOfZ o := ho.1
      have h2 : intOfZ o < intOfZ ofs + 1 := by
        have := ho.2; change intOfZ _ < intOfZ _ at this
        simpa [intOfZ_add, show intOfZ (size_chunk .Mint8unsigned) = 1 from rfl] using this
      rw [show o = ofs by apply intOfZ_injective; omega]
      exact hp
    exact (ha _ _ _ hva).1 ofs ⟨by change intOfZ _ ≤ intOfZ _; exact Int.le_refl _, by
      change intOfZ _ < intOfZ _
      simp only [intOfZ_add, show intOfZ (size_chunk .Mint8unsigned) = 1 from rfl]; omega⟩⟩

/-- A change confined to offsets `≥ 0` of `b` keeps it. -/
theorem Keep.of_outside {m m' : mem} {b : block} {hi : Int} (ho : Outside m m' b 0 hi) :
    Keep m m' b :=
  ⟨fun c o h => ho.load c o (.inl h), fun ofs p hp => by
    have hva : Mem.valid_access m .Mint8unsigned b ofs p := by
      refine ⟨fun o ho' => ?_, ⟨ofs, by
        apply intOfZ_injective
        simp [show intOfZ (align_chunk .Mint8unsigned) = 1 from rfl]⟩⟩
      have h1 : intOfZ ofs ≤ intOfZ o := ho'.1
      have h2 : intOfZ o < intOfZ ofs + 1 := by
        have := ho'.2; change intOfZ _ < intOfZ _ at this
        simpa [intOfZ_add, show intOfZ (size_chunk .Mint8unsigned) = 1 from rfl] using this
      rw [show o = ofs by apply intOfZ_injective; omega]
      exact hp
    exact (ho.access _ _ _ hva).1 ofs ⟨by change intOfZ _ ≤ intOfZ _; exact Int.le_refl _, by
      change intOfZ _ < intOfZ _
      simp only [intOfZ_add, show intOfZ (size_chunk .Mint8unsigned) = 1 from rfl]; omega⟩⟩

theorem Malloced.keep {m m' : mem} {b : block} {N : Nat} (h : Malloced m b N) (hk : Keep m m' b) :
    Malloced m' b N :=
  ⟨by rw [Mptr_eq, hk.low .Mint64 (-8) (by decide)]; exact h.hdr,
   fun o h1 h2 => hk.perm _ _ (h.perm o h1 h2), h.small⟩

/-- `DynAt` survives changes outside its globals that keep its block. -/
theorem DynAt.keep {m m' : mem} {bp bs : block} {c cap : Nat} {b : block}
    (h : DynAt m bp bs c cap b) {S : block → Prop} (hu : Unch m m' S) (hp : ¬ S bp) (hs : ¬ S bs)
    (hk : 0 < cap → Keep m m' b) : DynAt m' bp bs c cap b :=
  { h with
    capLd := by rw [hu.load _ _ _ hs]; exact h.capLd
    bsW := hu.access _ _ _ _ hs h.bsW
    bpW := hu.access _ _ _ _ hp h.bpW
    ptr := fun hc => by rw [hu.load _ _ _ hp]; exact h.ptr hc
    mal := fun hc => (h.mal hc).keep (hk hc)
    null := fun hc => by rw [hu.load _ _ _ hp]; exact h.null hc }

end NautyVerified.Proofs.Alloc

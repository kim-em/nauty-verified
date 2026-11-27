import NautyVerified.Proofs.Alloc.Malloc
import NautyVerified.Proofs.Alloc.Free

/-!
# Addressable `int` locals

nauty.c's search functions take the address of some `int` locals
(`&numcells`, `&tc`, `&tcellsize`, `&qinvar`, `&refcode`; `&sr` in
`processnode`), so Clight allocates them on entry. `alloc_ints`: allocating
any list of `int` locals succeeds, gives each a block not valid before with
`Freeable` permission on its four bytes, distinct blocks for distinct names,
and changes nothing else.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Proofs NautyVerified.Word

/-- `x` is bound in `e` to block `b`, an `int`. -/
abbrev Bound (e : env) (x : ident) (b : block) : Prop := PTree.get x e = some (b, tint)

theorem alloc_ints : ∀ (ids : List ident) (e0 : env) (m : mem), ids.Nodup →
    ∃ e m', alloc_variables ge e0 m (ids.map fun x => (x, tint)) e m' ∧
      (∀ x, x ∉ ids → PTree.get x e = PTree.get x e0) ∧
      (∀ x ∈ ids, ∃ b, Bound e x b ∧ ¬ Mem.valid_block m b ∧ Mem.valid_block m' b ∧
        Mem.valid_access m' .Mint32 b (zOfInt 0) .Freeable) ∧
      (∀ x ∈ ids, ∀ y ∈ ids, x ≠ y → ∀ bx by_, Bound e x bx → Bound e y by_ → bx ≠ by_) ∧
      Unch m m' (fun z => ¬ Mem.valid_block m z) ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  | [], e0, m, _ => ⟨e0, m, .nil _ _, fun _ _ => rfl, fun _ h => absurd h (by simp),
      fun _ h => absurd h (by simp), Unch.refl _ _, fun _ h => h⟩
  | x :: rest, e0, m, hnd => by
    rw [List.nodup_cons] at hnd
    obtain ⟨m1, b1⟩ := Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint) |> fun p => (p.1, p.2)
    have hal : Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint) =
        ((Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint)).1,
         (Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint)).2) := rfl
    generalize (Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint)).1 = m1 at hal
    generalize (Mem.alloc m (zOfInt 0) (sizeof ge.genv_cenv tint)).2 = b1 at hal
    obtain ⟨e, m', hav, hout, hin, hdist, hu, hg⟩ :=
      alloc_ints rest (PTree.set x (b1, tint) e0) m1 hnd.2
    have hfresh : ¬ Mem.valid_block m b1 := Mem.fresh_block_alloc _ _ _ _ _ hal
    have hv1 : ∀ z, Mem.valid_block m z → Mem.valid_block m1 z := Mem.valid_block_alloc _ _ _ _ _ hal
    have hb1 : Bound e x b1 := by
      show PTree.get x e = _
      rw [hout x hnd.1, PTree.gss]
    have hva1 : Mem.valid_access m1 .Mint32 b1 (zOfInt 0) .Freeable := by
      refine ⟨fun o ho => Mem.perm_alloc_2 _ _ _ _ _ hal o .Cur ⟨?_, ?_⟩, ⟨zOfInt 0, rfl⟩⟩
      · exact ho.1
      · have := ho.2
        change intOfZ _ < intOfZ _ at this ⊢
        have h4 : intOfZ (Common.Memdata.size_chunk .Mint32) = 4 := rfl
        simp only [intOfZ_add, intOfZ_zOfInt, h4, Int.zero_add] at this
        exact this
    refine ⟨e, m', .cons _ _ _ _ _ _ _ _ _ hal hav, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      rw [hout y (fun h => hy (.tail _ h)), PTree.gso _ _ (by rintro rfl; exact hy (.head _))]
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨b1, hb1, hfresh, hg _ (Mem.valid_new_block _ _ _ _ _ hal),
          hu.access _ _ _ _ (fun h => h (Mem.valid_new_block _ _ _ _ _ hal)) hva1⟩
      · obtain ⟨b, hb, hnv, hvb, hp⟩ := hin y hy
        exact ⟨b, hb, fun h => hnv (hv1 _ h), hvb, hp⟩
    · intro y hy z hz hyz by_ bz hby hbz
      have key : ∀ w ∈ rest, ∀ bw, Bound e w bw → bw ≠ b1 := fun w hw bw hbw h => by
        obtain ⟨b, hb, hnv, -, -⟩ := hin w hw
        have : bw = b := by
          have := hbw.symm.trans hb; cases this; rfl
        exact hnv (this ▸ h ▸ Mem.valid_new_block _ _ _ _ _ hal)
      rcases List.mem_cons.1 hy with rfl | hy' <;> rcases List.mem_cons.1 hz with rfl | hz'
      · exact absurd rfl hyz
      · have : by_ = b1 := by have := hby.symm.trans hb1; cases this; rfl
        subst this; exact (key z hz' bz hbz).symm
      · have : bz = b1 := by have := hbz.symm.trans hb1; cases this; rfl
        subst this; exact key y hy' by_ hby
      · exact hdist y hy' z hz' hyz by_ bz hby hbz
    · exact (Alloc.Unch.alloc hal |>.mono fun z hz => hz ▸ hfresh).trans
        (hu.mono fun z hz h => hz (hv1 _ h))
    · exact fun z h => hg _ (hv1 _ h)

/-- Freeing a list of distinct `int` locals, each `Freeable`, succeeds and
changes only them. -/
theorem free_ints : ∀ (l : List block) (m : mem), l.Nodup →
    (∀ b ∈ l, Mem.valid_access m .Mint32 b (zOfInt 0) .Freeable) →
    ∃ m', Mem.free_list m (l.map fun b => (b, zOfInt 0, sizeof ge.genv_cenv tint)) = some m' ∧
      Unch m m' (· ∈ l)
  | [], m, _, _ => ⟨m, rfl, Unch.refl _ _⟩
  | b :: rest, m, hnd, hva => by
    rw [List.nodup_cons] at hnd
    have hr : Mem.range_perm m b (zOfInt 0) (sizeof ge.genv_cenv tint) .Cur .Freeable :=
      (hva b (.head _)).1
    obtain ⟨m1, hf⟩ := Mem.range_perm_free m b (zOfInt 0) (sizeof ge.genv_cenv tint) hr
    have hu1 := Alloc.Unch.free hf
    obtain ⟨m', hl, hu⟩ := free_ints rest m1 hnd.2 fun b' hb' =>
      hu1.access _ _ _ _ (fun h => hnd.1 (h ▸ hb')) (hva b' (.tail _ hb'))
    refine ⟨m', ?_, (hu1.mono fun z hz => hz ▸ .head _).trans (hu.mono fun z hz => .tail _ hz)⟩
    simp only [List.map_cons, Mem.free_list, hf]
    exact hl

end NautyVerified.Proofs.Search

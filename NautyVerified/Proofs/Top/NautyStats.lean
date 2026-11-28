import NautyVerified.Proofs.Top.NautyOrbits

/-!
# `nauty()`'s statistics and level counters (`tStats`)

`stats->grpsize1 = 1.0; stats->grpsize2 = 0;` (reported, as `firstpathnode0`'s
`MULTIPLY` reads them) and the counters zeroed,
`stats->numorbits = n`, `EMPTYSET(fixedpts, m)`, `noncheaplevel = 1`,
`eqlev_canon = -1`.
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (FieldAt IntAt PtrAt SLoc)

set_option linter.unusedSimpArgs false

/-- A field of an 88-byte block held `Freeable` is writable. -/
theorem va88 {m : mem} {b : block}
    (h : Mem.range_perm m b (zOfInt 0) (zOfInt 88) .Cur .Freeable) (chunk : memory_chunk) (off : Int)
    (h0 : 0 ≤ off) (h1 : off + csize chunk ≤ 88)
    (hal : ZArith.BinInt.Z.divide (Common.Memdata.align_chunk chunk) (zOfInt off)) :
    Mem.valid_access m chunk b (zOfInt off) .Writable := by
  refine ⟨fun o ho => Mem.perm_implies _ _ _ _ _ _ (h o ⟨?_, ?_⟩) (.perm_F_any _), hal⟩
  · have := ho.1
    change intOfZ _ ≤ intOfZ _ at this ⊢
    simp only [intOfZ_zOfInt] at this ⊢
    omega
  · have := ho.2
    change intOfZ o < intOfZ (ZArith.BinInt.Z.add (zOfInt off) _) at this
    change intOfZ o < intOfZ _
    rw [intOfZ_add, intOfZ_zOfInt] at this
    simp only [intOfZ_zOfInt]
    have : intOfZ (Common.Memdata.size_chunk chunk) = csize chunk := rfl
    omega

variable {xi : ExternalCalls}

/-- The statistics, `fixedpts` and level counters (`tStats`). -/
theorem wp_tStats {Q : Post} {le : temp_env} {m : mem} {S : SLoc} {n M : Nat} {bF : block}
    {fv : Nat → val}
    (hso : S.sofs = Ptrofs.zero)
    (hst : PtrAt m Search.Block.stats (.Vptr S.bst S.sofs))
    (hR : Mem.range_perm m S.bst (zOfInt 0) (zOfInt 88) .Cur .Freeable)
    (hn : n < 2147483648) (hN : IntAt m Search.Block.n n) (hMm : IntAt m Search.Block.m M)
    (hM0 : 0 < M) (hM : M < 2147483648)
    (hF : Mem.load .Mint64 m Block.nautyFixedpts (zOfInt 0) = some (.Vptr bF Ptrofs.zero))
    (hfw : ArrayAt m .Mint64 bF 0 fv M)
    (hwN : Mem.valid_access m .Mint32 Search.Block.noncheaplevel (zOfInt 0) .Writable)
    (hwE : Mem.valid_access m .Mint32 Search.Block.eqlevCanon (zOfInt 0) .Writable)
    (hsep : S.bst ≠ Search.Block.n ∧ S.bst ≠ Search.Block.stats ∧ S.bst ≠ Search.Block.m ∧
      S.bst ≠ Block.nautyFixedpts ∧ S.bst ≠ bF ∧ S.bst ≠ Search.Block.noncheaplevel ∧
      S.bst ≠ Search.Block.eqlevCanon)
    (hsepF : bF ≠ Search.Block.m ∧ bF ≠ Block.nautyFixedpts ∧ bF ≠ Search.Block.noncheaplevel ∧
      bF ≠ Search.Block.eqlevCanon)
    (hQ : ∀ le' m', FieldAt m' .Mfloat64 S.bst (S.sb + 0)
        (.Vfloat (CompCert4Lean.Lib.Floats.Float.of_bits (lr 4607182418800017408))) →
      FieldAt m' .Mint32 S.bst (S.sb + 8) (.Vint (ir 0)) →
      FieldAt m' .Mint32 S.bst (S.sb + 12) (.Vint (ir n)) →
      FieldAt m' .Mint32 S.bst (S.sb + 16) (.Vint (ir 0)) →
      FieldAt m' .Mint64 S.bst (S.sb + 24) (.Vlong (lr 0)) →
      FieldAt m' .Mint64 S.bst (S.sb + 32) (.Vlong (lr 0)) →
      Mem.valid_access m' .Mint32 S.bst (zOfInt (S.sb + 40)) .Writable →
      FieldAt m' .Mint64 S.bst (S.sb + 48) (.Vlong (lr 0)) →
      FieldAt m' .Mint64 S.bst (S.sb + 56) (.Vlong (lr 0)) →
      ArrayAt m' .Mint64 bF 0 (Set.longs fun _ => lr 0) M →
      IntAt m' Search.Block.noncheaplevel 1 → IntAt m' Search.Block.eqlevCanon (-1) →
      Unch m m' (fun z => z = S.bst ∨ z = bF ∨ z = Search.Block.noncheaplevel ∨
        z = Search.Block.eqlevCanon) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.«es___2» → x ≠ idOf 733 → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tWork Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.tStats Q (nEnv bI) le m := by
  have hsb : S.sb = 0 := by simp [SLoc.sb, hso]
  have hva : ∀ (c : memory_chunk) (off : Int), 0 ≤ off → off + csize c ≤ 88 →
      ZArith.BinInt.Z.divide (Common.Memdata.align_chunk c) (zOfInt off) →
      Mem.valid_access m c S.bst (zOfInt (S.sb + off)) .Writable := fun c off h0 h1 hal => by
    rw [hsb, Int.zero_add]; exact va88 hR c off h0 h1 hal
  simp only [Nauty.tStats, Set.sk]
  -- the running frame: `hU : Unch m mk (· = S.bst)`, `hA : accesses kept`
  have hu : Unch m m (· = S.bst) := Unch.refl _ _
  have hA0 : ∀ c b o p, Mem.valid_access m c b o p → Mem.valid_access m c b o p := fun _ _ _ _ h => h
  wp_step; wp_step; wp_step
  refine Search.wp_statsStore (S := S) (ty := tdouble) (chunk := .Mfloat64) (off := 0) (w' := (.Vfloat (CompCert4Lean.Lib.Floats.Float.of_bits (lr 4607182418800017408)))) rfl Search.field_statsGrpsize1 rfl
    hst (by decide) (by rw [hsb]; decide)
    (hA0 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 0, rfl⟩))
    rfl rfl ?_
  intro m1 hs1
  have G1_0 := FieldAt.store_same hs1 (hA0 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 0, rfl⟩))
  have hU1 : Unch m m1 (· = S.bst) := (Unch.refl _ _).trans (Unch.store hs1 rfl)
  have hA1 : ∀ c b o p, Mem.valid_access m c b o p → Mem.valid_access m1 c b o p :=
    fun c b o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hs1 _ _ _ _ (hA0 c b o p h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine Search.wp_statsStore (S := S) (ty := tint) (chunk := .Mint32) (off := 8) (w' := (.Vint (ir 0))) rfl Search.field_statsGrpsize2 rfl
    (hst.unch (hu.trans hU1) (Ne.symm hsep.2.1)) (by decide) (by rw [hsb]; decide)
    (hA1 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 2, rfl⟩))
    rfl rfl ?_
  intro m2 hs2
  have G2_0 := G1_0.store_other hs2 (by rw [hsb]; decide)
  have G2_8 := FieldAt.store_same hs2 (hA1 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 2, rfl⟩))
  have hU2 : Unch m m2 (· = S.bst) := hU1.trans (Unch.store hs2 rfl)
  have hA2 : ∀ c b o p, Mem.valid_access m c b o p → Mem.valid_access m2 c b o p :=
    fun c b o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hs2 _ _ _ _ (hA1 c b o p h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine Search.wp_statsStore (S := S) (ty := tint) (chunk := .Mint32) (off := 16) (w' := (.Vint (ir 0))) rfl Search.fld_numgenerators rfl
    (hst.unch (hu.trans hU2) (Ne.symm hsep.2.1)) (by decide) (by rw [hsb]; decide)
    (hA2 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 4, rfl⟩))
    rfl rfl ?_
  intro m3 hs3
  have G3_0 := G2_0.store_other hs3 (by rw [hsb]; decide)
  have G3_8 := G2_8.store_other hs3 (by rw [hsb]; decide)
  have hU3 : Unch m m3 (· = S.bst) := hU2.trans (Unch.store hs3 rfl)
  have hA3 : ∀ c b o p, Mem.valid_access m c b o p → Mem.valid_access m3 c b o p :=
    fun c b o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hs3 _ _ _ _ (hA2 c b o p h)
  have F3_16 := (FieldAt.store_same hs3 (hA2 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 4, rfl⟩)))
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine Search.wp_statsStore (S := S) (ty := tulong) (chunk := .Mint64) (off := 24) (w' := (.Vlong (lr 0))) rfl Search.fld_numnodes rfl
    (hst.unch (hu.trans hU3) (Ne.symm hsep.2.1)) (by decide) (by rw [hsb]; decide)
    (hA3 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 3, rfl⟩))
    rfl rfl ?_
  intro m4 hs4
  have G4_0 := G3_0.store_other hs4 (by rw [hsb]; decide)
  have G4_8 := G3_8.store_other hs4 (by rw [hsb]; decide)
  have hU4 : Unch m m4 (· = S.bst) := hU3.trans (Unch.store hs4 rfl)
  have hA4 : ∀ c b o p, Mem.valid_access m c b o p → Mem.valid_access m4 c b o p :=
    fun c b o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hs4 _ _ _ _ (hA3 c b o p h)
  have F4_16 := (F3_16.store_other hs4 (by rw [hsb]; decide))
  have F4_24 := (FieldAt.store_same hs4 (hA3 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 3, rfl⟩)))
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine Search.wp_statsStore (S := S) (ty := tulong) (chunk := .Mint64) (off := 32) (w' := (.Vlong (lr 0))) rfl Search.fld_numbadleaves rfl
    (hst.unch (hu.trans hU4) (Ne.symm hsep.2.1)) (by decide) (by rw [hsb]; decide)
    (hA4 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 4, rfl⟩))
    rfl rfl ?_
  intro m5 hs5
  have G5_0 := G4_0.store_other hs5 (by rw [hsb]; decide)
  have G5_8 := G4_8.store_other hs5 (by rw [hsb]; decide)
  have hU5 : Unch m m5 (· = S.bst) := hU4.trans (Unch.store hs5 rfl)
  have hA5 : ∀ c b o p, Mem.valid_access m c b o p → Mem.valid_access m5 c b o p :=
    fun c b o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hs5 _ _ _ _ (hA4 c b o p h)
  have F5_16 := (F4_16.store_other hs5 (by rw [hsb]; decide))
  have F5_24 := (F4_24.store_other hs5 (by rw [hsb]; decide))
  have F5_32 := (FieldAt.store_same hs5 (hA4 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 4, rfl⟩)))
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine Search.wp_statsStore (S := S) (ty := tulong) (chunk := .Mint64) (off := 48) (w' := (.Vlong (lr 0))) rfl Search.fld_tctotal rfl
    (hst.unch (hu.trans hU5) (Ne.symm hsep.2.1)) (by decide) (by rw [hsb]; decide)
    (hA5 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 6, rfl⟩))
    rfl rfl ?_
  intro m6 hs6
  have G6_0 := G5_0.store_other hs6 (by rw [hsb]; decide)
  have G6_8 := G5_8.store_other hs6 (by rw [hsb]; decide)
  have hU6 : Unch m m6 (· = S.bst) := hU5.trans (Unch.store hs6 rfl)
  have hA6 : ∀ c b o p, Mem.valid_access m c b o p → Mem.valid_access m6 c b o p :=
    fun c b o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hs6 _ _ _ _ (hA5 c b o p h)
  have F6_16 := (F5_16.store_other hs6 (by rw [hsb]; decide))
  have F6_24 := (F5_24.store_other hs6 (by rw [hsb]; decide))
  have F6_32 := (F5_32.store_other hs6 (by rw [hsb]; decide))
  have F6_48 := (FieldAt.store_same hs6 (hA5 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 6, rfl⟩)))
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine Search.wp_statsStore (S := S) (ty := tulong) (chunk := .Mint64) (off := 56) (w' := (.Vlong (lr 0))) rfl Search.fld_canupdates rfl
    (hst.unch (hu.trans hU6) (Ne.symm hsep.2.1)) (by decide) (by rw [hsb]; decide)
    (hA6 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 7, rfl⟩))
    rfl rfl ?_
  intro m7 hs7
  have G7_0 := G6_0.store_other hs7 (by rw [hsb]; decide)
  have G7_8 := G6_8.store_other hs7 (by rw [hsb]; decide)
  have hU7 : Unch m m7 (· = S.bst) := hU6.trans (Unch.store hs7 rfl)
  have hA7 : ∀ c b o p, Mem.valid_access m c b o p → Mem.valid_access m7 c b o p :=
    fun c b o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hs7 _ _ _ _ (hA6 c b o p h)
  have F7_16 := (F6_16.store_other hs7 (by rw [hsb]; decide))
  have F7_24 := (F6_24.store_other hs7 (by rw [hsb]; decide))
  have F7_32 := (F6_32.store_other hs7 (by rw [hsb]; decide))
  have F7_48 := (F6_48.store_other hs7 (by rw [hsb]; decide))
  have F7_56 := (FieldAt.store_same hs7 (hA6 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 7, rfl⟩)))
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine Search.wp_statsStore (S := S) (ty := tint) (chunk := .Mint32) (off := 12) (w' := (.Vint (ir n))) rfl Search.fld_numorbits rfl
    (hst.unch (hu.trans hU7) (Ne.symm hsep.2.1)) (by decide) (by rw [hsb]; decide)
    (hA7 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 3, rfl⟩))
    (Search.eval_gint (e := nEnv bI) rfl Search.find_n (hN.unch (hu.trans hU7) (Ne.symm hsep.1))) rfl ?_
  intro m8 hs8
  have G8_0 := G7_0.store_other hs8 (by rw [hsb]; decide)
  have G8_8 := G7_8.store_other hs8 (by rw [hsb]; decide)
  have hU8 : Unch m m8 (· = S.bst) := hU7.trans (Unch.store hs8 rfl)
  have hA8 : ∀ c b o p, Mem.valid_access m c b o p → Mem.valid_access m8 c b o p :=
    fun c b o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hs8 _ _ _ _ (hA7 c b o p h)
  have F8_16 := (F7_16.store_other hs8 (by rw [hsb]; decide))
  have F8_24 := (F7_24.store_other hs8 (by rw [hsb]; decide))
  have F8_32 := (F7_32.store_other hs8 (by rw [hsb]; decide))
  have F8_48 := (F7_48.store_other hs8 (by rw [hsb]; decide))
  have F8_56 := (F7_56.store_other hs8 (by rw [hsb]; decide))
  have F8_12 := (FieldAt.store_same hs8 (hA7 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 3, rfl⟩)))
  simp only [seqPost, Post.after, E0_append]
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hsep
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hsepF
  have hF8 : Mem.load .Mint64 m8 Block.nautyFixedpts (zOfInt 0) = some (.Vptr bF Ptrofs.zero) := by
    rw [hU8.load _ _ _ (Ne.symm hb4)]; exact hF
  wp_step
  refine Set.wp_emptySetGE (by decide) rfl find_nautyFixedpts hF8 (Ne.symm hf2) (hfw.unch hU8 (Ne.symm hb5))
    hM0 hM (Search.eval_gint (e := nEnv bI) rfl Search.find_m (hMm.unch hU8 (Ne.symm hb3))) rfl ?_
  intro le9 m9 hfw9 hu9 _ _ hv9 ho9
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (v := .Vint (ir 1)) rfl Search.find_noncheaplevel rfl
    (hu9.access _ _ _ _ (Ne.symm hf3) (hA8 _ _ _ _ hwN)) rfl rfl rfl rfl ?_
  intro m10 hN10 hu10 hv10 ha10 _
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (ty := tint) (chunk := .Mint32) (v := .Vint (ir (-1))) rfl Search.find_eqlevCanon rfl
    (ha10 _ _ _ _ (hu9.access _ _ _ _ (Ne.symm hf4) (hA8 _ _ _ _ hwE))) rfl rfl rfl rfl ?_
  intro m11 hE11 hu11 hv11 ha11 _
  simp only [E0_append]
  have k : ∀ {c : memory_chunk} {off : Int} {v : val}, FieldAt m8 c S.bst off v → FieldAt m11 c S.bst off v :=
    fun h => ((h.unch hu9 hb5).unch hu10 hb6).unch hu11 hb7
  have hU : Unch m m11 (fun z => z = S.bst ∨ z = bF ∨ z = Search.Block.noncheaplevel ∨
      z = Search.Block.eqlevCanon) :=
    (((hU8.mono fun _ h => .inl h).trans (hu9.mono fun _ h => .inr (.inl h))).trans
      (hu10.mono fun _ h => .inr (.inr (.inl h)))).trans (hu11.mono fun _ h => .inr (.inr (.inr h)))
  refine hQ le9 m11 (k G8_0) (k G8_8) (k F8_12) (k F8_16) (k F8_24) (k F8_32)
    (ha11 _ _ _ _ (ha10 _ _ _ _ (hu9.access _ _ _ _ hb5
      (hA8 _ _ _ _ (hva _ _ (by decide) (by decide) ⟨zOfInt 10, rfl⟩)))))
    (k F8_48) (k F8_56) ((hfw9.unch hu10 hf3).unch hu11 hf4) (hN10.unch hu11 (by decide)) hE11 hU
    (fun z hz => hv11 _ (hv10 _ (hv9 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs8 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs7 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs6 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs5 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs4 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs3 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs2 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hs1 _ (hz)))))))))))) ho9


end NautyVerified.Proofs.Top

import NautyVerified.Proofs.Harness.Syntax

/-!
# The `options` global

`dense_main`'s `static DEFAULTOPTIONS_GRAPH(options)` starts as
`optionsInit` (`info_options`). `OptionsInit m`: the initial memory holds its
fields. Storing `getcanon = 1`, `defaultptn = 0`, `userautomproc =
emit_generator` and `outfile = &dummyfile` turns it into `OptionsAt`
(`OptionsInit.toAt`).
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (FieldAt)
open NautyVerified.Proofs.Init (info prog var_of_map var_init)

/-- `DEFAULTOPTIONS_GRAPH`'s initialiser, as CompCert lays it out. -/
def optionsInit : List init_data :=
  [.Init_int32 (ir 0), .Init_int32 (ir 0), .Init_int32 (ir 0), .Init_int32 (ir 0),
   .Init_int32 (ir 1), .Init_int32 (ir 0), .Init_int32 (ir 78), .Init_space (zOfInt 4),
   .Init_int64 (lr 0), .Init_int64 (lr 0), .Init_int64 (lr 0), .Init_int64 (lr 0),
   .Init_int64 (lr 0), .Init_int64 (lr 0), .Init_int64 (lr 0), .Init_int32 (ir 100),
   .Init_int32 (ir 0), .Init_int32 (ir 1), .Init_int32 (ir 0),
   .Init_addrof dense.id.dispatch_graph Ptrofs.zero, .Init_int32 (ir 0), .Init_space (zOfInt 4),
   .Init_int64 (lr 0)]

kernel_rfl info_options : info Block.options = some (optionsInit, false, false)

/-- The initial `options` fields (`DEFAULTOPTIONS_GRAPH`). -/
structure OptionsInit (m : mem) : Prop where
  perm : Mem.range_perm m Block.options (zOfInt 0) (zOfInt 128) .Cur .Writable
  getcanon : Mem.load .Mint32 m Block.options (zOfInt 0) = some (.Vint (ir 0))
  digraph : Mem.load .Mint32 m Block.options (zOfInt 4) = some (.Vint (ir 0))
  writeautoms : Mem.load .Mint32 m Block.options (zOfInt 8) = some (.Vint (ir 0))
  writemarkers : Mem.load .Mint32 m Block.options (zOfInt 12) = some (.Vint (ir 0))
  defaultptn : Mem.load .Mint32 m Block.options (zOfInt 16) = some (.Vint (ir 1))
  cartesian : Mem.load .Mint32 m Block.options (zOfInt 20) = some (.Vint (ir 0))
  linelength : Mem.load .Mint32 m Block.options (zOfInt 24) = some (.Vint (ir 78))
  outfile : Mem.load .Mint64 m Block.options (zOfInt 32) = some (.Vlong (lr 0))
  userrefproc : Mem.load .Mint64 m Block.options (zOfInt 40) = some (.Vlong (lr 0))
  userautomproc : Mem.load .Mint64 m Block.options (zOfInt 48) = some (.Vlong (lr 0))
  userlevelproc : Mem.load .Mint64 m Block.options (zOfInt 56) = some (.Vlong (lr 0))
  usernodeproc : Mem.load .Mint64 m Block.options (zOfInt 64) = some (.Vlong (lr 0))
  usercanonproc : Mem.load .Mint64 m Block.options (zOfInt 72) = some (.Vlong (lr 0))
  invarproc : Mem.load .Mint64 m Block.options (zOfInt 80) = some (.Vlong (lr 0))
  tcLevel : Mem.load .Mint32 m Block.options (zOfInt 88) = some (.Vint (ir 100))
  mininvarlevel : Mem.load .Mint32 m Block.options (zOfInt 92) = some (.Vint (ir 0))
  maxinvarlevel : Mem.load .Mint32 m Block.options (zOfInt 96) = some (.Vint (ir 1))
  invararg : Mem.load .Mint32 m Block.options (zOfInt 100) = some (.Vint (ir 0))
  dispatch : Mem.load .Mint64 m Block.options (zOfInt 104) =
    some (.Vptr Block.dispatchGraph Ptrofs.zero)
  schreier : Mem.load .Mint32 m Block.options (zOfInt 112) = some (.Vint (ir 0))
  extraOptions : Mem.load .Mint64 m Block.options (zOfInt 120) = some (.Vlong (lr 0))

theorem optionsInit_of {m : mem} (hm : Genv.init_mem prog = some m) : OptionsInit m := by
  obtain ⟨v, hv, hi, hro, hvol⟩ := var_of_map info_options
  have h := var_init hm hv hvol
  have hp : Genv.perm_globvar v = .Writable := by
    unfold Genv.perm_globvar; rw [hro, hvol]; rfl
  rw [hp, hi] at h
  obtain ⟨hperm, h⟩ := h
  simp only [optionsInit, Genv.load_store_init_data] at h
  obtain ⟨h0, h4, h8, h12, h16, h20, h24, -, h32, h40, h48, h56, h64, h72, h80, h88, h92, h96, h100,
    ⟨bd, hbd, h104⟩, h112, -, h120, -⟩ := h
  rw [find_dispatchGraph] at hbd
  cases hbd
  exact ⟨hperm, h0, h4, h8, h12, h16, h20, h24, h32, h40, h48, h56, h64, h72, h80, h88, h92, h96,
    h100, h104, h112, h120⟩

/-- A load at an offset disjoint from a store is unchanged. -/
theorem load_store_far {m m' : mem} {c c' : memory_chunk} {b : block} {ofs ofs' : Int} {v : val}
    (h : Mem.store c m b (zOfInt ofs) v = some m')
    (hd : ofs' + csize c' ≤ ofs ∨ ofs + csize c ≤ ofs') :
    Mem.load c' m' b (zOfInt ofs') = Mem.load c' m b (zOfInt ofs') := by
  apply Mem.load_store_other _ _ _ _ _ _ h _ _ _ (.inr ?_)
  rcases hd with hd | hd
  · left
    change ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ _) _
    simp only [Z_le_iff, intOfZ_add, intOfZ_zOfInt]
    simpa [csize] using hd
  · right
    change ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ _) _
    simp only [Z_le_iff, intOfZ_add, intOfZ_zOfInt]
    simpa [csize] using hd

/-- A writable aligned field of `options`. -/
theorem OptionsInit.access {m : mem} (h : OptionsInit m) (c : memory_chunk) (ofs : Int)
    (h0 : 0 ≤ ofs) (h1 : ofs + csize c ≤ 128) (ha : ZArith.BinInt.Z.divide (CompCert4Lean.Common.Memdata.align_chunk c) (zOfInt ofs)) :
    Mem.valid_access m c Block.options (zOfInt ofs) .Writable := by
  refine ⟨fun o ho => h.perm o ?_, ha⟩
  have := csize_pos c
  obtain ⟨ho1, ho2⟩ := ho
  change ZArith.BinInt.Z.le _ _ at ho1
  change ZArith.BinInt.Z.lt _ (ZArith.BinInt.Z.add _ _) at ho2
  simp only [Z_le_iff, Z_lt_iff, intOfZ_add, intOfZ_zOfInt] at ho1 ho2
  constructor
  · change ZArith.BinInt.Z.le _ _
    simp only [Z_le_iff, intOfZ_zOfInt]; omega
  · change ZArith.BinInt.Z.lt _ _
    simp only [Z_lt_iff, intOfZ_zOfInt]; simp only [csize] at h1 this; omega

theorem csize_Mint32 : csize .Mint32 = 4 := rfl
theorem csize_Mint64 : csize .Mint64 = 8 := rfl

/-- `main`'s four stores turn the initial `options` into `OptionsAt`. -/
theorem OptionsInit.toAt {m₀ m m₁ m₂ m₃ m₄ : mem} {S : block → Prop} (h : OptionsInit m₀)
    (hu : Unch m₀ m S) (hS : ¬ S Block.options)
    (h1 : Mem.store .Mint32 m Block.options (zOfInt 0) (.Vint (ir 1)) = some m₁)
    (h2 : Mem.store .Mint32 m₁ Block.options (zOfInt 16) (.Vint (ir 0)) = some m₂)
    (h3 : Mem.store .Mint64 m₂ Block.options (zOfInt 48) (.Vptr Block.emitGenerator Ptrofs.zero) =
      some m₃)
    (h4 : Mem.store .Mint64 m₃ Block.options (zOfInt 32) (.Vptr Block.dummyfile Ptrofs.zero) =
      some m₄) :
    OptionsAt m₄ :=
  have acc4 : ∀ {c ofs}, Mem.valid_access m₀ c Block.options ofs .Writable →
      Mem.valid_access m₄ c Block.options ofs .Writable := fun hv =>
    Mem.store_valid_access_1 _ _ _ _ _ _ h4 _ _ _ _ (Mem.store_valid_access_1 _ _ _ _ _ _ h3 _ _ _ _
      (Mem.store_valid_access_1 _ _ _ _ _ _ h2 _ _ _ _ (Mem.store_valid_access_1 _ _ _ _ _ _ h1 _ _ _ _
        (hu.access _ _ _ _ hS hv))))
  {
    getcanon := ⟨by rw [load_store_far h4 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h3 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h2 (.inl (by simp only [csize_Mint32]; omega)), Mem.load_store_same _ _ _ _ _ _ h1]; rfl, acc4 (h.access .Mint32 0 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 0, rfl⟩)⟩
    digraph := ⟨by rw [load_store_far h4 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h3 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h2 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.digraph, acc4 (h.access .Mint32 4 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 1, rfl⟩)⟩
    writeautoms := ⟨by rw [load_store_far h4 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h3 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h2 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.writeautoms, acc4 (h.access .Mint32 8 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 2, rfl⟩)⟩
    writemarkers := ⟨by rw [load_store_far h4 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h3 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h2 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.writemarkers, acc4 (h.access .Mint32 12 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 3, rfl⟩)⟩
    defaultptn := ⟨by rw [load_store_far h4 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h3 (.inl (by simp only [csize_Mint32]; omega)), Mem.load_store_same _ _ _ _ _ _ h2]; rfl, acc4 (h.access .Mint32 16 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 4, rfl⟩)⟩
    cartesian := ⟨by rw [load_store_far h4 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h3 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.cartesian, acc4 (h.access .Mint32 20 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 5, rfl⟩)⟩
    linelength := ⟨by rw [load_store_far h4 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h3 (.inl (by simp only [csize_Mint32]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.linelength, acc4 (h.access .Mint32 24 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 6, rfl⟩)⟩
    outfile := ⟨by rw [Mem.load_store_same _ _ _ _ _ _ h4]; rfl, acc4 (h.access .Mint64 32 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 4, rfl⟩)⟩
    userrefproc := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inl (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.userrefproc, acc4 (h.access .Mint64 40 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 5, rfl⟩)⟩
    userautomproc := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), Mem.load_store_same _ _ _ _ _ _ h3]; rfl, acc4 (h.access .Mint64 48 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 6, rfl⟩)⟩
    userlevelproc := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.userlevelproc, acc4 (h.access .Mint64 56 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 7, rfl⟩)⟩
    usernodeproc := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.usernodeproc, acc4 (h.access .Mint64 64 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 8, rfl⟩)⟩
    usercanonproc := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.usercanonproc, acc4 (h.access .Mint64 72 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 9, rfl⟩)⟩
    invarproc := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.invarproc, acc4 (h.access .Mint64 80 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 10, rfl⟩)⟩
    tcLevel := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.tcLevel, acc4 (h.access .Mint32 88 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 22, rfl⟩)⟩
    mininvarlevel := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.mininvarlevel, acc4 (h.access .Mint32 92 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 23, rfl⟩)⟩
    maxinvarlevel := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.maxinvarlevel, acc4 (h.access .Mint32 96 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 24, rfl⟩)⟩
    invararg := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.invararg, acc4 (h.access .Mint32 100 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 25, rfl⟩)⟩
    dispatch := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.dispatch, acc4 (h.access .Mint64 104 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 13, rfl⟩)⟩
    schreier := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.schreier, acc4 (h.access .Mint32 112 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 28, rfl⟩)⟩
    extraOptions := ⟨by rw [load_store_far h4 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h3 (.inr (by simp only [csize_Mint64]; omega)), load_store_far h2 (.inr (by simp only [csize_Mint32]; omega)), load_store_far h1 (.inr (by simp only [csize_Mint32]; omega)), hu.load _ _ _ hS]; exact h.extraOptions, acc4 (h.access .Mint64 120 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 15, rfl⟩)⟩ }

end NautyVerified.Proofs.Harness

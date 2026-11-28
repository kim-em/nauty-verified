import NautyVerified.Proofs.Alloc.Dyn
import NautyVerified.Proofs.Set.Add
import NautyVerified.Proofs.Nextelement.Leftbit
import NautyVerified.Proofs.Alloc.Blocks
import HexGraphIso.Nauty.Search.Bits

/-!
# What the initial memory holds

The initial memory `m` of the linked dense program (`Genv.init_mem prog = some m`,
the memory Clight's `initial_state` starts from) holds each global's
initialiser. `var_init` is CompCert's `init_mem_characterization` for one
global; `loads64`/`loads32` read an initialiser list of 64- and 32-bit
integers back as loads. Each global's initialiser is pinned by the kernel
(`kernel_rfl`), one global at a time, so the whole initial memory is never
evaluated.
-/

namespace NautyVerified.Proofs.Init

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.AST CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs

/-- The linked dense program, as the memory model sees it. -/
abbrev prog := Cfrontend.Ctypes.program_of_program Source.dense.locals

kernel_rfl ge_eq : ge.genv_genv = Genv.globalenv prog

/-- The facts `init_mem` gives about a non-volatile global. -/
theorem var_init {m : mem} (hm : Genv.init_mem prog = some m) {b : block}
    {v : globvar Cfrontend.Ctypes.type} (hv : Genv.find_var_info ge.genv_genv b = some v)
    (hvol : v.gvar_volatile = false) :
    Mem.range_perm m b .Z0 (init_data_list_size v.gvar_init) .Cur (Genv.perm_globvar v) ∧
      Genv.load_store_init_data ge.genv_genv m b .Z0 v.gvar_init := by
  rw [ge_eq] at hv ⊢
  have h := Genv.init_mem_characterization _ _ prog b v m hv hm
  exact ⟨h.1, h.2.2.1 hvol⟩

/-- A global's initialiser, read off a kernel-checked equation. -/
theorem var_of_map {b : block} {x : List init_data × Bool × Bool}
    (h : (Genv.find_var_info ge.genv_genv b).map
      (fun v => (v.gvar_init, v.gvar_readonly, v.gvar_volatile)) = some x) :
    ∃ v, Genv.find_var_info ge.genv_genv b = some v ∧ v.gvar_init = x.1 ∧
      v.gvar_readonly = x.2.1 ∧ v.gvar_volatile = x.2.2 := by
  cases hf : Genv.find_var_info ge.genv_genv b with
  | none => rw [hf] at h; cases h
  | some v =>
    rw [hf] at h
    cases h
    exact ⟨v, rfl, rfl, rfl, rfl⟩

theorem zadd_ofs (q : Int) (k : Nat) (hk : intOfZ (ZArith.BinInt.Z.of_nat k) = k) :
    ZArith.BinInt.Z.add (zOfInt q) (ZArith.BinInt.Z.of_nat k) = zOfInt (q + k) := by
  apply intOfZ_injective
  rw [intOfZ_add, intOfZ_zOfInt, intOfZ_zOfInt, hk]

/-- Reading back an initialiser of 64-bit integers. -/
theorem loads64 {m : mem} {b : block} :
    ∀ (ws : List int64) (q : Int),
      Genv.load_store_init_data ge.genv_genv m b (zOfInt q) (ws.map .Init_int64) →
      ∀ i (hi : i < ws.length), Mem.load .Mint64 m b (zOfInt (q + 8 * i)) = some (.Vlong ws[i])
  | [], _, _, _, hi => absurd hi (by simp)
  | w :: ws, q, h, i, hi => by
    obtain ⟨h0, hr⟩ := h
    cases i with
    | zero => simpa using h0
    | succ i =>
      have hr' : Genv.load_store_init_data ge.genv_genv m b (zOfInt (q + 8)) (ws.map .Init_int64) := by
        rw [show q + 8 = q + ((8 : Nat) : Int) from rfl, ← zadd_ofs q 8 rfl]; exact hr
      have := loads64 ws (q + 8) hr' i (by simpa using hi)
      rw [show q + 8 * ((i + 1 : Nat) : Int) = q + 8 + 8 * i by push_cast; omega]
      simpa using this

/-- Reading back an initialiser of 32-bit integers. -/
theorem loads32 {m : mem} {b : block} :
    ∀ (ws : List Lib.Integers.int) (q : Int),
      Genv.load_store_init_data ge.genv_genv m b (zOfInt q) (ws.map .Init_int32) →
      ∀ i (hi : i < ws.length), Mem.load .Mint32 m b (zOfInt (q + 4 * i)) = some (.Vint ws[i])
  | [], _, _, _, hi => absurd hi (by simp)
  | w :: ws, q, h, i, hi => by
    obtain ⟨h0, hr⟩ := h
    cases i with
    | zero => simpa using h0
    | succ i =>
      have hr' : Genv.load_store_init_data ge.genv_genv m b (zOfInt (q + 4)) (ws.map .Init_int32) := by
        rw [show q + 4 = q + ((4 : Nat) : Int) from rfl, ← zadd_ofs q 4 rfl]; exact hr
      have := loads32 ws (q + 4) hr' i (by simpa using hi)
      rw [show q + 4 * ((i + 1 : Nat) : Int) = q + 4 + 4 * i by push_cast; omega]
      simpa using this

/-- The global's initialiser, permission and volatility, as `kernel_rfl` pins them. -/
abbrev info (b : block) : Option (List init_data × Bool × Bool) :=
  (Genv.find_var_info ge.genv_genv b).map
    (fun v => (v.gvar_init, v.gvar_readonly, v.gvar_volatile))

theorem z0_eq : (ZArith.BinInt.Z.Z0 : Z) = zOfInt 0 := rfl

/-- A global initialised with the 64-bit words `ws` holds them. -/
theorem table64 {m : mem} (hm : Genv.init_mem prog = some m) {b : block} {ws : List int64}
    {ro : Bool} (h : info b = some (ws.map .Init_int64, ro, false)) :
    ∀ i (hi : i < ws.length), Mem.load .Mint64 m b (zOfInt (8 * i)) = some (.Vlong ws[i]) := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_map h
  have h2 := (var_init hm hv hvol).2
  rw [hi] at h2
  change Genv.load_store_init_data _ m b (zOfInt 0) (ws.map .Init_int64) at h2
  intro i hi
  simpa using loads64 ws 0 h2 i hi

/-- A global initialised with the 32-bit words `ws` holds them. -/
theorem table32 {m : mem} (hm : Genv.init_mem prog = some m) {b : block}
    {ws : List Lib.Integers.int} {ro : Bool} (h : info b = some (ws.map .Init_int32, ro, false)) :
    ∀ i (hi : i < ws.length), Mem.load .Mint32 m b (zOfInt (4 * i)) = some (.Vint ws[i]) := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_map h
  have h2 := (var_init hm hv hvol).2
  rw [hi] at h2
  change Genv.load_store_init_data _ m b (zOfInt 0) (ws.map .Init_int32) at h2
  intro i hi
  simpa using loads32 ws 0 h2 i hi

/-! ## The bit tables -/

/-- The initialiser of every copy of nauty's `bit[64]`. -/
def bitWords : List int64 := (List.range 64).map fun i => lr ((2 ^ (63 - i) : Nat) : Int)

theorem bitTable {m : mem} (hm : Genv.init_mem prog = some m) {b : block}
    (h : info b = some (bitWords.map .Init_int64, true, false)) : Set.BitTable m b := by
  intro i hi
  have := table64 hm h i (by simpa [bitWords] using hi)
  simp only [bitWords, List.getElem_map, List.getElem_range] at this
  simp only [elemOfs, Int.zero_add, show csize .Mint64 = 8 from rfl]
  exact this

kernel_rfl info_nautilBit : info Block.nautilBit = some (bitWords.map .Init_int64, true, false)
kernel_rfl info_naugraphBit : info Block.naugraphBit = some (bitWords.map .Init_int64, true, false)
kernel_rfl info_nautyBit : info Block.nautyBit = some (bitWords.map .Init_int64, true, false)
kernel_rfl info_denseMainBit : info Block.denseMainBit = some (bitWords.map .Init_int64, true, false)

/-! ## `leftbit` and `bytecount` -/

def leftbitWords : List Lib.Integers.int :=
  (List.range 256).map fun i => Lib.Integers.Int.repr (zOfInt (Nextelement.lbv i))

kernel_rfl info_leftbit : info Block.leftbit = some (leftbitWords.map .Init_int32, true, false)

theorem leftbitTable {m : mem} (hm : Genv.init_mem prog = some m) :
    Nextelement.LeftbitTable m := by
  intro i hi
  have := table32 hm info_leftbit i (by simpa [leftbitWords] using hi)
  simpa [leftbitWords] using this

/-- naugraph.c's `bytecount` table, as it is in memory `m`: entry `i` is the
number of set bits of the byte `i`. -/
def BytecountTable (m : mem) : Prop :=
  ∀ i : Nat, i < 256 → Mem.load .Mint32 m Block.naugraphBytecount (zOfInt (4 * (i : Int))) =
    some (.Vint (ir (Hex.GraphIso.Nauty.popCount i)))

def bytecountWords : List Lib.Integers.int :=
  (List.range 256).map fun i => ir (Hex.GraphIso.Nauty.popCount i)

kernel_rfl info_bytecount :
  info Block.naugraphBytecount = some (bytecountWords.map .Init_int32, true, false)

theorem bytecountTable {m : mem} (hm : Genv.init_mem prog = some m) : BytecountTable m := by
  intro i hi
  have := table32 hm info_bytecount i (by simpa [bytecountWords] using hi)
  simpa [bytecountWords] using this

/-! ## `DYNALLSTAT` pairs start empty -/

/-- A writable non-volatile global of 8 bytes allows 64-bit stores at offset 0. -/
theorem writable8 {m : mem} (hm : Genv.init_mem prog = some m) {b : block} {l : List init_data}
    (h : info b = some (l, false, false)) (hl : init_data_list_size l = zOfInt 8) :
    Mem.valid_access m .Mint64 b (zOfInt 0) .Writable := by
  obtain ⟨v, hv, hi, hro, hvol⟩ := var_of_map h
  have h1 := (var_init hm hv hvol).1
  have hp : Genv.perm_globvar v = .Writable := by
    unfold Genv.perm_globvar; rw [hro, hvol]; rfl
  rw [hp, hi, hl] at h1
  exact ⟨h1, ⟨zOfInt 0, rfl⟩⟩

/-- A non-volatile global initialised as 8 bytes of space reads as `NULL`. -/
theorem space8 {m : mem} (hm : Genv.init_mem prog = some m) {b : block} {ro : Bool}
    (h : info b = some ([.Init_space (zOfInt 8)], ro, false)) :
    Mem.load .Mint64 m b (zOfInt 0) = some Vnullptr := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_map h
  have h2 := (var_init hm hv hvol).2
  rw [hi] at h2
  exact h2.1 .Mint64 (zOfInt 0) (by decide) (by decide) ⟨zOfInt 0, rfl⟩

/-- Before the first `DYNALLOC1`, a `DYNALLSTAT` pair has capacity 0 (its
`_sz` global is initialised to 0 and its pointer global is 8 bytes of
space), so `DynAt` holds for any block. -/
theorem dynAt_zero {m : mem} (hm : Genv.init_mem prog = some m) {bp bs : block} (c : Nat)
    (b : block) (hne : bs ≠ bp)
    (hs : info bs = some ([.Init_int64 (lr 0)], false, false))
    (hp : info bp = some ([.Init_space (zOfInt 8)], false, false)) :
    Alloc.DynAt m bp bs c 0 b where
  capLd := by
    have := table64 hm (ws := [lr 0]) hs 0 (by decide)
    simpa using this
  bsW := writable8 hm hs rfl
  bpW := writable8 hm hp rfl
  ptr := fun h => absurd h (Nat.lt_irrefl 0)
  mal := fun h => absurd h (Nat.lt_irrefl 0)
  ne := hne
  bne := fun h => absurd h (Nat.lt_irrefl 0)
  small := by simp
  capLt := by decide
  null := fun _ => space8 hm hp


kernel_rfl info_nautilWorkpermSz : info Block.nautilWorkpermSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautilWorkperm : info Block.nautilWorkperm = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautilWorkperm {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautilWorkperm Block.nautilWorkpermSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautilWorkpermSz info_nautilWorkperm

kernel_rfl info_naugraphWorkpermSz : info Block.naugraphWorkpermSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_naugraphWorkperm : info Block.naugraphWorkperm = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_naugraphWorkperm {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz c 0 b :=
  dynAt_zero hm c b (by decide) info_naugraphWorkpermSz info_naugraphWorkperm

kernel_rfl info_naugraphWorksetSz : info Block.naugraphWorksetSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_naugraphWorkset : info Block.naugraphWorkset = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_naugraphWorkset {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.naugraphWorkset Block.naugraphWorksetSz c 0 b :=
  dynAt_zero hm c b (by decide) info_naugraphWorksetSz info_naugraphWorkset

kernel_rfl info_naugraphBucketSz : info Block.naugraphBucketSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_naugraphBucket : info Block.naugraphBucket = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_naugraphBucket {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.naugraphBucket Block.naugraphBucketSz c 0 b :=
  dynAt_zero hm c b (by decide) info_naugraphBucketSz info_naugraphBucket

kernel_rfl info_naugraphDnworkSz : info Block.naugraphDnworkSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_naugraphDnwork : info Block.naugraphDnwork = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_naugraphDnwork {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.naugraphDnwork Block.naugraphDnworkSz c 0 b :=
  dynAt_zero hm c b (by decide) info_naugraphDnworkSz info_naugraphDnwork

kernel_rfl info_nautyCanonlabSz : info Block.nautyCanonlabSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautyCanonlab : info Block.nautyCanonlab = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautyCanonlab {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautyCanonlab Block.nautyCanonlabSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautyCanonlabSz info_nautyCanonlab

kernel_rfl info_nautyDefltworkSz : info Block.nautyDefltworkSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautyDefltwork : info Block.nautyDefltwork = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautyDefltwork {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautyDefltwork Block.nautyDefltworkSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautyDefltworkSz info_nautyDefltwork

kernel_rfl info_nautyActiveSz : info Block.nautyActiveSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautyActive : info Block.nautyActive = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautyActive {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautyActive Block.nautyActiveSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautyActiveSz info_nautyActive

kernel_rfl info_nautyCanoncodeSz : info Block.nautyCanoncodeSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautyCanoncode : info Block.nautyCanoncode = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautyCanoncode {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautyCanoncode Block.nautyCanoncodeSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautyCanoncodeSz info_nautyCanoncode

kernel_rfl info_nautyFixedptsSz : info Block.nautyFixedptsSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautyFixedpts : info Block.nautyFixedpts = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautyFixedpts {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautyFixedpts Block.nautyFixedptsSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautyFixedptsSz info_nautyFixedpts

kernel_rfl info_nautyFirstcodeSz : info Block.nautyFirstcodeSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautyFirstcode : info Block.nautyFirstcode = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautyFirstcode {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautyFirstcode Block.nautyFirstcodeSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautyFirstcodeSz info_nautyFirstcode

kernel_rfl info_nautyWorkpermSz : info Block.nautyWorkpermSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautyWorkperm : info Block.nautyWorkperm = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautyWorkperm {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautyWorkperm Block.nautyWorkpermSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautyWorkpermSz info_nautyWorkperm

kernel_rfl info_nautyFirsttcSz : info Block.nautyFirsttcSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautyFirsttc : info Block.nautyFirsttc = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautyFirsttc {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautyFirsttc Block.nautyFirsttcSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautyFirsttcSz info_nautyFirsttc

kernel_rfl info_nautyFirstlabSz : info Block.nautyFirstlabSz = some ([.Init_int64 (lr 0)], false, false)
kernel_rfl info_nautyFirstlab : info Block.nautyFirstlab = some ([.Init_space (zOfInt 8)], false, false)
theorem dynAt_nautyFirstlab {m : mem} (hm : Genv.init_mem prog = some m) (c : Nat) (b : block) :
    Alloc.DynAt m Block.nautyFirstlab Block.nautyFirstlabSz c 0 b :=
  dynAt_zero hm c b (by decide) info_nautyFirstlabSz info_nautyFirstlab

/-! ## Validity and the whole bundle -/

/-- Every global's block is valid in the initial memory. -/
theorem valid_global {m : mem} (hm : Genv.init_mem prog = some m) {id : ident} {b : block}
    (h : Genv.find_symbol ge.genv_genv id = some b) : Mem.valid_block m b := by
  rw [ge_eq] at h
  exact Genv.find_symbol_not_fresh _ _ prog id b m hm h

/-- What the initial memory provides for the globals the dense specifications
read: the bit tables, `leftbit`, `bytecount`, and every `DYNALLSTAT` pair
empty. -/
structure Globals (m : mem) : Prop where
  nautilBit : Set.BitTable m Block.nautilBit
  naugraphBit : Set.BitTable m Block.naugraphBit
  nautyBit : Set.BitTable m Block.nautyBit
  denseMainBit : Set.BitTable m Block.denseMainBit
  leftbit : Nextelement.LeftbitTable m
  bytecount : BytecountTable m
  nautilWorkperm : ∀ c b, Alloc.DynAt m Block.nautilWorkperm Block.nautilWorkpermSz c 0 b
  naugraphWorkperm : ∀ c b, Alloc.DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz c 0 b
  naugraphWorkset : ∀ c b, Alloc.DynAt m Block.naugraphWorkset Block.naugraphWorksetSz c 0 b
  naugraphBucket : ∀ c b, Alloc.DynAt m Block.naugraphBucket Block.naugraphBucketSz c 0 b
  naugraphDnwork : ∀ c b, Alloc.DynAt m Block.naugraphDnwork Block.naugraphDnworkSz c 0 b
  nautyCanonlab : ∀ c b, Alloc.DynAt m Block.nautyCanonlab Block.nautyCanonlabSz c 0 b
  nautyDefltwork : ∀ c b, Alloc.DynAt m Block.nautyDefltwork Block.nautyDefltworkSz c 0 b
  nautyActive : ∀ c b, Alloc.DynAt m Block.nautyActive Block.nautyActiveSz c 0 b
  nautyCanoncode : ∀ c b, Alloc.DynAt m Block.nautyCanoncode Block.nautyCanoncodeSz c 0 b
  nautyFixedpts : ∀ c b, Alloc.DynAt m Block.nautyFixedpts Block.nautyFixedptsSz c 0 b
  nautyFirstcode : ∀ c b, Alloc.DynAt m Block.nautyFirstcode Block.nautyFirstcodeSz c 0 b
  nautyWorkperm : ∀ c b, Alloc.DynAt m Block.nautyWorkperm Block.nautyWorkpermSz c 0 b
  nautyFirsttc : ∀ c b, Alloc.DynAt m Block.nautyFirsttc Block.nautyFirsttcSz c 0 b
  nautyFirstlab : ∀ c b, Alloc.DynAt m Block.nautyFirstlab Block.nautyFirstlabSz c 0 b

theorem globals {m : mem} (hm : Genv.init_mem prog = some m) : Globals m where
  nautilBit := bitTable hm info_nautilBit
  naugraphBit := bitTable hm info_naugraphBit
  nautyBit := bitTable hm info_nautyBit
  denseMainBit := bitTable hm info_denseMainBit
  leftbit := leftbitTable hm
  bytecount := bytecountTable hm
  nautilWorkperm := dynAt_nautilWorkperm hm
  naugraphWorkperm := dynAt_naugraphWorkperm hm
  naugraphWorkset := dynAt_naugraphWorkset hm
  naugraphBucket := dynAt_naugraphBucket hm
  naugraphDnwork := dynAt_naugraphDnwork hm
  nautyCanonlab := dynAt_nautyCanonlab hm
  nautyDefltwork := dynAt_nautyDefltwork hm
  nautyActive := dynAt_nautyActive hm
  nautyCanoncode := dynAt_nautyCanoncode hm
  nautyFixedpts := dynAt_nautyFixedpts hm
  nautyFirstcode := dynAt_nautyFirstcode hm
  nautyWorkperm := dynAt_nautyWorkperm hm
  nautyFirsttc := dynAt_nautyFirsttc hm
  nautyFirstlab := dynAt_nautyFirstlab hm

end NautyVerified.Proofs.Init

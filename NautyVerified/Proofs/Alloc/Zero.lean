import NautyVerified.Proofs.Alloc.Zalloc

/-!
# Zero-filled blocks as arrays

`zero_array`: the first `n` elements of a block whose bytes are all zero and
`Freeable` form an array of zeros, for `int` (`Mint32`) and `long`
(`Mint64`) elements.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word

theorem loadbytes_sub {m : mem} {b : block} {N : Nat}
    (h : Mem.loadbytes m b (zOfInt 0) (zOfInt N) = some (List.replicate N zb)) (o len : Nat)
    (hle : o + len ≤ N) :
    Mem.loadbytes m b (zOfInt o) (zOfInt len) = some (List.replicate len zb) := by
  have hN : zOfInt N = ZArith.BinInt.Z.add (zOfInt o) (zOfInt (N - o : Nat)) := by
    apply intOfZ_injective; simp [intOfZ_zOfInt]; omega
  rw [hN] at h
  obtain ⟨b1, b2, h1, h2, he⟩ := Mem.loadbytes_split _ _ _ _ _ _ h
    (by change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt]) (by change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt])
  have hl1 := Mem.loadbytes_length _ _ _ _ _ h1
  have ho : ZArith.BinInt.Z.add (zOfInt 0) (zOfInt o) = zOfInt o := by
    apply intOfZ_injective; simp [intOfZ_zOfInt]
  replace h2 : Mem.loadbytes m b (zOfInt o) (zOfInt (N - o : Nat)) = some b2 := by
    rw [← ho]; exact h2
  have hNo : zOfInt (N - o : Nat) = ZArith.BinInt.Z.add (zOfInt len) (zOfInt (N - o - len : Nat)) := by
    apply intOfZ_injective; simp [intOfZ_zOfInt]; omega
  rw [hNo] at h2
  obtain ⟨c1, c2, h3, h4, he2⟩ := Mem.loadbytes_split _ _ _ _ _ _ h2
    (by change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt]) (by change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt])
  have hl3 := Mem.loadbytes_length _ _ _ _ _ h3
  rw [h3]
  congr 1
  have hzl1 : ZArith.BinInt.Z.to_nat (zOfInt o) = o := by simp [ZArith.BinInt.Z.to_nat, intOfZ_zOfInt]
  have hzl3 : ZArith.BinInt.Z.to_nat (zOfInt len) = len := by simp [ZArith.BinInt.Z.to_nat, intOfZ_zOfInt]
  replace hl1 : b1.length = o := hl1.trans hzl1
  replace hl3 : c1.length = len := hl3.trans hzl3
  apply List.eq_replicate_iff.2
  refine ⟨hl3, fun x hx => ?_⟩
  have : x ∈ List.replicate N zb := by
    rw [he, he2]; simp [hx]
  exact (List.mem_replicate.1 this).2

/-- Every aligned element of the first `N` bytes of `b` loads as zero bytes. Unlike
`Mem.loadbytes`, this survives `Unch` for any set not containing `b`. -/
def Zeros (m : mem) (b : block) (N : Nat) : Prop :=
  ∀ chunk (c : Nat), csize chunk = c → intOfZ (align_chunk chunk) = c → ∀ i : Nat, c * i + c ≤ N →
    Mem.load chunk m b (elemOfs chunk 0 i) = some (decode_val chunk (List.replicate c zb))

theorem Zeros.unch {m m' : mem} {b : block} {N : Nat} (h : Zeros m b N) {S : block → Prop}
    (hu : Unch m m' S) (hb : ¬ S b) : Zeros m' b N :=
  fun chunk c hc ha i hi => by rw [hu.load _ _ _ hb]; exact h chunk c hc ha i hi

theorem Zeros.mono {m : mem} {b : block} {N N' : Nat} (h : Zeros m b N) (hle : N' ≤ N) :
    Zeros m b N' :=
  fun chunk c hc ha i hi => h chunk c hc ha i (by omega)

theorem Zeros.of_bytes {m : mem} {b : block} {N : Nat}
    (hz : Mem.loadbytes m b (zOfInt 0) (zOfInt N) = some (List.replicate N zb)) : Zeros m b N := by
  intro chunk c hc ha i hi
  have hofs : elemOfs chunk 0 i = zOfInt ((c * i : Nat) : Int) := by
    simp only [elemOfs, hc]; congr 1; push_cast; omega
  have halign : ZArith.BinInt.Z.divide (align_chunk chunk) (zOfInt ((c * i : Nat) : Int)) :=
    ⟨zOfInt i, by
      apply intOfZ_injective
      simp only [intOfZ_mul, intOfZ_zOfInt, ha]; push_cast; rw [Int.mul_comm]⟩
  rw [hofs]
  have hsub := loadbytes_sub hz (c * i) c hi
  have hsc : zOfInt (c : Int) = size_chunk chunk := by
    apply intOfZ_injective; rw [intOfZ_zOfInt]; exact hc.symm
  rw [hsc] at hsub
  rw [Mem.loadbytes_load _ _ _ _ _ hsub halign]

/-- The first `n` elements of a zero-filled `Freeable` block, as an array of
the value `v` that zero bytes decode to. -/
theorem Zeros.array {m : mem} {b : block} {N : Nat} (hz : Zeros m b N)
    (hperm : ∀ ofs : Int, 0 ≤ ofs → ofs < N → Mem.perm m b (zOfInt ofs) .Cur .Freeable)
    (hN : N < 2 ^ 62) (chunk : memory_chunk) (c : Nat) (hc : csize chunk = c)
    (ha : intOfZ (align_chunk chunk) = c) (v : val)
    (hv : decode_val chunk (List.replicate c zb) = v) (n : Nat) (hn : c * n ≤ N) :
    ArrayAt m chunk b 0 (fun _ => v) n := by
  have hcpos := csize_pos chunk
  have hle : ∀ i, i < n → c * i + c ≤ N := fun i hi => by
    have := Nat.mul_le_mul_left c (show i + 1 ≤ n by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  have hofs : ∀ i : Nat, elemOfs chunk 0 i = zOfInt ((c * i : Nat) : Int) := fun i => by
    simp only [elemOfs, hc]; congr 1; push_cast; omega
  have halign : ∀ i : Nat, ZArith.BinInt.Z.divide (align_chunk chunk) (zOfInt ((c * i : Nat) : Int)) :=
    fun i => ⟨zOfInt i, by
      apply intOfZ_injective
      simp only [intOfZ_mul, intOfZ_zOfInt, ha]; push_cast; rw [Int.mul_comm]⟩
  refine ⟨Int.le_refl _, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hc]
    have : c * n < 2 ^ 64 := by omega
    have : ((c * n : Nat) : Int) = (c : Int) * n := by push_cast; rfl
    omega
  · rw [hz chunk c hc ha i (hle i hi), hv]
  · rw [hofs]
    refine ⟨fun o ho => ?_, halign i⟩
    have h1 : ((c * i : Nat) : Int) ≤ intOfZ o := by
      have := ho.1; change intOfZ _ ≤ intOfZ _ at this; rwa [intOfZ_zOfInt] at this
    have h2 : intOfZ o < ((c * i : Nat) : Int) + c := by
      have := ho.2; change intOfZ _ < intOfZ _ at this
      rwa [intOfZ_add, intOfZ_zOfInt, show intOfZ (size_chunk chunk) = c from hc] at this
    have := hperm (intOfZ o) (by omega) (by have := hle i hi; omega)
    rw [zOfInt_intOfZ] at this
    exact Mem.perm_implies _ _ _ _ _ _ this (.perm_F_any _)

/-- The first `n` elements of a zero-filled `Freeable` block, as an array of
the value `v` that zero bytes decode to. -/
theorem zero_array {m : mem} {b : block} {N : Nat}
    (hz : Mem.loadbytes m b (zOfInt 0) (zOfInt N) = some (List.replicate N zb))
    (hperm : ∀ ofs : Int, 0 ≤ ofs → ofs < N → Mem.perm m b (zOfInt ofs) .Cur .Freeable)
    (hN : N < 2 ^ 62) (chunk : memory_chunk) (c : Nat) (hc : csize chunk = c)
    (ha : intOfZ (align_chunk chunk) = c) (v : val)
    (hv : decode_val chunk (List.replicate c zb) = v) (n : Nat) (hn : c * n ≤ N) :
    ArrayAt m chunk b 0 (fun _ => v) n :=
  (Zeros.of_bytes hz).array hperm hN chunk c hc ha v hv n hn

theorem zero_ints {m : mem} {b : block} {N : Nat}
    (hz : Mem.loadbytes m b (zOfInt 0) (zOfInt N) = some (List.replicate N zb))
    (hperm : ∀ ofs : Int, 0 ≤ ofs → ofs < N → Mem.perm m b (zOfInt ofs) .Cur .Freeable)
    (hN : N < 2 ^ 62) (n : Nat) (hn : 4 * n ≤ N) :
    ArrayAt m .Mint32 b 0 (fun _ => .Vint (ir 0)) n :=
  zero_array hz hperm hN .Mint32 4 rfl rfl _ rfl n hn

theorem zero_longs {m : mem} {b : block} {N : Nat}
    (hz : Mem.loadbytes m b (zOfInt 0) (zOfInt N) = some (List.replicate N zb))
    (hperm : ∀ ofs : Int, 0 ≤ ofs → ofs < N → Mem.perm m b (zOfInt ofs) .Cur .Freeable)
    (hN : N < 2 ^ 62) (n : Nat) (hn : 8 * n ≤ N) :
    ArrayAt m .Mint64 b 0 (fun _ => .Vlong (lr 0)) n :=
  zero_array hz hperm hN .Mint64 8 rfl rfl _ rfl n hn

end NautyVerified.Proofs.Alloc

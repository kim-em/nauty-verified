import NautyVerified.Proofs.Top.Init

/-!
# Copying a struct

`copy_load`: after `storebytes` of the bytes `loadbytes` read from a source
block, an aligned load in the destination returns what the same load returned
in the source.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified NautyVerified.Word

theorem zof_add (a b : Nat) :
    zOfInt ((a + b : Nat) : Int) = ZArith.BinInt.Z.add (zOfInt a) (zOfInt b) := by
  apply intOfZ_injective
  rw [intOfZ_add, intOfZ_zOfInt, intOfZ_zOfInt, intOfZ_zOfInt]; push_cast; rfl

theorem zToNat_zOfInt (a : Nat) : ZArith.BinInt.Z.to_nat (zOfInt a) = a := by
  rw [ZArith.BinInt.Z.to_nat]
  simp [intOfZ_zOfInt]

/-- `loadbytes` of `a + b` bytes splits at `a`. -/
theorem lb_split {m : mem} {b : block} {o a c : Nat} {bytes : List memval}
    (h : Mem.loadbytes m b (zOfInt o) (zOfInt ((a + c : Nat) : Int)) = some bytes) :
    ∃ b1 b2, Mem.loadbytes m b (zOfInt o) (zOfInt a) = some b1 ∧
      Mem.loadbytes m b (zOfInt ((o + a : Nat) : Int)) (zOfInt c) = some b2 ∧ bytes = b1 ++ b2 ∧
      b1.length = a ∧ b2.length = c := by
  rw [zof_add] at h
  obtain ⟨b1, b2, h1, h2, he⟩ := Mem.loadbytes_split _ _ _ _ _ _ h
    (by change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt])
    (by change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt])
  have h2' : Mem.loadbytes m b (zOfInt ((o + a : Nat) : Int)) (zOfInt c) = some b2 := by
    rw [zof_add]; exact h2
  refine ⟨b1, b2, h1, h2', he, ?_, ?_⟩
  · exact (Mem.loadbytes_length _ _ _ _ _ h1).trans (zToNat_zOfInt a)
  · exact (Mem.loadbytes_length _ _ _ _ _ h2).trans (zToNat_zOfInt c)

theorem copy_load {m m' : mem} {bs bd : block} {N : Nat} {bytes : List memval}
    (hl : Mem.loadbytes m bs (zOfInt 0) (zOfInt N) = some bytes)
    (hs : Mem.storebytes m bd (zOfInt 0) bytes = some m')
    {chunk : memory_chunk} {k s : Nat} (hsz : size_chunk chunk = zOfInt s) {v : val}
    (hv : Mem.load chunk m bs (zOfInt k) = some v) (hk : k + s ≤ N)
    (hal : ZArith.BinInt.Z.divide (align_chunk chunk) (zOfInt k)) :
    Mem.load chunk m' bd (zOfInt k) = some v := by
  obtain ⟨bk, hbk, rfl⟩ := Mem.load_loadbytes _ _ _ _ _ hv
  rw [hsz] at hbk
  have hlen : bytes.length = N := (Mem.loadbytes_length _ _ _ _ _ hl).trans (zToNat_zOfInt N)
  -- the source
  rw [show N = k + (s + (N - k - s)) by omega] at hl
  obtain ⟨a1, a2, -, ha2, rfl, la1, la2⟩ := lb_split (o := 0) hl
  rw [Nat.zero_add] at ha2
  obtain ⟨c1, c2, hc1, -, rfl, lc1, lc2⟩ := lb_split (o := k) ha2
  rw [hbk] at hc1
  cases hc1
  -- the destination
  have hd0 := Mem.loadbytes_storebytes_same _ _ _ _ _ hs
  have hz : ZArith.BinInt.Z.of_nat (a1 ++ (bk ++ c2)).length =
      zOfInt ((k + (s + (N - k - s)) : Nat) : Int) :=
    intOfZ_injective (by rw [intOfZ_of_nat, intOfZ_zOfInt]; simp [la1, lc1, lc2])
  have hd : Mem.loadbytes m' bd (zOfInt 0) (zOfInt ((k + (s + (N - k - s)) : Nat) : Int)) =
      some (a1 ++ (bk ++ c2)) := by rw [← hz]; exact hd0
  obtain ⟨d1, d2, -, hd2, he, ld1, ld2⟩ := lb_split (o := 0) hd
  rw [Nat.zero_add] at hd2
  obtain ⟨e1, e2, he1, -, rfl, le1, le2⟩ := lb_split (o := k) hd2
  have h1 := List.append_inj he (by rw [la1, ld1])
  have h2 := List.append_inj h1.2 (by rw [lc1, le1])
  rw [← h2.1] at he1
  rw [← hsz] at he1
  exact Mem.loadbytes_load _ _ _ _ _ he1 hal

end NautyVerified.Proofs.Top

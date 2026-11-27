import NautyVerified.Proofs.Alloc.Malloc

/-!
# `free`

`freeSpec b n`: freeing a block with `malloc`'s header recording `n` and
`Freeable` on `[-8, n)` succeeds and changes only that block.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word

theorem Unch.free {m m' : mem} {b : block} {lo hi : Z} (h : Mem.free m b lo hi = some m') :
    Unch m m' (· = b) :=
  ⟨fun _ _ _ hb => Mem.load_free _ _ _ _ _ h _ _ _ (.inl hb),
   fun _ _ _ _ hb hv => Mem.valid_access_free_1 _ _ _ _ _ h _ _ _ _ hv (.inl hb)⟩

/-- A block as `malloc` leaves it: the header records `n`, and `[-8, n)` is
`Freeable`. -/
structure Malloced (m : mem) (b : block) (n : Nat) : Prop where
  hdr : Mem.load Mptr m b (zOfInt (-8)) = some (.Vlong (lr n))
  perm : ∀ ofs : Int, -8 ≤ ofs → ofs < n → Mem.perm m b (zOfInt ofs) .Cur .Freeable
  small : n < 2 ^ 62

def freeSpec (b : block) (n : Nat) : FunSpec where
  pre args m := args = [.Vptr b Ptrofs.zero] ∧ Malloced m b n
  post _ m t v m' := t = E0 ∧ v = .Vundef ∧ Unch m m' (· = b)

theorem free_satisfies {xi : ExternalCalls} (b : block) (n : Nat) :
    Satisfies xi ge (.External .EF_free [tptr .Tvoid] .Tvoid Common.AST.cc_default)
      (freeSpec b n) := by
  apply satisfies_external
  rintro args m ⟨rfl, hm⟩
  have hhi : ZArith.BinInt.Z.add (Ptrofs.unsigned Ptrofs.zero)
      (Ptrofs.unsigned (Ptrofs.repr (zOfInt n))) = zOfInt n := by
    apply intOfZ_injective
    rw [intOfZ_add, intOfZ_Ptrofs_unsigned, intOfZ_Ptrofs_unsigned, bvp_repr, intOfZ_zOfInt,
      bvp_zero, BitVec.toNat_ofInt]
    have := hm.small
    rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]; omega
  have hrange : Mem.range_perm m b (zOfInt (-8)) (zOfInt n) .Cur .Freeable := fun o ho => by
    have h1 : -8 ≤ intOfZ o := by have := ho.1; change intOfZ _ ≤ intOfZ _ at this; simpa [intOfZ_zOfInt] using this
    have h2 : intOfZ o < n := by have := ho.2; change intOfZ _ < intOfZ _ at this; simpa [intOfZ_zOfInt] using this
    have := hm.perm (intOfZ o) h1 h2
    rwa [zOfInt_intOfZ] at this
  obtain ⟨m', hfree⟩ := Mem.range_perm_free _ _ _ _ hrange
  refine ⟨E0, .Vundef, m', ?_, rfl, rfl, Unch.free hfree⟩
  refine .extcall_free_sem_ptr _ _ (Ptrofs.repr (zOfInt n)) _ _ ?_ ?_
  · show Mem.load Mptr m b (zOfInt (-8)) = some (Vptrofs (Ptrofs.repr (zOfInt n)))
    rw [vptrofs_lr]; exact hm.hdr
  · have : Mem.free m b (zOfInt (-8)) (ZArith.BinInt.Z.add (Ptrofs.unsigned Ptrofs.zero)
        (Ptrofs.unsigned (Ptrofs.repr (zOfInt n)))) = some m' := by rw [hhi]; exact hfree
    exact this

end NautyVerified.Proofs.Alloc

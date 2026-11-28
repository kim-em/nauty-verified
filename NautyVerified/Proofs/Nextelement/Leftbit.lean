import NautyVerified.Program.Env
import NautyVerified.Word.Machine
import NautyVerified.Program.Dense
import NautyVerified.Proofs.Nextelement.Bits

/-!
# nauty's `leftbit` table in memory

`LeftbitTable m`: the static `leftbit[256]` of nautil.c holds, at entry `i`,
the number of leading zeros of the byte `i` (`lbv i`). `load_leftbit` is the
load a `FIRSTBITNZ` leaf performs, `leftbit[idx]` for an `unsigned long`
index below 256.
-/

namespace NautyVerified.Proofs.Nextelement

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open NautyVerified.Word NautyVerified.Program

/-- nauty's `leftbit` table, as it is in memory `m`. -/
def LeftbitTable (m : mem) : Prop :=
  ∀ i : Nat, i < 256 → Mem.load .Mint32 m E.leftbit (zOfInt (4 * (i : Int))) =
    some (.Vint (Lib.Integers.Int.repr (zOfInt (lbv i))))

theorem ofs_leftbit (ce : Cfrontend.Ctypes.composite_env) (y : Lib.Integers.int64)
    (hy : (bv64 y).toNat < 256) :
    Ptrofs.unsigned (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr (Cfrontend.Ctypes.sizeof ce (.Tint .I32 .Signed
        { attr_volatile := false, attr_alignas := none }))) (Ptrofs.of_int64 y))) =
      zOfInt (4 * ((bv64 y).toNat : Int)) := by
  apply intOfZ_injective
  rw [intOfZ_Ptrofs_unsigned, intOfZ_zOfInt]
  simp only [bvp_add, bvp_zero, bvp_mul, bvp_repr, bvp_of_int64]
  rw [show intOfZ (Cfrontend.Ctypes.sizeof ce (.Tint .I32 .Signed
    { attr_volatile := false, attr_alignas := none })) = 4 from rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofInt]
  have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
  have h4 : ((4 : Int) % ((2 ^ 64 : Nat) : Int)).toNat = 4 := by decide
  rw [h0, h4]
  omega

theorem load_leftbit {m : mem} (h : LeftbitTable m) (ce : Cfrontend.Ctypes.composite_env)
    (y : Lib.Integers.int64) (hy : (bv64 y).toNat < 256) :
    Mem.loadv .Mint32 m (.Vptr E.leftbit (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr (Cfrontend.Ctypes.sizeof ce (.Tint .I32 .Signed
        { attr_volatile := false, attr_alignas := none }))) (Ptrofs.of_int64 y)))) =
      some (.Vint (Lib.Integers.Int.repr (zOfInt (lbv (bv64 y).toNat)))) := by
  show Mem.load _ _ _ _ = _
  rw [ofs_leftbit ce y hy]
  have := h _ hy
  simpa using this

end NautyVerified.Proofs.Nextelement

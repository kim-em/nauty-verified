import NautyVerified.Proofs.Breakout.Syntax
import NautyVerified.Logic.PtrArith
import NautyVerified.Logic.Wp
import NautyVerified.Logic.Simp
import NautyVerified.Program.Dense

/-!
# `EMPTYSET` in `breakout`

`wp_clear`: the clearing loop of `breakout` sets all `m` words of the active
set to zero, changing only its block and the temporaries `es_` and `t1`.
-/

namespace NautyVerified.Proofs.Breakout

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word

variable {xi : ExternalCalls}

/-- The values of an array of `long`s. -/
def longs (ws : Nat → Lib.Integers.int64) (i : Nat) : val := .Vlong (ws i)

/-- Words below `k` as in `ws`, the rest zero. -/
def clearedFrom (ws : Nat → Lib.Integers.int64) (k : Nat) (w : Nat) : Lib.Integers.int64 :=
  if w < k then ws w else lr 0

theorem sizeof_tulong : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong) = 8 := rfl

theorem cmplu_ptrTo {m : mem} {ba : block} {base : Int} {vals : Nat → val} {M : Nat}
    (harr : ArrayAt m .Mint64 ba base vals M) (hM : 0 < M) {k : Nat} (hk : k ≤ M)
    {ofs : ptrofs} (hofs : intOfZ (Ptrofs.unsigned ofs) = base) :
    Val.cmplu_bool (Mem.valid_pointer m) .Cgt (.Vptr ba (ptrTo base 8 k)) (.Vptr ba ofs) =
      some (decide (0 < k)) := by
  have hf := harr.fits
  have hb := harr.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  have hu : intOfZ (Ptrofs.unsigned (ptrTo base 8 k)) = base + 8 * k := by
    apply unsigned_ptrTo <;> omega
  have hz1 : Ptrofs.unsigned (ptrTo base 8 k) = zOfInt (base + 8 * k) := by
    rw [← hu, zOfInt_intOfZ]
  have hz2 : Ptrofs.unsigned ofs = zOfInt base := by rw [← hofs, zOfInt_intOfZ]
  rw [cmplu_same _ _ _ _ _ (by rw [hz1]; exact harr.weak_valid hM (by omega) (by rw [h8]; omega))
    (by rw [hz2]; exact harr.weak_valid hM (by omega) (by rw [h8]; omega)), cmpu_gt]
  congr 1
  rw [intOfZ_Ptrofs_unsigned] at hu hofs
  apply decide_eq_decide.2
  omega

end NautyVerified.Proofs.Breakout

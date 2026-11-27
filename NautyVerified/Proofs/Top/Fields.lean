import NautyVerified.Program.Dense
import NautyVerified.Exec.Expr

/-!
# Struct fields `nauty()` reads

Offsets of the fields of `optionstruct` and of the `dispatchvec` (`_1027`)
fields not in `Search/Node/Fields.lean`, as the composite environment of the
dense program lays them out, each checked by the kernel.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Program NautyVerified.Source

kernel_rfl field_oGetcanon : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«getcanon» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 0)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oDigraph : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«digraph» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 4)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oWriteautoms : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«writeautoms» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 8)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oWritemarkers : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«writemarkers» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 12)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oDefaultptn : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«defaultptn» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 16)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oCartesian : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«cartesian» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 20)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oLinelength : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«linelength» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 24)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oOutfile : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«outfile» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 32)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oUserrefproc : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«userrefproc» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 40)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oUserautomproc : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«userautomproc» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 48)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oUserlevelproc : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«userlevelproc» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 56)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oUsernodeproc : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«usernodeproc» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oUsercanonproc : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«usercanonproc» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oInvarproc : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«invarproc» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oTcLevel : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«tc_level» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 88)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oMininvarlevel : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«mininvarlevel» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 92)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oMaxinvarlevel : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«maxinvarlevel» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 96)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oInvararg : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«invararg» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 100)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oDispatch : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«dispatch» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 104)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_oSchreier : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«schreier» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 112)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dFreedyn : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«freedyn» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 56)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dCheck : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«check» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dInit : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«init» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dCleanup : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«cleanup» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

end NautyVerified.Proofs.Top

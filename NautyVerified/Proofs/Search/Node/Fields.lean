import NautyVerified.Program.Dense
import NautyVerified.Exec.Expr

/-!
# Struct fields nauty.c's search reads

Offsets of the fields of `tcnode`, `statsblk` (`_1024`) and `dispatchvec`
(`_1027`) as the composite environment of the dense program lays them out,
each checked by the kernel.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Program NautyVerified.Source

kernel_rfl field_tcnodeNext : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«tcnode_struct» noattr) dense.id.«next» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 0)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_tcnodeTcell : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«tcnode_struct» noattr) dense.id.«tcellptr» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 8)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsGrpsize1 : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«grpsize1» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 0)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsGrpsize2 : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«grpsize2» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 8)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsNumorbits : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«numorbits» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 12)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsNumgenerators : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«numgenerators» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 16)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsErrstatus : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«errstatus» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 20)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsNumnodes : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«numnodes» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 24)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsNumbadleaves : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«numbadleaves» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 32)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsMaxlevel : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«maxlevel» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 40)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsTctotal : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«tctotal» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 48)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_statsCanupdates : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«canupdates» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 56)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dIsautom : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«isautom» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 0)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dTestcanlab : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«testcanlab» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 8)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dUpdatecan : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«updatecan» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 16)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dRefine : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«refine» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 24)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dRefine1 : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«refine1» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 32)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dCheapautom : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«cheapautom» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 40)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

kernel_rfl field_dTargetcell : ∀ (b : block) (ofs : ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«targetcell» (.Vptr b ofs) =
    some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 48)), CompCert4Lean.Cfrontend.Ctypes.bitfield.Full)

end NautyVerified.Proofs.Search

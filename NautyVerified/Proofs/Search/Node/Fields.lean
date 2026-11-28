import NautyVerified.Program.Env

/-!
# Struct fields nauty.c's search reads

Offsets of the fields of `tcnode`, `statsblk` (`_1024`) and `dispatchvec`
(`_1027`) in the composite environment of any linked program, from its
`NautyEnv` (each instance checks them by the kernel: `DenseLayout` in
`Program/Env.lean`, `SparseEnv` in `Program/Sparse.lean`).
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Program NautyVerified.Source

variable {ge : genv} [E : NautyEnv ge]

theorem field_tcnodeNext : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr) dense.id.«next» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 0)), .Full) :=
  E.field_tcnodeNext

theorem field_tcnodeTcell : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr) dense.id.«tcellptr» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 8)), .Full) :=
  E.field_tcnodeTcell

theorem field_statsGrpsize1 : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«grpsize1» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 0)), .Full) :=
  E.field_statsGrpsize1

theorem field_statsGrpsize2 : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«grpsize2» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 8)), .Full) :=
  E.field_statsGrpsize2

theorem field_statsNumorbits : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numorbits» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 12)), .Full) :=
  E.field_statsNumorbits

theorem field_statsNumgenerators : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numgenerators» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 16)), .Full) :=
  E.field_statsNumgenerators

theorem field_statsErrstatus : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«errstatus» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 20)), .Full) :=
  E.field_statsErrstatus

theorem field_statsNumnodes : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numnodes» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 24)), .Full) :=
  E.field_statsNumnodes

theorem field_statsNumbadleaves : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«numbadleaves» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 32)), .Full) :=
  E.field_statsNumbadleaves

theorem field_statsMaxlevel : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«maxlevel» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 40)), .Full) :=
  E.field_statsMaxlevel

theorem field_statsTctotal : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«tctotal» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 48)), .Full) :=
  E.field_statsTctotal

theorem field_statsCanupdates : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) dense.id.«canupdates» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 56)), .Full) :=
  E.field_statsCanupdates

theorem field_dIsautom : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«isautom» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 0)), .Full) :=
  E.field_dIsautom

theorem field_dTestcanlab : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«testcanlab» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 8)), .Full) :=
  E.field_dTestcanlab

theorem field_dUpdatecan : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«updatecan» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 16)), .Full) :=
  E.field_dUpdatecan

theorem field_dRefine : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«refine» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 24)), .Full) :=
  E.field_dRefine

theorem field_dRefine1 : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«refine1» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 32)), .Full) :=
  E.field_dRefine1

theorem field_dCheapautom : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«cheapautom» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 40)), .Full) :=
  E.field_dCheapautom

theorem field_dTargetcell : ∀ (b : block) (ofs : Lib.Integers.ptrofs),
    Exec.lvalOfField ge (Cfrontend.Ctypes.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr) dense.id.«targetcell» (.Vptr b ofs) =
      some (b, Lib.Integers.Ptrofs.add ofs (Lib.Integers.Ptrofs.repr (Foundation.Numbers.Rocq.Coq.zOfInt 48)), .Full) :=
  E.field_dTargetcell

end NautyVerified.Proofs.Search

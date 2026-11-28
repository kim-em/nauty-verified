import NautyVerified.Proofs.Top.NautySyntax
import NautyVerified.Proofs.Alloc.Dyn
import NautyVerified.Proofs.Top.Fields
import NautyVerified.Program.Sparse

/-!
# `nauty()`'s local environment

`nauty()` has one addressable local, `int initstatus` (its address is passed
to `dispatch.init`), so its body runs in the environment `nEnv bI` binding
`initstatus` to the block `bI`. Every other identifier is absent from it, so
reading a global looks up the global environment as in `empty_env`.

`TopEnv ge`: the facts about a linked program that `nauty()`'s own proofs use
beyond `NautyEnv`: that `initstatus` names no global, so `nEnv` shadows none;
the member offsets of `optionstruct` and of the `dispatchvec` (`_1027`) members
`freedyn`, `check`, `init` and `cleanup`; and the size and alignment of
`dispatchvec`, which `nauty()` copies; the offsets of the `statsblk` members
only `nauty()` writes. `TopEnv.dense` is the dense program's
instance (`Top/Fields.lean`); `TopEnv.sparse`, each fact checked by the kernel
against `sparseGe`, is not a global instance (as `NautyEnv.sparse`).
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Lib.Maps CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Program NautyVerified.Source

/-- `nauty()`'s environment: `initstatus` at the block `bI`. -/
abbrev nEnv (bI : Common.Values.block) : env :=
  PTree.set dense.id.«initstatus» (bI, tint) empty_env

-- `initstatus` names no global.
kernel_rfl find_initstatus : Common.Globalenvs.Genv.find_symbol ge.genv_genv dense.id.«initstatus» = none

theorem noShadow_nEnv {bI : Common.Values.block} : Alloc.NoShadow (nEnv bI) := by
  intro i b hb
  by_cases h : i = dense.id.«initstatus»
  · subst h; rw [find_initstatus] at hb; cases hb
  · exact (PTree.gso _ _ h).trans rfl

kernel_rfl field_statsInvapplics : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«invapplics» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), .Full)

kernel_rfl field_statsInvsuccesses : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«invsuccesses» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), .Full)

kernel_rfl field_statsInvarsuclevel : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«invarsuclevel» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), .Full)

/-- The program facts `nauty()`'s proofs use beyond `NautyEnv`. -/
class TopEnv (ge : outParam genv) where
  find_initstatus : Common.Globalenvs.Genv.find_symbol ge.genv_genv dense.id.«initstatus» = none
  field_oGetcanon : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«getcanon» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 0)), .Full)
  field_oDigraph : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«digraph» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 4)), .Full)
  field_oWriteautoms : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«writeautoms» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 8)), .Full)
  field_oWritemarkers : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«writemarkers» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 12)), .Full)
  field_oDefaultptn : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«defaultptn» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 16)), .Full)
  field_oCartesian : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«cartesian» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 20)), .Full)
  field_oLinelength : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«linelength» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 24)), .Full)
  field_oOutfile : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«outfile» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 32)), .Full)
  field_oUserrefproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«userrefproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 40)), .Full)
  field_oUserautomproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«userautomproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 48)), .Full)
  field_oUserlevelproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«userlevelproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 56)), .Full)
  field_oUsernodeproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«usernodeproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), .Full)
  field_oUsercanonproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«usercanonproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), .Full)
  field_oInvarproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«invarproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), .Full)
  field_oTcLevel : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«tc_level» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 88)), .Full)
  field_oMininvarlevel : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«mininvarlevel» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 92)), .Full)
  field_oMaxinvarlevel : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«maxinvarlevel» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 96)), .Full)
  field_oInvararg : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«invararg» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 100)), .Full)
  field_oDispatch : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«dispatch» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 104)), .Full)
  field_oSchreier : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«optionstruct» noattr) dense.id.«schreier» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 112)), .Full)
  field_dFreedyn : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«freedyn» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 56)), .Full)
  field_dCheck : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«check» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), .Full)
  field_dInit : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«init» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), .Full)
  field_dCleanup : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) dense.id.«cleanup» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), .Full)
  /-- `sizeof` and the block-copy alignment of `dispatchvec`. -/
  sizeof_dispatch : sizeof ge.genv_cenv (Tstruct dense.id._1027 noattr) = zOfInt 88
  align_dispatch : alignof_blockcopy ge.genv_cenv (Tstruct dense.id._1027 noattr) = zOfInt 8
  /-- The offsets of `statsblk`'s members that only `nauty()` writes. -/
  field_statsInvapplics : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«invapplics» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), .Full)
  field_statsInvsuccesses : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«invsuccesses» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), .Full)
  field_statsInvarsuclevel : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.«invarsuclevel» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), .Full)

instance TopEnv.dense : TopEnv ge where
  find_initstatus := NautyVerified.Proofs.Top.find_initstatus
  field_oGetcanon := NautyVerified.Proofs.Top.field_oGetcanon
  field_oDigraph := NautyVerified.Proofs.Top.field_oDigraph
  field_oWriteautoms := NautyVerified.Proofs.Top.field_oWriteautoms
  field_oWritemarkers := NautyVerified.Proofs.Top.field_oWritemarkers
  field_oDefaultptn := NautyVerified.Proofs.Top.field_oDefaultptn
  field_oCartesian := NautyVerified.Proofs.Top.field_oCartesian
  field_oLinelength := NautyVerified.Proofs.Top.field_oLinelength
  field_oOutfile := NautyVerified.Proofs.Top.field_oOutfile
  field_oUserrefproc := NautyVerified.Proofs.Top.field_oUserrefproc
  field_oUserautomproc := NautyVerified.Proofs.Top.field_oUserautomproc
  field_oUserlevelproc := NautyVerified.Proofs.Top.field_oUserlevelproc
  field_oUsernodeproc := NautyVerified.Proofs.Top.field_oUsernodeproc
  field_oUsercanonproc := NautyVerified.Proofs.Top.field_oUsercanonproc
  field_oInvarproc := NautyVerified.Proofs.Top.field_oInvarproc
  field_oTcLevel := NautyVerified.Proofs.Top.field_oTcLevel
  field_oMininvarlevel := NautyVerified.Proofs.Top.field_oMininvarlevel
  field_oMaxinvarlevel := NautyVerified.Proofs.Top.field_oMaxinvarlevel
  field_oInvararg := NautyVerified.Proofs.Top.field_oInvararg
  field_oDispatch := NautyVerified.Proofs.Top.field_oDispatch
  field_oSchreier := NautyVerified.Proofs.Top.field_oSchreier
  field_dFreedyn := NautyVerified.Proofs.Top.field_dFreedyn
  field_dCheck := NautyVerified.Proofs.Top.field_dCheck
  field_dInit := NautyVerified.Proofs.Top.field_dInit
  field_dCleanup := NautyVerified.Proofs.Top.field_dCleanup
  sizeof_dispatch := NautyVerified.Proofs.Top.sizeof_dispatch
  align_dispatch := NautyVerified.Proofs.Top.align_dispatch
  field_statsInvapplics := NautyVerified.Proofs.Top.field_statsInvapplics
  field_statsInvsuccesses := NautyVerified.Proofs.Top.field_statsInvsuccesses
  field_statsInvarsuclevel := NautyVerified.Proofs.Top.field_statsInvarsuclevel

namespace SparseTop

kernel_rfl field_oGetcanon : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«getcanon» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 0)), .Full)

kernel_rfl field_oDigraph : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«digraph» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 4)), .Full)

kernel_rfl field_oWriteautoms : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«writeautoms» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 8)), .Full)

kernel_rfl field_oWritemarkers : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«writemarkers» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 12)), .Full)

kernel_rfl field_oDefaultptn : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«defaultptn» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 16)), .Full)

kernel_rfl field_oCartesian : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«cartesian» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 20)), .Full)

kernel_rfl field_oLinelength : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«linelength» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 24)), .Full)

kernel_rfl field_oOutfile : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«outfile» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 32)), .Full)

kernel_rfl field_oUserrefproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«userrefproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 40)), .Full)

kernel_rfl field_oUserautomproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«userautomproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 48)), .Full)

kernel_rfl field_oUserlevelproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«userlevelproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 56)), .Full)

kernel_rfl field_oUsernodeproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«usernodeproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), .Full)

kernel_rfl field_oUsercanonproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«usercanonproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), .Full)

kernel_rfl field_oInvarproc : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«invarproc» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), .Full)

kernel_rfl field_oTcLevel : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«tc_level» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 88)), .Full)

kernel_rfl field_oMininvarlevel : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«mininvarlevel» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 92)), .Full)

kernel_rfl field_oMaxinvarlevel : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«maxinvarlevel» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 96)), .Full)

kernel_rfl field_oInvararg : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«invararg» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 100)), .Full)

kernel_rfl field_oDispatch : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«dispatch» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 104)), .Full)

kernel_rfl field_oSchreier : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«optionstruct» noattr) dense.id.«schreier» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 112)), .Full)

kernel_rfl field_dFreedyn : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«_1027» noattr) dense.id.«freedyn» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 56)), .Full)

kernel_rfl field_dCheck : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«_1027» noattr) dense.id.«check» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), .Full)

kernel_rfl field_dInit : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«_1027» noattr) dense.id.«init» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), .Full)

kernel_rfl field_dCleanup : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«_1027» noattr) dense.id.«cleanup» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), .Full)

kernel_rfl sizeof_dispatch : sizeof sparseGe.genv_cenv (Tstruct dense.id._1027 noattr) = zOfInt 88

kernel_rfl align_dispatch :
  alignof_blockcopy sparseGe.genv_cenv (Tstruct dense.id._1027 noattr) = zOfInt 8

kernel_rfl find_initstatus :
  Common.Globalenvs.Genv.find_symbol sparseGe.genv_genv dense.id.«initstatus» = none

kernel_rfl field_statsInvapplics : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«_1024» noattr) dense.id.«invapplics» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 64)), .Full)
kernel_rfl field_statsInvsuccesses : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«_1024» noattr) dense.id.«invsuccesses» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 72)), .Full)
kernel_rfl field_statsInvarsuclevel : ∀ (b : block) (ofs : ptrofs),
    Exec.lvalOfField sparseGe (Tstruct dense.id.«_1024» noattr) dense.id.«invarsuclevel» (.Vptr b ofs) =
      some (b, Ptrofs.add ofs (Ptrofs.repr (zOfInt 80)), .Full)

end SparseTop

/-- The sparse program's facts. -/
theorem TopEnv.sparse : TopEnv sparseGe where
  find_initstatus := SparseTop.find_initstatus
  field_oGetcanon := SparseTop.field_oGetcanon
  field_oDigraph := SparseTop.field_oDigraph
  field_oWriteautoms := SparseTop.field_oWriteautoms
  field_oWritemarkers := SparseTop.field_oWritemarkers
  field_oDefaultptn := SparseTop.field_oDefaultptn
  field_oCartesian := SparseTop.field_oCartesian
  field_oLinelength := SparseTop.field_oLinelength
  field_oOutfile := SparseTop.field_oOutfile
  field_oUserrefproc := SparseTop.field_oUserrefproc
  field_oUserautomproc := SparseTop.field_oUserautomproc
  field_oUserlevelproc := SparseTop.field_oUserlevelproc
  field_oUsernodeproc := SparseTop.field_oUsernodeproc
  field_oUsercanonproc := SparseTop.field_oUsercanonproc
  field_oInvarproc := SparseTop.field_oInvarproc
  field_oTcLevel := SparseTop.field_oTcLevel
  field_oMininvarlevel := SparseTop.field_oMininvarlevel
  field_oMaxinvarlevel := SparseTop.field_oMaxinvarlevel
  field_oInvararg := SparseTop.field_oInvararg
  field_oDispatch := SparseTop.field_oDispatch
  field_oSchreier := SparseTop.field_oSchreier
  field_dFreedyn := SparseTop.field_dFreedyn
  field_dCheck := SparseTop.field_dCheck
  field_dInit := SparseTop.field_dInit
  field_dCleanup := SparseTop.field_dCleanup
  sizeof_dispatch := SparseTop.sizeof_dispatch
  align_dispatch := SparseTop.align_dispatch
  field_statsInvapplics := SparseTop.field_statsInvapplics
  field_statsInvsuccesses := SparseTop.field_statsInvsuccesses
  field_statsInvarsuclevel := SparseTop.field_statsInvarsuclevel

theorem noShadow_nEnvG {ge : genv} [NautyEnv ge] [T : TopEnv ge] {bI : Common.Values.block} :
    Alloc.NoShadow (ge := ge) (nEnv bI) := by
  intro i b hb
  by_cases h : i = dense.id.«initstatus»
  · subst h; rw [T.find_initstatus] at hb; cases hb
  · exact (PTree.gso _ _ h).trans rfl

end NautyVerified.Proofs.Top

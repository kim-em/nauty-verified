import NautyVerified.Proofs.Search.Processnode.Set
import NautyVerified.Proofs.Search.Node.Fields
import NautyVerified.Proofs.Isautom.Satisfies
import NautyVerified.Proofs.Updatecan.Satisfies
import NautyVerified.Proofs.Testcanlab.Satisfies
import NautyVerified.Proofs.Fmperm.Satisfies
import NautyVerified.Proofs.Fmptn.Satisfies
import NautyVerified.Proofs.Orbjoin.Satisfies

/-!
# The functions `processnode` calls

`eval_dispatch`: a function pointer read from nauty's `dispatch` table. The
`type_*` lemmas give the callees' types.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search

/-- `*dispatch.fld`, a function of type `fty`, for the field at byte `off`. -/
theorem eval_dispatch {e : env} {le : temp_env} {m : mem} {fld : ident} {fty : type}
    {off : Int} {fb : block} (hge : PTree.get dense.id.«nauty:dispatch» e = none)
    (hfld : ∀ b o, Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) fld (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (hacc : access_mode fty = .By_reference) (h0 : 0 ≤ off) (h1 : off < 2 ^ 32)
    (hf : FieldAt m .Mint64 Block.dispatch off (.Vptr fb Ptrofs.zero)) :
    Exec.evalExpr ge e le m
      (.Ederef (.Efield (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr)) fld
        (tptr fty)) fty) = some (.Vptr fb Ptrofs.zero) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, find_dispatch, Exec.derefLoc, typeof, hfld,
    Mem.loadv, hacc, Alloc.Mptr_eq, show access_mode (tptr fty) = .By_value .Mint64 from rfl,
    show access_mode (Tstruct dense.id.«_1027» noattr) = .By_copy from rfl]
  rw [unsigned_add_off Ptrofs.zero h0 (by
    rw [show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl]; omega)]
  rw [show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl, Int.zero_add, hf.load]

kernel_rfl type_isautom : type_of_fundef (.Internal dense.fn.«isautom») =
  tfun [tptr tulong, tptr tint, tint, tint, tint] tint
kernel_rfl type_updatecan : type_of_fundef (.Internal dense.fn.«updatecan») =
  tfun [tptr tulong, tptr tulong, tptr tint, tint, tint, tint] .Tvoid
kernel_rfl type_testcanlab : type_of_fundef (.Internal dense.fn.«testcanlab») =
  tfun [tptr tulong, tptr tulong, tptr tint, tptr tint, tint, tint] tint
kernel_rfl type_fmperm : type_of_fundef (.Internal dense.fn.«fmperm») =
  tfun [tptr tint, tptr tulong, tptr tulong, tint, tint] .Tvoid
kernel_rfl type_fmptn : type_of_fundef (.Internal dense.fn.«fmptn») =
  tfun [tptr tint, tptr tint, tint, tptr tulong, tptr tulong, tint, tint] .Tvoid
kernel_rfl type_orbjoin : type_of_fundef (.Internal dense.fn.«orbjoin») =
  tfun [tptr tint, tptr tint, tint] tint

end NautyVerified.Proofs.Search.Processnode

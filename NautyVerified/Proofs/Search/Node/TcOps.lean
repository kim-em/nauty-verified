import NautyVerified.Program.Env
import NautyVerified.Proofs.Search.Node.Tc
import NautyVerified.Proofs.Search.Node.Fields
import NautyVerified.Proofs.Alloc.Dyn
import NautyVerified.Proofs.Search.Ops

/-!
# Reading and writing `tcnode` fields

`tcF p fld` is `p->fld` for a `tcnode *` temporary `p`; `eval_tcF` reads it
at the field's offset, `wp_tcFStore` writes it.
-/

namespace NautyVerified.Proofs.Search

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Source NautyVerified.Word

variable {xi : ExternalCalls}

abbrev tcStruct : type := Tstruct dense.id.«tcnode_struct» noattr

/-- `p->fld` for a `tcnode *` temporary `p`. -/
abbrev tcF (p fld : Common.AST.ident) (ty : type) : expr :=
  .Efield (.Ederef (.Etempvar p (tptr tcStruct)) tcStruct) fld ty

theorem eval_tcF {e : env} {le : temp_env} {m : mem} {p fld : Common.AST.ident} {t : type}
    {b : block} {off : Nat} {v : val} (hp : PTree.get p le = some (.Vptr b Ptrofs.zero))
    (hfld : Exec.lvalOfField ge tcStruct fld (.Vptr b Ptrofs.zero) =
      some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt off)), .Full))
    (hoff : off < 2 ^ 63) (hl : FieldAt m .Mint64 b off v) :
    Exec.evalExpr ge e le m (tcF p fld (tptr t)) = some v := by
  simp only [Exec.evalExpr, hp, typeof, Exec.derefLoc, Cfrontend.Ctypes.access_mode, hfld, Mem.loadv]
  rw [unsigned_add_off Ptrofs.zero (by omega) (by
    rw [show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl]; omega),
    show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl, Int.zero_add, Alloc.Mptr_eq]
  exact hl.load

/-- `p->fld = a`. -/
theorem wp_tcFStore {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {p fld : Common.AST.ident} {t : type} {a : expr} {b : block} {off : Nat} {v : val}
    (hp : PTree.get p le = some (.Vptr b Ptrofs.zero))
    (hfld : Exec.lvalOfField ge tcStruct fld (.Vptr b Ptrofs.zero) =
      some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt off)), .Full))
    (hoff : off < 2 ^ 63) (ha : Exec.evalExpr ge e le m a = some v)
    {ta : type} (hta : typeof a = ta) (hcast : Cfrontend.Cop.sem_cast v ta (tptr t) m = some v)
    (hw : Mem.valid_access m .Mint64 b (zOfInt off) .Writable)
    (hQ : ∀ m', Mem.store .Mint64 m b (zOfInt off) v = some m' → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (tcF p fld (tptr t)) a) Q e le m := by
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ v hw
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hta]
  simp only [typeof, Exec.derefLoc, Cfrontend.Ctypes.access_mode, hfld]
  simp only [hcast, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [unsigned_add_off Ptrofs.zero (by omega) (by
    rw [show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl]; omega),
    show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl, Int.zero_add, Alloc.Mptr_eq, hst]
  exact hQ m' hst

end NautyVerified.Proofs.Search

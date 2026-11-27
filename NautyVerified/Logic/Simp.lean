import CompCert4Lean.Cfrontend.Clight

/-!
# Simplification lemmas for symbolic execution

Temporaries are a `PTree` of values; during symbolic execution they are a
chain of `PTree.set` over concrete identifiers, so lookups reduce by `gss`
and `gso` with the side condition decided on the identifiers.
-/

namespace NautyVerified.Logic

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

@[simp] theorem ptree_gss {A : Type} (i : positive) (x : A) (m : PTree.tree A) :
    PTree.get i (PTree.set i x m) = some x := PTree.gss i x m

@[simp] theorem ptree_gso {A : Type} {i j : positive} (x : A) (m : PTree.tree A)
    (h : i ≠ j := by decide) : PTree.get i (PTree.set j x m) = PTree.get i m :=
  PTree.gso x m h

@[simp] theorem ptree_gempty {A : Type} (i : positive) : PTree.get i (PTree.empty A) = none :=
  PTree.gempty A i

/-! The same for Clight's temporaries and local environments, whose types are
definitions of `PTree.t` (so the generic lemmas do not match them syntactically). -/

open CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Values in
@[simp] theorem temps_gss (i : positive) (v : val) (le : temp_env) :
    PTree.get i (PTree.set i v le) = some v := PTree.gss i v le

open CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Values in
@[simp] theorem temps_gso {i j : positive} (v : val) (le : temp_env) (h : i ≠ j := by decide) :
    PTree.get i (PTree.set j v le) = PTree.get i le := PTree.gso v le h

end NautyVerified.Logic

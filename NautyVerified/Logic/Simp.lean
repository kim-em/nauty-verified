import CompCert4Lean.Lib.Maps

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

end NautyVerified.Logic

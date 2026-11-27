import NautyVerified.Proofs.Set.Syntax
import NautyVerified.Proofs.Nextelement.Syntax
import NautyVerified.Logic.For

/-!
# `permset`, factored

The Clight of nauty's `permset` (nautil.c), in named pieces; `body_eq` pins
it to `dense.body.permset`. `TAKEBIT(b, setw)` inlines `FIRSTBITNZ(setw)` as
`nextelement`'s decision tree (`Nextelement.fbTree`).
-/

namespace NautyVerified.Proofs.Permset

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv emptySet addElement bit)

namespace id
abbrev set1 : Common.AST.ident := dense.id.set1
abbrev set2 : Common.AST.ident := dense.id.set2
abbrev m : Common.AST.ident := dense.id.m
abbrev perm : Common.AST.ident := dense.id.perm
abbrev setw : Common.AST.ident := dense.id.setw
abbrev pos : Common.AST.ident := dense.id.pos
abbrev b : Common.AST.ident := dense.id.b
abbrev w : Common.AST.ident := dense.id.w
abbrev es : Common.AST.ident := dense.id.es_
abbrev t1 : Common.AST.ident := idOf 703
abbrev t2 : Common.AST.ident := idOf 704
abbrev t3 : Common.AST.ident := idOf 705
end id

abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint
abbrev sw : expr := .Etempvar id.setw tulong

/-- `bit[e]`. -/
abbrev bitAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar bit (tarray tulong 64)) e (tptr tulong)) tulong

/-- `perm[e]`. -/
abbrev permAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.perm (tptr tint)) e (tptr tint)) tint

/-- `TAKEBIT(b, setw)`, with the tree's result in `t`. -/
abbrev takebit (t : Common.AST.ident) : statement :=
  .Ssequence (.Ssequence (Nextelement.fbTree t id.setw) (.Sset id.b (tv t)))
    (sk (.Sset id.setw (.Ebinop .Oxor sw (bitAt (tv id.b)) tulong)))

/-- `while (setw != 0) { TAKEBIT(b, setw); body }` -/
abbrev bits (t : Common.AST.ident) (body : statement) : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .One sw (ci 0 tint) tint) .Sskip .Sbreak))
      (.Ssequence (takebit t) body))
    .Sskip

/-- The `m == 1` case. -/
abbrev one : statement :=
  .Ssequence (sk (.Sassign (.Ederef (pv id.set2) tulong) (ci 0 tint)))
    (.Ssequence
      (sk (.Sset id.setw (.Ederef (.Ebinop .Oadd (pv id.set1) (ci 0 tint) (tptr tulong)) tulong)))
      (bits id.t1 (sk (.Sassign (.Ederef (pv id.set2) tulong)
        (.Ebinop .Oor (.Ederef (pv id.set2) tulong) (bitAt (permAt (tv id.b))) tulong)))))

/-- The body of the loop over words, for word `w`. -/
abbrev word : statement :=
  .Ssequence
    (sk (.Sset id.setw (.Ederef (.Ebinop .Oadd (pv id.set1) (tv id.w) (tptr tulong)) tulong)))
    (bits id.t3
      (.Ssequence
        (sk (.Sset id.pos (permAt (.Ebinop .Oadd (.Ebinop .Oshl (tv id.w) (ci 6 tint) tint) (tv id.b) tint))))
        (addElement id.set2 (tv id.pos))))

/-- The general case. -/
abbrev many : statement :=
  .Ssequence (emptySet id.set2 id.m id.es id.t2) (NautyVerified.Logic.forLoop id.w id.m word)

abbrev body : statement :=
  sk (.Sifthenelse (.Ebinop .Oeq (tv id.m) (ci 1 tint) tint) one many)

kernel_rfl body_eq : dense.body.permset = body

end NautyVerified.Proofs.Permset

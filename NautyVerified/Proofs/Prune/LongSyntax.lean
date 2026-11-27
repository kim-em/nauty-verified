import NautyVerified.Proofs.Set.Subset

/-!
# `longprune`, factored

The Clight of nauty's `longprune` (nautil.c), in named pieces; `body_eq` pins
it to `dense.body.longprune`.
-/

namespace NautyVerified.Proofs.Prune.Long

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Logic NautyVerified.Proofs.Set

namespace id
abbrev tcell : Common.AST.ident := dense.id.tcell
abbrev fix : Common.AST.ident := dense.id.fix
abbrev bottom : Common.AST.ident := dense.id.bottom
abbrev top : Common.AST.ident := dense.id.top
abbrev m : Common.AST.ident := dense.id.m
abbrev i : Common.AST.ident := dense.id.i
end id

/-- `bottom += M;` -/
abbrev advance : statement :=
  sk (.Sset id.bottom (.Ebinop .Oadd (pv id.bottom) (.Etempvar id.m tint) (tptr tulong)))

/-- One pair: test `fix ⊆ bottom`, step to the second set, intersect, step on. -/
abbrev pair : statement :=
  .Ssequence (forLoop id.i id.m (notSubsetBreak id.fix id.bottom id.i))
    (.Ssequence advance
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Oeq (.Etempvar id.i tint) (.Etempvar id.m tint) tint)
          (forLoop id.i id.m (andWord id.tcell id.bottom id.i)) .Sskip))
        advance))

abbrev body : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (pv id.bottom) (pv id.top) tint) .Sskip .Sbreak))
      pair)
    .Sskip

kernel_rfl body_eq : dense.body.longprune = body

end NautyVerified.Proofs.Prune.Long

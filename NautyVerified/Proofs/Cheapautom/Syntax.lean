import NautyVerified.Proofs.Syntax
import NautyVerified.Source.Dense

/-!
# `cheapautom`, factored

The Clight of nauty's `cheapautom` (naugraph.c), in named pieces; `body_eq`
pins it to `dense.body.cheapautom`.
-/

namespace NautyVerified.Proofs.Cheapautom

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source

namespace id
abbrev ptn : Common.AST.ident := dense.id.ptn
abbrev level : Common.AST.ident := dense.id.level
abbrev digraph : Common.AST.ident := dense.id.digraph
abbrev n : Common.AST.ident := dense.id.n
abbrev i : Common.AST.ident := dense.id.i
abbrev k : Common.AST.ident := dense.id.k
abbrev nnt : Common.AST.ident := dense.id.nnt
abbrev t1 : Common.AST.ident := idOf 703
abbrev t2 : Common.AST.ident := idOf 704
end id

abbrev sk (s : statement) : statement := .Ssequence .Sskip s
abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint

/-- `ptn[e]`. -/
abbrev ptnAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.ptn (tptr tint)) e (tptr tint)) tint

/-- `while (ptn[++i] > level) {}` -/
abbrev skip : statement :=
  .Sloop
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (sk (.Sset id.t1 (.Ecast (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint) tint)))
          (.Sset id.i (tv id.t1)))
        (.Sifthenelse (.Ebinop .Ogt (ptnAt (tv id.t1)) (tv id.level) tint) .Sskip .Sbreak))
      .Sskip)
    .Sskip

/-- The body of the loop over cells. -/
abbrev cellBody : statement :=
  .Ssequence (sk (.Sset id.k (.Ebinop .Osub (tv id.k) (ci 1 tint) tint)))
    (sk (.Sifthenelse (.Ebinop .Ogt (ptnAt (tv id.i)) (tv id.level) tint)
      (.Ssequence (sk (.Sset id.nnt (.Ebinop .Oadd (tv id.nnt) (ci 1 tint) tint))) skip)
      .Sskip))

/-- `for (i = 0; i < n; ++i) cellBody` -/
abbrev loop : statement :=
  .Ssequence (sk (.Sset id.i (ci 0 tint)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak))
        cellBody)
      (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))))

/-- `return (k <= nnt + 1 || k <= 4);` -/
abbrev ret : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Ebinop .Ole (tv id.k) (.Ebinop .Oadd (tv id.nnt) (ci 1 tint) tint) tint)
      (.Sset id.t2 (ci 1 tint))
      (sk (.Sset id.t2 (.Ecast (.Ebinop .Ole (tv id.k) (ci 4 tint) tint) tbool)))))
    (.Sreturn (some (tv id.t2)))

abbrev body : statement :=
  .Ssequence (sk (.Sifthenelse (tv id.digraph) (sk (.Sreturn (some (ci 0 tint)))) .Sskip))
    (.Ssequence (sk (.Sset id.k (tv id.n)))
      (.Ssequence (sk (.Sset id.nnt (ci 0 tint)))
        (.Ssequence loop ret)))

kernel_rfl body_eq : dense.body.cheapautom = body

end NautyVerified.Proofs.Cheapautom

import NautyVerified.Proofs.Syntax
import NautyVerified.Source.Dense

/-!
# nauty's set macros, as SimplExpr writes them

`emptySet s m es t` is `EMPTYSET(s, m)` (`es` and `t` the temporaries
SimplExpr introduces), and `addElement s a` is `ADDELEMENT(s, a)` for an
`int` expression `a`, reading nautil.c's `bit` table.
-/

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source

abbrev sk (s : statement) : statement := .Ssequence .Sskip s
abbrev pv (x : Common.AST.ident) : expr := .Etempvar x (tptr tulong)

/-- nautil.c's `bit`. -/
abbrev bit : Common.AST.ident := NautyVerified.Source.dense.id.«nautil:bit»

/-- `EMPTYSET(s, m)`: clear the words from the end. -/
abbrev emptySet (s m es t : Common.AST.ident) : statement :=
  .Ssequence
    (sk (.Sset es (.Ebinop .Oadd (.Ecast (pv s) (tptr tulong)) (.Etempvar m tint) (tptr tulong))))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Ogt (pv es) (.Ecast (pv s) (tptr tulong)) tint)
          .Sskip .Sbreak))
        (.Ssequence
          (.Ssequence
            (sk (.Sset t (.Ecast (.Ebinop .Osub (pv es) (ci 1 tint) (tptr tulong)) (tptr tulong))))
            (.Sset es (pv t)))
          (.Sassign (.Ederef (pv t) tulong) (ci 0 tint))))
      .Sskip)

/-- `s[a >> 6]`. -/
abbrev setWord (s : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (pv s) (.Ebinop .Oshr a (ci 6 tint) tint) (tptr tulong)) tulong

/-- `ADDELEMENT(s, a)`. -/
abbrev addElement (s : Common.AST.ident) (a : expr) : statement :=
  sk (.Sassign (setWord s a)
    (.Ebinop .Oor (setWord s a)
      (.Ederef (.Ebinop .Oadd (.Evar bit (tarray tulong 64))
        (.Ebinop .Oand a (ci 63 tint) tint) (tptr tulong)) tulong) tulong))

end NautyVerified.Proofs.Set

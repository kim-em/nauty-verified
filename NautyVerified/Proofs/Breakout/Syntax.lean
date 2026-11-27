import NautyVerified.Proofs.Syntax
import NautyVerified.Source.Dense

/-!
# `breakout`, factored

The Clight of nauty's `breakout` (nautil.c), in named pieces; `body_eq` pins it
to `dense.body.breakout`. `breakout` empties the active set and adds the target
cell `tc`, rotates `tv` to the front of the cell in `lab`, and closes the new
one-element cell in `ptn`.
-/

namespace NautyVerified.Proofs.Breakout

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source

namespace id
abbrev lab : Common.AST.ident := dense.id.lab
abbrev ptn : Common.AST.ident := dense.id.ptn
abbrev level : Common.AST.ident := dense.id.level
abbrev tc : Common.AST.ident := dense.id.tc
abbrev tv : Common.AST.ident := dense.id.tv
abbrev active : Common.AST.ident := dense.id.active
abbrev m : Common.AST.ident := dense.id.m
abbrev i : Common.AST.ident := dense.id.i
abbrev prev : Common.AST.ident := dense.id.prev
abbrev next : Common.AST.ident := dense.id.next
abbrev es : Common.AST.ident := dense.id.es_
abbrev t1 : Common.AST.ident := idOf 703
abbrev t2 : Common.AST.ident := idOf 704
abbrev bit : Common.AST.ident := NautyVerified.Source.dense.id.«nautil:bit»
end id

abbrev sk (s : statement) : statement := .Ssequence .Sskip s
abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint
abbrev pv (x : Common.AST.ident) : expr := .Etempvar x (tptr tulong)

/-- `EMPTYSET(active, m)`: clear the words from the end. -/
abbrev clear : statement :=
  .Ssequence
    (sk (.Sset id.es (.Ebinop .Oadd (.Ecast (pv id.active) (tptr tulong)) (tv id.m) (tptr tulong))))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Ogt (pv id.es) (.Ecast (pv id.active) (tptr tulong)) tint)
          .Sskip .Sbreak))
        (.Ssequence
          (.Ssequence
            (sk (.Sset id.t1 (.Ecast (.Ebinop .Osub (pv id.es) (ci 1 tint) (tptr tulong)) (tptr tulong))))
            (.Sset id.es (pv id.t1)))
          (.Sassign (.Ederef (pv id.t1) tulong) (ci 0 tint))))
      .Sskip)

/-- `active[tc >> 6]`. -/
abbrev activeWord : expr :=
  .Ederef (.Ebinop .Oadd (pv id.active) (.Ebinop .Oshr (tv id.tc) (ci 6 tint) tint) (tptr tulong))
    tulong

/-- `ADDELEMENT(active, tc)`. -/
abbrev add : statement :=
  sk (.Sassign activeWord
    (.Ebinop .Oor activeWord
      (.Ederef (.Ebinop .Oadd (.Evar id.bit (tarray tulong 64))
        (.Ebinop .Oand (tv id.tc) (ci 63 tint) tint) (tptr tulong)) tulong) tulong))

/-- `lab[e]`. -/
abbrev labAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.lab (tptr tint)) e (tptr tint)) tint

/-- `do { next = lab[i]; lab[i++] = prev; prev = next; } while (prev != tv);` -/
abbrev rotate : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sset id.next (labAt (tv id.i))))
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk (.Sset id.t2 (tv id.i)))
            (.Sset id.i (.Ebinop .Oadd (tv id.t2) (ci 1 tint) tint)))
          (.Sassign (labAt (tv id.t2)) (tv id.prev)))
        (sk (.Sset id.prev (tv id.next)))))
    (sk (.Sifthenelse (.Ebinop .One (tv id.prev) (tv id.tv) tint) .Sskip .Sbreak))

abbrev body : statement :=
  .Ssequence clear
    (.Ssequence add
      (.Ssequence (sk (.Sset id.i (tv id.tc)))
        (.Ssequence (sk (.Sset id.prev (tv id.tv)))
          (.Ssequence rotate
            (sk (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar id.ptn (tptr tint)) (tv id.tc) (tptr tint))
              tint) (tv id.level)))))))

kernel_rfl body_eq : NautyVerified.Source.dense.body.breakout = body

end NautyVerified.Proofs.Breakout

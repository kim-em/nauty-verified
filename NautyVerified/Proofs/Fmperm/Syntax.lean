import NautyVerified.Proofs.Alloc.Dyn
import NautyVerified.Proofs.Set.Syntax
import NautyVerified.Logic.For

/-!
# `fmperm`, factored

The Clight of nauty's `fmperm` (nautil.c), in named pieces; `body_eq` pins it
to `dense.body.fmperm`.
-/

namespace NautyVerified.Proofs.Fmperm

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Proofs.Set

namespace id
abbrev perm : Common.AST.ident := dense.id.perm
abbrev fix : Common.AST.ident := dense.id.fix
abbrev mcr : Common.AST.ident := dense.id.mcr
abbrev m : Common.AST.ident := dense.id.m
abbrev n : Common.AST.ident := dense.id.n
abbrev i : Common.AST.ident := dense.id.i
abbrev k : Common.AST.ident := dense.id.k
abbrev l : Common.AST.ident := dense.id.l
abbrev es : Common.AST.ident := dense.id.es_
abbrev es1 : Common.AST.ident := dense.id.«es___1»
abbrev wp : Common.AST.ident := dense.id.«nautil:workperm»
abbrev wsz : Common.AST.ident := dense.id.«nautil:workperm_sz»
abbrev msg : Common.AST.ident := dense.id.«nautil:__stringlit_1»
abbrev t1 : Common.AST.ident := idOf 703
abbrev t2 : Common.AST.ident := idOf 704
abbrev t3 : Common.AST.ident := idOf 705
abbrev t4 : Common.AST.ident := idOf 706
abbrev t5 : Common.AST.ident := idOf 707
end id

abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint

/-- `workperm[e]`. -/
abbrev wpAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar id.wp (tptr tint)) e (tptr tint)) tint

/-- `perm[e]`. -/
abbrev permAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.perm (tptr tint)) e (tptr tint)) tint

/-- `for (i = n; --i >= 0;) workperm[i] = 0;` -/
abbrev clearWp : statement :=
  .Ssequence (sk (.Sset id.i (tv id.n)))
    (.Sloop
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk (.Sset id.t5 (.Ecast (.Ebinop .Osub (tv id.i) (ci 1 tint) tint) tint)))
            (.Sset id.i (tv id.t5)))
          (.Sifthenelse (.Ebinop .Oge (tv id.t5) (ci 0 tint) tint) .Sskip .Sbreak))
        (sk (.Sassign (wpAt (tv id.i)) (ci 0 tint))))
      .Sskip)


/-- `l = i; do { k = l; l = perm[l]; workperm[k] = 1; } while (l != i);` then
`ADDELEMENT(mcr, i)`. -/
abbrev cycle : statement :=
  .Ssequence (sk (.Sset id.l (tv id.i)))
    (.Ssequence
      (.Sloop
        (.Ssequence (sk (.Sset id.k (tv id.l)))
          (.Ssequence (sk (.Sset id.l (permAt (tv id.l))))
            (sk (.Sassign (wpAt (tv id.k)) (ci 1 tint)))))
        (sk (.Sifthenelse (.Ebinop .One (tv id.l) (tv id.i) tint) .Sskip .Sbreak)))
      (addElement id.mcr (tv id.i)))

/-- The body of the main loop, for vertex `i`. -/
abbrev step : statement :=
  sk (.Sifthenelse (.Ebinop .Oeq (permAt (tv id.i)) (tv id.i) tint)
    (.Ssequence (addElement id.fix (tv id.i)) (addElement id.mcr (tv id.i)))
    (sk (.Sifthenelse (.Ebinop .Oeq (wpAt (tv id.i)) (ci 0 tint) tint) cycle .Sskip)))

abbrev body : statement :=
  .Ssequence (Alloc.dynalloc1 id.wsz id.wp tint (tv id.n) id.t1 id.t2 id.msg 10)
    (.Ssequence (emptySet id.fix id.m id.es id.t3)
      (.Ssequence (emptySet id.mcr id.m id.es1 id.t4)
        (.Ssequence clearWp (NautyVerified.Logic.forLoop id.i id.n step))))

kernel_rfl body_eq : dense.body.fmperm = body

end NautyVerified.Proofs.Fmperm

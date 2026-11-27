import NautyVerified.Proofs.Set.Syntax

/-!
# `fmptn`, factored

The Clight of nauty's `fmptn` (nautil.c), in named pieces; `body_eq` pins it
to `dense.body.fmptn`.
-/

namespace NautyVerified.Proofs.Fmptn

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Proofs.Set

namespace id
abbrev lab : Common.AST.ident := dense.id.lab
abbrev ptn : Common.AST.ident := dense.id.ptn
abbrev level : Common.AST.ident := dense.id.level
abbrev fix : Common.AST.ident := dense.id.fix
abbrev mcr : Common.AST.ident := dense.id.mcr
abbrev m : Common.AST.ident := dense.id.m
abbrev n : Common.AST.ident := dense.id.n
abbrev i : Common.AST.ident := dense.id.i
abbrev lmin : Common.AST.ident := dense.id.lmin
abbrev es : Common.AST.ident := dense.id.es_
abbrev es1 : Common.AST.ident := dense.id.«es___1»
abbrev t1 : Common.AST.ident := idOf 703
abbrev t2 : Common.AST.ident := idOf 704
abbrev t3 : Common.AST.ident := idOf 705
end id

abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint

/-- `p[e]` for an `int *` temporary `p`. -/
abbrev at_ (p : Common.AST.ident) (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar p (tptr tint)) e (tptr tint)) tint

/-- A trivial cell: `ADDELEMENT(fix, lab[i]); ADDELEMENT(mcr, lab[i]);` -/
abbrev single : statement :=
  .Ssequence (addElement id.fix (at_ id.lab (tv id.i))) (addElement id.mcr (at_ id.lab (tv id.i)))

/-- `do if (lab[++i] < lmin) lmin = lab[i]; while (ptn[i] > level);` -/
abbrev scan : statement :=
  .Sloop
    (.Ssequence
      (.Ssequence
        (sk (.Sset id.t3 (.Ecast (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint) tint)))
        (.Sset id.i (tv id.t3)))
      (.Sifthenelse (.Ebinop .Olt (at_ id.lab (tv id.t3)) (tv id.lmin) tint)
        (sk (.Sset id.lmin (at_ id.lab (tv id.i))))
        .Sskip))
    (sk (.Sifthenelse (.Ebinop .Ogt (at_ id.ptn (tv id.i)) (tv id.level) tint) .Sskip .Sbreak))

/-- A nontrivial cell: find its least vertex and add it to `mcr`. -/
abbrev cell : statement :=
  .Ssequence (sk (.Sset id.lmin (at_ id.lab (tv id.i))))
    (.Ssequence scan (addElement id.mcr (tv id.lmin)))

/-- The outer loop, from `i = 0`. -/
abbrev loop : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak))
      (sk (.Sifthenelse (.Ebinop .Ole (at_ id.ptn (tv id.i)) (tv id.level) tint) single cell)))
    (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint)))

abbrev body : statement :=
  .Ssequence (emptySet id.fix id.m id.es id.t1)
    (.Ssequence (emptySet id.mcr id.m id.es1 id.t2)
      (.Ssequence (sk (.Sset id.i (ci 0 tint))) loop))

kernel_rfl body_eq : NautyVerified.Source.dense.body.fmptn = body

end NautyVerified.Proofs.Fmptn

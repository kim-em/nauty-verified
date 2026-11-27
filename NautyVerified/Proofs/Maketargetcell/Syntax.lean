import NautyVerified.Proofs.Targetcell.Syntax

/-!
# `maketargetcell`, factored

The Clight of nautil.c's `maketargetcell`, in named pieces; `body_eq` pins it
to `dense.body.maketargetcell`. `targetcell` is called through the function
pointer argument.
-/

namespace NautyVerified.Proofs.Maketargetcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv)
open NautyVerified.Proofs.Updatecan (tv labAt)
open NautyVerified.Proofs.Bestcell (ptnAt)

namespace id
abbrev g : Common.AST.ident := dense.id.g
abbrev lab : Common.AST.ident := dense.id.lab
abbrev ptn : Common.AST.ident := dense.id.ptn
abbrev level : Common.AST.ident := dense.id.level
abbrev tcell : Common.AST.ident := dense.id.tcell
abbrev tcellsize : Common.AST.ident := dense.id.tcellsize
abbrev cellpos : Common.AST.ident := dense.id.cellpos
abbrev tc_level : Common.AST.ident := dense.id.tc_level
abbrev digraph : Common.AST.ident := dense.id.digraph
abbrev hint : Common.AST.ident := dense.id.hint
abbrev targetcell : Common.AST.ident := dense.id.targetcell
abbrev m : Common.AST.ident := dense.id.m
abbrev n : Common.AST.ident := dense.id.n
abbrev i : Common.AST.ident := dense.id.i
abbrev j : Common.AST.ident := dense.id.j
abbrev k : Common.AST.ident := dense.id.k
abbrev es : Common.AST.ident := dense.id.es_
abbrev t3 : Common.AST.ident := idOf 703
abbrev t4 : Common.AST.ident := idOf 704
end id

/-- The type of `targetcell`. -/
abbrev tcType : Cfrontend.Ctypes.type :=
  tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tint, tint, tint] tint

/-- `i = (*targetcell)(g, lab, ptn, level, tc_level, digraph, hint, m, n);` -/
abbrev call : statement :=
  .Ssequence
    (sk (.Scall (some id.t3) (.Ederef (.Etempvar id.targetcell (tptr tcType)) tcType)
      [.Etempvar id.g (tptr tulong), .Etempvar id.lab (tptr tint), .Etempvar id.ptn (tptr tint),
        tv id.level, tv id.tc_level, tv id.digraph, tv id.hint, tv id.m, tv id.n]))
    (.Sset id.i (tv id.t3))

/-- `for (j = i + 1; ptn[j] > level; ++j) {}` -/
abbrev jloop : statement :=
  .Ssequence (sk (.Sset id.j (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Ogt (ptnAt (tv id.j)) (tv id.level) tint) .Sskip .Sbreak))
        .Sskip)
      (sk (.Sset id.j (.Ebinop .Oadd (tv id.j) (ci 1 tint) tint))))

/-- `*tcellsize = j - i + 1;` -/
abbrev size : statement :=
  sk (.Sassign (.Ederef (.Etempvar id.tcellsize (tptr tint)) tint)
    (.Ebinop .Oadd (.Ebinop .Osub (tv id.j) (tv id.i) tint) (ci 1 tint) tint))

/-- `for (k = i; k <= j; ++k) ADDELEMENT(tcell, lab[k]);` -/
abbrev kloop : statement :=
  .Ssequence (sk (.Sset id.k (tv id.i)))
    (.Sloop
      (.Ssequence (sk (.Sifthenelse (.Ebinop .Ole (tv id.k) (tv id.j) tint) .Sskip .Sbreak))
        (Set.addElement id.tcell (labAt (tv id.k))))
      (sk (.Sset id.k (.Ebinop .Oadd (tv id.k) (ci 1 tint) tint))))

/-- `*cellpos = i;` -/
abbrev pos : statement :=
  sk (.Sassign (.Ederef (.Etempvar id.cellpos (tptr tint)) tint) (tv id.i))

abbrev body : statement :=
  .Ssequence call
    (.Ssequence jloop
      (.Ssequence size
        (.Ssequence (Set.emptySet id.tcell id.m id.es id.t4)
          (.Ssequence kloop pos))))

kernel_rfl body_eq : dense.body.maketargetcell = body

end NautyVerified.Proofs.Maketargetcell

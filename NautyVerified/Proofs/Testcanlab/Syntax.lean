import NautyVerified.Proofs.Updatecan.Syntax

/-!
# `testcanlab`, factored

The Clight of nauty's `testcanlab` (naugraph.c), in named pieces; `body_eq`
pins it to `dense.body.testcanlab`. The inverse-permutation loop is
`Updatecan.inv`, statement for statement.
-/

namespace NautyVerified.Proofs.Testcanlab

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv)
open NautyVerified.Proofs.Updatecan (tv labAt row)

namespace id
abbrev g : Common.AST.ident := dense.id.g
abbrev canong : Common.AST.ident := dense.id.canong
abbrev samerows : Common.AST.ident := dense.id.samerows
abbrev m : Common.AST.ident := dense.id.m
abbrev n : Common.AST.ident := dense.id.n
abbrev i : Common.AST.ident := dense.id.i
abbrev j : Common.AST.ident := dense.id.j
abbrev ph : Common.AST.ident := dense.id.ph
abbrev wp : Common.AST.ident := dense.id.«naugraph:workperm»
abbrev wsz : Common.AST.ident := dense.id.«naugraph:workperm_sz»
abbrev ws : Common.AST.ident := dense.id.«naugraph:workset»
abbrev wssz : Common.AST.ident := dense.id.«naugraph:workset_sz»
abbrev msg : Common.AST.ident := dense.id.«naugraph:__stringlit_1»
abbrev t1 : Common.AST.ident := idOf 703
abbrev t2 : Common.AST.ident := idOf 704
abbrev t3 : Common.AST.ident := idOf 705
abbrev t4 : Common.AST.ident := idOf 706
end id

/-- `workset[j]` and `ph[j]`. -/
abbrev wsAt : expr :=
  .Ederef (.Ebinop .Oadd (.Evar id.ws (tptr tulong)) (tv id.j) (tptr tulong)) tulong
abbrev phAt : expr :=
  .Ederef (.Ebinop .Oadd (pv id.ph) (tv id.j) (tptr tulong)) tulong

/-- `*samerows = i; return r;` -/
abbrev stop (r : expr) : statement :=
  .Ssequence (sk (.Sassign (.Ederef (.Etempvar id.samerows (tptr tint)) tint) (tv id.i)))
    (sk (.Sreturn (some r)))

/-- `for (j = 0; j < M; ++j) if (workset[j] < ph[j]) … else if (workset[j] > ph[j]) …` -/
abbrev cmp : statement :=
  NautyVerified.Logic.forLoop id.j id.m
    (sk (.Sifthenelse (.Ebinop .Olt wsAt phAt tint) (stop (.Eunop .Oneg (ci 1 tint) tint))
      (sk (.Sifthenelse (.Ebinop .Ogt wsAt phAt tint) (stop (ci 1 tint)) .Sskip))))

abbrev rows : statement :=
  .Ssequence
    (.Ssequence (sk (.Sset id.i (ci 0 tint))) (.Sset id.ph (pv id.canong)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak))
        (.Ssequence
          (sk (.Scall none (.Evar dense.id.permset (tfun [tptr tulong, tptr tulong, tint, tptr tint] .Tvoid))
            [row id.g (labAt (tv id.i)), .Evar id.ws (tptr tulong), tv id.m, .Evar id.wp (tptr tint)]))
          cmp))
      (.Ssequence (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint)))
        (.Sset id.ph (.Ebinop .Oadd (pv id.ph) (tv id.m) (tptr tulong)))))

abbrev final : statement :=
  .Ssequence (sk (.Sassign (.Ederef (.Etempvar id.samerows (tptr tint)) tint) (tv id.n)))
    (sk (.Sreturn (some (ci 0 tint))))

abbrev body : statement :=
  .Ssequence (Alloc.dynalloc1 id.wsz id.wp tint (tv id.n) id.t1 id.t2 id.msg 11)
    (.Ssequence (Alloc.dynalloc1 id.wssz id.ws tulong (tv id.m) id.t3 id.t4 id.msg 11)
      (.Ssequence Updatecan.inv (.Ssequence rows final)))

kernel_rfl body_eq : dense.body.testcanlab = body

end NautyVerified.Proofs.Testcanlab

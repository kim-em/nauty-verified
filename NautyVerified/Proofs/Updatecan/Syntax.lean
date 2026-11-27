import NautyVerified.Proofs.Alloc.Dyn
import NautyVerified.Proofs.Set.Syntax
import NautyVerified.Proofs.Alloc.Global
import NautyVerified.Logic.For

/-!
# `updatecan`, factored

The Clight of nauty's `updatecan` (naugraph.c), in named pieces; `body_eq`
pins it to `dense.body.updatecan`.
-/

namespace NautyVerified.Proofs.Updatecan

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv)

namespace id
abbrev g : Common.AST.ident := dense.id.g
abbrev canong : Common.AST.ident := dense.id.canong
abbrev lab : Common.AST.ident := dense.id.lab
abbrev samerows : Common.AST.ident := dense.id.samerows
abbrev m : Common.AST.ident := dense.id.m
abbrev n : Common.AST.ident := dense.id.n
abbrev i : Common.AST.ident := dense.id.i
abbrev ph : Common.AST.ident := dense.id.ph
abbrev wp : Common.AST.ident := dense.id.«naugraph:workperm»
abbrev wsz : Common.AST.ident := dense.id.«naugraph:workperm_sz»
abbrev msg : Common.AST.ident := dense.id.«naugraph:__stringlit_2»
abbrev t1 : Common.AST.ident := idOf 703
abbrev t2 : Common.AST.ident := idOf 704
end id

abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint

/-- `lab[e]`. -/
abbrev labAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.lab (tptr tint)) e (tptr tint)) tint

/-- `GRAPHROW(p, e, M)`. -/
abbrev row (p : Common.AST.ident) (e : expr) : expr :=
  .Ebinop .Oadd (.Ecast (pv p) (tptr tulong)) (.Ebinop .Omul (tv id.m) (.Ecast e tulong) tulong) (tptr tulong)

/-- `for (i = 0; i < n; ++i) workperm[lab[i]] = i;` -/
abbrev inv : statement :=
  NautyVerified.Logic.forLoop id.i id.n
    (sk (.Sassign (Alloc.gat id.wp (labAt (tv id.i))) (tv id.i)))

/-- `for (i = samerows, ph = GRAPHROW(canong, samerows, M); i < n; ++i, ph += M) permset(...);` -/
abbrev rows : statement :=
  .Ssequence
    (.Ssequence (sk (.Sset id.i (tv id.samerows))) (.Sset id.ph (row id.canong (tv id.samerows))))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak))
        (sk (.Scall none (.Evar dense.id.permset (tfun [tptr tulong, tptr tulong, tint, tptr tint] .Tvoid))
          [row id.g (labAt (tv id.i)), pv id.ph, tv id.m, .Evar id.wp (tptr tint)])))
      (.Ssequence (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint)))
        (.Sset id.ph (.Ebinop .Oadd (pv id.ph) (tv id.m) (tptr tulong)))))

abbrev body : statement :=
  .Ssequence (Alloc.dynalloc1 id.wsz id.wp tint (tv id.n) id.t1 id.t2 id.msg 10)
    (.Ssequence inv rows)

kernel_rfl body_eq : dense.body.updatecan = body

end NautyVerified.Proofs.Updatecan

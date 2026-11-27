import NautyVerified.Proofs.Set.Elem

/-!
# `isautom`, factored

The Clight of nauty's `isautom` (naugraph.c), in named pieces; `body_eq` pins
it to `dense.body.isautom`.
-/

namespace NautyVerified.Proofs.Isautom

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv isElement)

namespace id
abbrev g : Common.AST.ident := dense.id.g
abbrev perm : Common.AST.ident := dense.id.perm
abbrev digraph : Common.AST.ident := dense.id.digraph
abbrev m : Common.AST.ident := dense.id.m
abbrev n : Common.AST.ident := dense.id.n
abbrev pg : Common.AST.ident := dense.id.pg
abbrev pos : Common.AST.ident := dense.id.pos
abbrev pgp : Common.AST.ident := dense.id.pgp
abbrev posp : Common.AST.ident := dense.id.posp
abbrev i : Common.AST.ident := dense.id.i
abbrev t1 : Common.AST.ident := idOf 703
abbrev t2 : Common.AST.ident := idOf 704
abbrev t3 : Common.AST.ident := idOf 705
abbrev bit : Common.AST.ident := dense.id.«naugraph:bit»
end id

abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint

/-- `perm[e]`. -/
abbrev permAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.perm (tptr tint)) e (tptr tint)) tint

/-- `while ((pos = nextelement(pg, M, pos)) >= 0) { posp = perm[pos]; if (!ISELEMENT(pgp, posp)) return FALSE; }` -/
abbrev scan : statement :=
  .Sloop
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk (.Scall (some id.t2) (.Evar dense.id.nextelement (tfun [tptr tulong, tint, tint] tint))
              [pv id.pg, tv id.m, tv id.pos]))
            (.Sset id.t3 (.Ecast (tv id.t2) tint)))
          (.Sset id.pos (tv id.t3)))
        (.Sifthenelse (.Ebinop .Oge (tv id.t3) (ci 0 tint) tint) .Sskip .Sbreak))
      (.Ssequence (sk (.Sset id.posp (permAt (tv id.pos))))
        (sk (.Sifthenelse (.Eunop .Onotbool (isElement id.pgp id.bit (tv id.posp)) tint)
          (sk (.Sreturn (some (ci 0 tint)))) .Sskip))))
    .Sskip

/-- One row: set `pgp` to row `perm[i]`, start at `pos = i`, scan. -/
abbrev row : statement :=
  .Ssequence
    (sk (.Sset id.pgp (.Ebinop .Oadd (.Ecast (pv id.g) (tptr tulong))
      (.Ebinop .Omul (tv id.m) (.Ecast (permAt (tv id.i)) tulong) tulong) (tptr tulong))))
    (.Ssequence
      (.Ssequence
        (sk (.Sifthenelse (tv id.digraph)
          (sk (.Sset id.t1 (.Ecast (.Eunop .Oneg (ci 1 tint) tint) tint)))
          (sk (.Sset id.t1 (.Ecast (tv id.i) tint)))))
        (.Sset id.pos (tv id.t1)))
      scan)

abbrev body : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence (sk (.Sset id.pg (pv id.g))) (.Sset id.i (ci 0 tint)))
      (.Sloop
        (.Ssequence (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak)) row)
        (.Ssequence (sk (.Sset id.pg (.Ebinop .Oadd (pv id.pg) (tv id.m) (tptr tulong))))
          (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint)))))
    (sk (.Sreturn (some (ci 1 tint))))

kernel_rfl body_eq : dense.body.isautom = body

end NautyVerified.Proofs.Isautom

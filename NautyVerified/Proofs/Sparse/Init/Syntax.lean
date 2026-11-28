import NautyVerified.Proofs.Alloc.DynF
import NautyVerified.Proofs.Sparse.Graph

/-!
# `init_sg`, factored

The Clight of nausparse.c's `init_sg` in named pieces; `body_eq` pins it to
`sparse.body.init_sg`. `sgAlloc` is `SG_ALLOC(*sh, sg->nv, sg->nde,
"init_sg")`: a `do { ... } while (0)` around three `DYNALLOC1`s on the
fields of `*sh`.
-/

namespace NautyVerified.Proofs.Sparse.Init

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Alloc (fld dynalloc1F sk)

namespace id
abbrev gin : Common.AST.ident := sparse.id.gin
abbrev hin : Common.AST.ident := sparse.id.hin
abbrev options : Common.AST.ident := sparse.id.options
abbrev status : Common.AST.ident := sparse.id.status
abbrev sg : Common.AST.ident := sparse.id.sg
abbrev sh : Common.AST.ident := sparse.id.sh
abbrev sid : Common.AST.ident := sparse.id.«_1406»
abbrev msg : Common.AST.ident := sparse.id.«nausparse:__stringlit_4»
end id

/-- `SG_ALLOC(*sh, sg->nv, sg->nde, "init_sg")`. -/
abbrev sgAlloc : statement :=
  .Sloop
    (.Ssequence
      (dynalloc1F id.sh id.sid sparse.id.v sparse.id.vlen tulong (fld id.sg id.sid sparse.id.nv tint)
        (idOf 703) (idOf 704) id.msg 8)
      (.Ssequence
        (dynalloc1F id.sh id.sid sparse.id.d sparse.id.dlen tint (fld id.sg id.sid sparse.id.nv tint)
          (idOf 705) (idOf 706) id.msg 8)
        (dynalloc1F id.sh id.sid sparse.id.e sparse.id.elen tint (fld id.sg id.sid sparse.id.nde tulong)
          (idOf 707) (idOf 708) id.msg 8)))
    (sk .Sbreak)

/-- `sh->nv = sg->nv; sh->nde = sg->nde;` -/
abbrev copyCounts : statement :=
  .Ssequence
    (sk (.Sassign (fld id.sh id.sid sparse.id.nv tint) (fld id.sg id.sid sparse.id.nv tint)))
    (sk (.Sassign (fld id.sh id.sid sparse.id.nde tulong) (fld id.sg id.sid sparse.id.nde tulong)))

/-- The `getcanon` branch. -/
abbrev canonBranch : statement :=
  .Ssequence (sk (.Sset id.sg (.Ecast (.Etempvar id.gin (tptr tulong)) (tptr sgTy))))
    (.Ssequence (sk (.Sset id.sh (.Ecast (.Etempvar id.hin (tptr tulong)) (tptr sgTy))))
      (.Ssequence sgAlloc copyCounts))

abbrev body : statement :=
  .Ssequence
    (sk (.Sifthenelse (fld id.options sparse.id.optionstruct sparse.id.getcanon tint) canonBranch .Sskip))
    (sk (.Sassign (.Ederef (.Etempvar id.status (tptr tint)) tint) (ci 0 tint)))

kernel_rfl body_eq : sparse.body.init_sg = body

end NautyVerified.Proofs.Sparse.Init

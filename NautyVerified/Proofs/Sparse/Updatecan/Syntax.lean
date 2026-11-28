import NautyVerified.Proofs.Sparse.Testcanlab.Syntax

/-!
# `updatecan_sg`, factored

The Clight of nausparse.c's `updatecan_sg`, in named pieces; `body_eq` pins
it to `sparse.body.updatecan_sg`.
-/

namespace NautyVerified.Proofs.Sparse.Updatecan

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat)
open NautyVerified.Proofs.Sparse.Testcanlab (wat iloop scatter)

namespace id
abbrev g : Common.AST.ident := sparse.id.g
abbrev canong : Common.AST.ident := sparse.id.canong
abbrev lab : Common.AST.ident := sparse.id.lab
abbrev samerows : Common.AST.ident := sparse.id.samerows
abbrev m : Common.AST.ident := sparse.id.m
abbrev n : Common.AST.ident := sparse.id.n
abbrev v : Common.AST.ident := sparse.id.v
abbrev d : Common.AST.ident := sparse.id.d
abbrev e : Common.AST.ident := sparse.id.e
abbrev cv : Common.AST.ident := sparse.id.cv
abbrev cd : Common.AST.ident := sparse.id.cd
abbrev ce : Common.AST.ident := sparse.id.ce
abbrev i : Common.AST.ident := sparse.id.i
abbrev k : Common.AST.ident := sparse.id.k
abbrev dli : Common.AST.ident := sparse.id.dli
abbrev j : Common.AST.ident := sparse.id.j
abbrev vli : Common.AST.ident := sparse.id.vli
abbrev work1 : Common.AST.ident := sparse.id.«nausparse:work1»
abbrev work1Sz : Common.AST.ident := sparse.id.«nausparse:work1_sz»
abbrev wt : Common.AST.ident := sparse.id.wt
abbrev cwt : Common.AST.ident := sparse.id.cwt
abbrev t1 : Common.AST.ident := idOf 705
abbrev t2 : Common.AST.ident := idOf 706
end id

/-- `SWG_VDE(p, v, d, e, w)`. -/
abbrev vdew (p v d e w : Common.AST.ident) : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sset v (sgField p sparse.id.v (tptr tulong))))
      (.Ssequence
        (sk (.Sset d (sgField p sparse.id.d (tptr tint))))
        (.Ssequence
          (sk (.Sset e (sgField p sparse.id.e (tptr tint))))
          (sk (.Sset w (sgField p sparse.id.w (tptr tint)))))))
    (sk .Sbreak)

/-- `for (j = 0; j < dli; ++j) <s>`. -/
abbrev jloop (s : statement) : statement :=
  .Ssequence
    (sk (.Sset id.j (.Ecast (ci 0 tint) tulong)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tl id.j) (tv id.dli) tint) .Sskip .Sbreak))
        s)
      (sk (.Sset id.j (.Ebinop .Oadd (tl id.j) (ci 1 tint) tulong))))

/-- `INVLAB[e[vli+j]]`. -/
abbrev invat : expr := wat (iat id.e (.Ebinop .Oadd (tl id.vli) (tl id.j) tulong))

/-- The weighted copy, not taken (`wt` is `NULL`). -/
abbrev wcopy : statement :=
  jloop
    (.Ssequence
      (sk (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar id.ce (tptr tint)) (tl id.k) (tptr tint)) tint) invat))
      (.Ssequence
        (sk (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar id.cwt (tptr tint)) (tl id.k) (tptr tint)) tint)
          (iat id.wt (.Ebinop .Oadd (tl id.vli) (tl id.j) tulong))))
        (sk (.Sset id.k (.Ebinop .Oadd (tl id.k) (ci 1 tint) tulong)))))

/-- `ce[k++] = INVLAB[e[vli+j]]`. -/
abbrev copyBody : statement :=
  .Ssequence
    (.Ssequence (sk (.Sset id.t2 (tl id.k)))
      (.Sset id.k (.Ebinop .Oadd (.Etempvar id.t2 tulong) (ci 1 tint) tulong)))
    (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar id.ce (tptr tint)) (.Etempvar id.t2 tulong) (tptr tint)) tint)
      invat)

/-- The body of the loop over rows from `samerows`. -/
abbrev row : statement :=
  .Ssequence (sk (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar id.cv (tptr tulong)) (tv id.i) (tptr tulong)) tulong)
      (tl id.k)))
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (sk (.Sset id.t1 (.Ecast (iat id.d (iat id.lab (tv id.i))) tint)))
          (.Sset id.dli (.Etempvar id.t1 tint)))
        (.Sassign (iat id.cd (tv id.i)) (.Etempvar id.t1 tint)))
      (.Ssequence
        (sk (.Sset id.vli (lat id.v (iat id.lab (tv id.i)))))
        (sk (.Sifthenelse (.Etempvar id.wt (tptr tint)) wcopy (jloop copyBody)))))

/-- `canong->f = x`. -/
abbrev setField (f : Common.AST.ident) (ty : Cfrontend.Ctypes.type) (x : expr) : statement :=
  sk (.Sassign (sgField id.canong f ty) x)

/-- `k = samerows == 0 ? 0 : cv[samerows-1] + cd[samerows-1]`. -/
abbrev setK : statement :=
  sk (.Sifthenelse (.Ebinop .Oeq (tv id.samerows) (ci 0 tint) tint)
    (sk (.Sset id.k (.Ecast (ci 0 tint) tulong)))
    (sk (.Sset id.k (.Ebinop .Oadd
      (lat id.cv (.Ebinop .Osub (tv id.samerows) (ci 1 tint) tint))
      (iat id.cd (.Ebinop .Osub (tv id.samerows) (ci 1 tint) tint)) tulong))))

/-- `for (i = samerows; i < n; ++i) row`. -/
abbrev rows : statement :=
  .Ssequence
    (sk (.Sset id.i (tv id.samerows)))
    (.Sloop
      (.Ssequence (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak)) row)
      (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))))

abbrev body : statement :=
  .Ssequence (vdew id.g id.v id.d id.e id.wt)
    (.Ssequence (vdew id.canong id.cv id.cd id.ce id.cwt)
      (.Ssequence
        (Alloc.dynalloc1 id.work1Sz id.work1 tint (tv id.n) (idOf 703) (idOf 704)
          sparse.id.«nausparse:__stringlit_2» 14)
        (.Ssequence (setField sparse.id.nv tint (tv id.n))
          (.Ssequence (setField sparse.id.nde tulong (sgField id.g sparse.id.nde tulong))
            (.Ssequence (iloop scatter)
              (.Ssequence setK rows))))))

kernel_rfl body_eq : sparse.body.updatecan_sg = body

end NautyVerified.Proofs.Sparse.Updatecan

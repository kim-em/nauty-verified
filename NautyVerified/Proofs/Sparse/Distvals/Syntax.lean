import NautyVerified.Proofs.Sparse.Testcanlab.Syntax
import NautyVerified.Proofs.Sparse.Freedyn

/-!
# `distvals`, factored

The Clight of nausparse.c's `distvals`, in named pieces; `body_eq` pins it
to `sparse.body.distvals`.
-/

namespace NautyVerified.Proofs.Sparse.Distvals

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat)

namespace id
abbrev g : Common.AST.ident := sparse.id.g
abbrev v0 : Common.AST.ident := sparse.id.v0
abbrev dist : Common.AST.ident := sparse.id.dist
abbrev n : Common.AST.ident := sparse.id.n
abbrev v : Common.AST.ident := sparse.id.v
abbrev d : Common.AST.ident := sparse.id.d
abbrev e : Common.AST.ident := sparse.id.e
abbrev i : Common.AST.ident := sparse.id.i
abbrev head : Common.AST.ident := sparse.id.head
abbrev tail : Common.AST.ident := sparse.id.tail
abbrev di : Common.AST.ident := sparse.id.di
abbrev k : Common.AST.ident := sparse.id.k
abbrev vi : Common.AST.ident := sparse.id.vi
abbrev j : Common.AST.ident := sparse.id.j
abbrev work4 : Common.AST.ident := sparse.id.«nausparse:work4»
abbrev work4Sz : Common.AST.ident := sparse.id.«nausparse:work4_sz»
abbrev t1 : Common.AST.ident := idOf 705
abbrev t2 : Common.AST.ident := idOf 706
abbrev t3 : Common.AST.ident := idOf 707
end id

/-- `p->f` for a `sparsegraph *p` (`SG_VDE` casts it to its own type). -/
abbrev sgFieldS (p : Common.AST.ident) (f : Common.AST.ident) (ty : Cfrontend.Ctypes.type) : expr :=
  .Efield (.Ederef (.Ecast (.Etempvar p (tptr sgTy)) (tptr sgTy)) sgTy) f ty

/-- `SG_VDE(g, v, d, e)` for a `sparsegraph *g`. -/
abbrev vde : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sset id.v (sgFieldS id.g sparse.id.v (tptr tulong))))
      (.Ssequence
        (sk (.Sset id.d (sgFieldS id.g sparse.id.d (tptr tint))))
        (sk (.Sset id.e (sgFieldS id.g sparse.id.e (tptr tint))))))
    (sk .Sbreak)

/-- `QUEUE[a]`. -/
abbrev qat (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar id.work4 (tptr tint)) a (tptr tint)) tint

/-- `dist[a]`. -/
abbrev dat (a : expr) : expr := iat id.dist a

/-- `for (i = 0; i < n; ++i) dist[i] = n;` -/
abbrev fill : statement :=
  .Ssequence
    (sk (.Sset id.i (ci 0 tint)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak))
        (sk (.Sassign (dat (tv id.i)) (tv id.n))))
      (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))))

/-- `k = e[vi+j]; if (dist[k] == n) { dist[k] = dist[i] + 1; QUEUE[tail++] = k; }` -/
abbrev edgeBody : statement :=
  .Ssequence
    (sk (.Sset id.k (iat id.e (.Ebinop .Oadd (tl id.vi) (tl id.j) tulong))))
    (sk (.Sifthenelse (.Ebinop .Oeq (dat (tv id.k)) (tv id.n) tint)
      (.Ssequence
        (sk (.Sassign (dat (tv id.k)) (.Ebinop .Oadd (dat (tv id.i)) (ci 1 tint) tint)))
        (.Ssequence
          (.Ssequence
            (sk (.Sset id.t3 (tv id.tail)))
            (.Sset id.tail (.Ebinop .Oadd (tv id.t3) (ci 1 tint) tint)))
          (.Sassign (qat (tv id.t3)) (tv id.k))))
      .Sskip))

/-- `for (j = 0; j < di; ++j) edgeBody` -/
abbrev edges : statement := Testcanlab.jloop edgeBody

/-- The test `tail < n && head < tail`. -/
abbrev test : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Ebinop .Olt (tv id.tail) (tv id.n) tint)
      (sk (.Sset id.t1 (.Ecast (.Ebinop .Olt (tv id.head) (tv id.tail) tint) tbool)))
      (.Sset id.t1 (ci 0 tint))))
    (.Sifthenelse (tv id.t1) .Sskip .Sbreak)

/-- `i = QUEUE[head++]; vi = v[i]; di = d[i]; edges` -/
abbrev step : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence
        (sk (.Sset id.t2 (tv id.head)))
        (.Sset id.head (.Ebinop .Oadd (tv id.t2) (ci 1 tint) tint)))
      (.Sset id.i (qat (tv id.t2))))
    (.Ssequence
      (sk (.Sset id.vi (lat id.v (tv id.i))))
      (.Ssequence
        (sk (.Sset id.di (iat id.d (tv id.i))))
        edges))

/-- `QUEUE[0] = v0; dist[v0] = 0; head = 0; tail = 1; while (...) step` -/
abbrev search : statement :=
  .Ssequence
    (sk (.Sassign (qat (ci 0 tint)) (tv id.v0)))
    (.Ssequence
      (sk (.Sassign (dat (tv id.v0)) (ci 0 tint)))
      (.Ssequence
        (sk (.Sset id.head (ci 0 tint)))
        (.Ssequence
          (sk (.Sset id.tail (ci 1 tint)))
          (.Sloop (.Ssequence test step) .Sskip))))

abbrev body : statement :=
  .Ssequence vde
    (.Ssequence
      (Alloc.dynalloc1 id.work4Sz id.work4 tint (tv id.n) (idOf 703) (idOf 704)
        sparse.id.«nausparse:__stringlit_5» 9)
      (.Ssequence fill search))

kernel_rfl body_eq : sparse.body.distvals = body

end NautyVerified.Proofs.Sparse.Distvals

import NautyVerified.Proofs.Sparse.Marks

/-!
# `isautom_sg`, factored

The Clight of nausparse.c's `isautom_sg`, in named pieces; `body_eq` pins it
to `sparse.body.isautom_sg`.
-/

namespace NautyVerified.Proofs.Sparse.Isautom

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Proofs.Sparse

namespace id
abbrev g : Common.AST.ident := sparse.id.g
abbrev p : Common.AST.ident := sparse.id.p
abbrev digraph : Common.AST.ident := sparse.id.digraph
abbrev m : Common.AST.ident := sparse.id.m
abbrev n : Common.AST.ident := sparse.id.n
abbrev v : Common.AST.ident := sparse.id.v
abbrev d : Common.AST.ident := sparse.id.d
abbrev e : Common.AST.ident := sparse.id.e
abbrev i : Common.AST.ident := sparse.id.i
abbrev pi : Common.AST.ident := sparse.id.pi
abbrev di : Common.AST.ident := sparse.id.di
abbrev vi : Common.AST.ident := sparse.id.vi
abbrev vpi : Common.AST.ident := sparse.id.vpi
abbrev j : Common.AST.ident := sparse.id.j
abbrev ij : Common.AST.ident := sparse.id.ij
abbrev t1 : Common.AST.ident := idOf 703
abbrev t2 : Common.AST.ident := idOf 704
end id

abbrev sk (s : statement) : statement := .Ssequence .Sskip s
abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint
abbrev tl (x : Common.AST.ident) : expr := .Etempvar x tulong

/-- `q[a]` for an `int *` temporary `q`. -/
abbrev iat (q : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar q (tptr tint)) a (tptr tint)) tint
/-- `v[a]`. -/
abbrev lat (q : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar q (tptr tulong)) a (tptr tulong)) tulong
/-- `vmark1[a]`. -/
abbrev mat (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar Sparse.id.vmark1 (tptr tshort)) a (tptr tshort)) tshort
/-- `e[x + j]`. -/
abbrev eat (x : Common.AST.ident) : expr :=
  iat id.e (.Ebinop .Oadd (tl x) (tl id.j) tulong)

/-- `SG_VDE(g, v, d, e)`. -/
abbrev vde : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sset id.v (sgField id.g sparse.id.v (tptr tulong))))
      (.Ssequence
        (sk (.Sset id.d (sgField id.g sparse.id.d (tptr tint))))
        (sk (.Sset id.e (sgField id.g sparse.id.e (tptr tint))))))
    (sk .Sbreak)

/-- `for (j = 0; j < di; ++j) <s>`. -/
abbrev jloop (s : statement) : statement :=
  .Ssequence
    (sk (.Sset id.j (.Ecast (ci 0 tint) tulong)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tl id.j) (tv id.di) tint) .Sskip .Sbreak))
        (sk s))
      (sk (.Sset id.j (.Ebinop .Oadd (tl id.j) (ci 1 tint) tulong))))

/-- `MARK1(p[e[vi+j]])`. -/
abbrev mark : statement :=
  .Sassign (mat (iat id.p (eat id.vi))) (.Evar Sparse.id.vmark1Val tshort)

/-- `if (ISNOTMARKED1(e[vpi+j])) return FALSE;` -/
abbrev check : statement :=
  .Sifthenelse (.Ebinop .One (mat (eat id.vpi)) (.Evar Sparse.id.vmark1Val tshort) tint)
    (sk (.Sreturn (some (ci 0 tint)))) .Sskip

/-- The body for a moved vertex `i`. -/
abbrev moved : statement :=
  .Ssequence (sk (.Sset id.pi (iat id.p (tv id.i))))
    (.Ssequence (sk (.Sset id.di (iat id.d (tv id.i))))
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .One (iat id.d (tv id.pi)) (tv id.di) tint)
          (sk (.Sreturn (some (ci 0 tint)))) .Sskip))
        (.Ssequence (sk (.Sset id.vi (lat id.v (tv id.i))))
          (.Ssequence (sk (.Sset id.vpi (lat id.v (tv id.pi))))
            (.Ssequence (resetmarks1 id.t1 id.ij)
              (.Ssequence (jloop mark) (jloop check)))))))

/-- The body of the loop over `i`. -/
abbrev row : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Ebinop .One (iat id.p (tv id.i)) (tv id.i) tint)
      (.Sset id.t2 (ci 1 tint))
      (sk (.Sset id.t2 (.Ecast (tv id.digraph) tbool)))))
    (.Sifthenelse (tv id.t2) moved .Sskip)

abbrev body : statement :=
  .Ssequence vde
    (.Ssequence
      (sk (.Scall none (.Evar sparse.id.«nausparse:preparemarks1» (tfun [tulong] .Tvoid)) [tv id.n]))
      (.Ssequence
        (.Ssequence (sk (.Sset id.i (ci 0 tint)))
          (.Sloop
            (.Ssequence (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak)) row)
            (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint)))))
        (sk (.Sreturn (some (ci 1 tint))))))

kernel_rfl body_eq : sparse.body.isautom_sg = body

end NautyVerified.Proofs.Sparse.Isautom

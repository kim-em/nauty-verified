import NautyVerified.Proofs.Sparse.Isautom.Syntax
import NautyVerified.Proofs.Alloc.DynL

/-!
# `testcanlab_sg`, factored

The Clight of nausparse.c's `testcanlab_sg`, in named pieces; `body_eq` pins
it to `sparse.body.testcanlab_sg`.
-/

namespace NautyVerified.Proofs.Sparse.Testcanlab

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat mat)

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
abbrev di : Common.AST.ident := sparse.id.di
abbrev dli : Common.AST.ident := sparse.id.dli
abbrev j : Common.AST.ident := sparse.id.j
abbrev vi : Common.AST.ident := sparse.id.vi
abbrev vli : Common.AST.ident := sparse.id.vli
abbrev mina : Common.AST.ident := sparse.id.mina
abbrev ij : Common.AST.ident := sparse.id.ij
abbrev work1 : Common.AST.ident := sparse.id.«nausparse:work1»
abbrev work1Sz : Common.AST.ident := sparse.id.«nausparse:work1_sz»
abbrev t1 : Common.AST.ident := idOf 705
abbrev t2 : Common.AST.ident := idOf 706
end id

/-- `INVLAB[a]`. -/
abbrev wat (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar id.work1 (tptr tint)) a (tptr tint)) tint

/-- `SG_VDE(p, v, d, e)`. -/
abbrev vde (p v d e : Common.AST.ident) : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sset v (sgField p sparse.id.v (tptr tulong))))
      (.Ssequence
        (sk (.Sset d (sgField p sparse.id.d (tptr tint))))
        (sk (.Sset e (sgField p sparse.id.e (tptr tint))))))
    (sk .Sbreak)

/-- `for (j = 0; j < di; ++j) <s>`. -/
abbrev jloop (s : statement) : statement :=
  .Ssequence
    (sk (.Sset id.j (.Ecast (ci 0 tint) tulong)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tl id.j) (tv id.di) tint) .Sskip .Sbreak))
        s)
      (sk (.Sset id.j (.Ebinop .Oadd (tl id.j) (ci 1 tint) tulong))))

/-- `for (i = 0; i < n; ++i) <s>`. -/
abbrev iloop (s : statement) : statement :=
  .Ssequence
    (sk (.Sset id.i (ci 0 tint)))
    (.Sloop
      (.Ssequence (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak)) s)
      (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))))

/-- `ce[vi+j]`. -/
abbrev ceat : expr := iat id.ce (.Ebinop .Oadd (tl id.vi) (tl id.j) tulong)

/-- `INVLAB[lab[i]] = i`. -/
abbrev scatter : statement := sk (.Sassign (wat (iat id.lab (tv id.i))) (tv id.i))

/-- `MARK1(ce[vi+j])`. -/
abbrev mark : statement := sk (.Sassign (mat ceat) (.Evar Sparse.id.vmark1Val tshort))

/-- The candidate pass: `k = INVLAB[e[vli+j]]; if (ISMARKED1(k)) UNMARK1(k);
else if (k < mina) mina = k;` -/
abbrev unmarkBody : statement :=
  .Ssequence
    (sk (.Sset id.k (wat (iat id.e (.Ebinop .Oadd (tl id.vli) (tl id.j) tulong)))))
    (sk (.Sifthenelse (.Ebinop .Oeq (mat (tv id.k)) (.Evar Sparse.id.vmark1Val tshort) tint)
      (sk (.Sassign (mat (tv id.k)) (ci 0 tint)))
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.k) (tv id.mina) tint)
        (sk (.Sset id.mina (tv id.k))) .Sskip))))

/-- `k = ce[vi+j]; if (ISMARKED1(k) && k < mina) return -1;` -/
abbrev checkBody : statement :=
  .Ssequence
    (sk (.Sset id.k ceat))
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Oeq (mat (tv id.k)) (.Evar Sparse.id.vmark1Val tshort) tint)
        (sk (.Sset id.t2 (.Ecast (.Ebinop .Olt (tv id.k) (tv id.mina) tint) tbool)))
        (.Sset id.t2 (ci 0 tint))))
      (.Sifthenelse (tv id.t2) (sk (.Sreturn (some (.Eunop .Oneg (ci 1 tint) tint)))) .Sskip))

/-- `*samerows = x`. -/
abbrev setSame (x : Common.AST.ident) : statement :=
  sk (.Sassign (.Ederef (.Etempvar id.samerows (tptr tint)) tint) (tv x))

/-- The rows after the degrees agree. -/
abbrev rowTail : statement :=
  .Ssequence (resetmarks1 id.t1 id.ij)
    (.Ssequence (sk (.Sset id.mina (tv id.n)))
      (.Ssequence (jloop mark)
        (.Ssequence (jloop unmarkBody)
          (sk (.Sifthenelse (.Ebinop .One (tv id.mina) (tv id.n) tint)
            (.Ssequence (setSame id.i)
              (.Ssequence (jloop checkBody) (sk (.Sreturn (some (ci 1 tint))))))
            .Sskip)))))

/-- The body of the loop over rows. -/
abbrev row : statement :=
  .Ssequence (sk (.Sset id.vi (lat id.cv (tv id.i))))
    (.Ssequence (sk (.Sset id.di (iat id.cd (tv id.i))))
      (.Ssequence (sk (.Sset id.vli (lat id.v (iat id.lab (tv id.i)))))
        (.Ssequence (sk (.Sset id.dli (iat id.d (iat id.lab (tv id.i)))))
          (.Ssequence
            (sk (.Sifthenelse (.Ebinop .One (tv id.di) (tv id.dli) tint)
              (.Ssequence (setSame id.i)
                (.Ssequence
                  (sk (.Sifthenelse (.Ebinop .Olt (tv id.di) (tv id.dli) tint)
                    (sk (.Sreturn (some (.Eunop .Oneg (ci 1 tint) tint)))) .Sskip))
                  (sk (.Sreturn (some (ci 1 tint))))))
              .Sskip))
            rowTail))))

abbrev body : statement :=
  .Ssequence (vde id.g id.v id.d id.e)
    (.Ssequence (vde id.canong id.cv id.cd id.ce)
      (.Ssequence
        (Alloc.dynalloc1 id.work1Sz id.work1 tint (tv id.n) (idOf 703) (idOf 704)
          sparse.id.«nausparse:__stringlit_2» 14)
        (.Ssequence
          (sk (.Scall none (.Evar sparse.id.«nausparse:preparemarks1» (tfun [tulong] .Tvoid)) [tv id.n]))
          (.Ssequence (iloop scatter)
            (.Ssequence (iloop row)
              (.Ssequence (setSame id.n) (sk (.Sreturn (some (ci 0 tint))))))))))

kernel_rfl body_eq : sparse.body.testcanlab_sg = body

end NautyVerified.Proofs.Sparse.Testcanlab

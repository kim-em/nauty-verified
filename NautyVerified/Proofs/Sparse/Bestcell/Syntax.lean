import NautyVerified.Proofs.Sparse.Testcanlab.Syntax
import NautyVerified.Proofs.Sparse.Freedyn

/-!
# `bestcell_sg`, factored

The Clight of nausparse.c's `bestcell_sg`, in named pieces; `body_eq` pins
it to `sparse.body.«nausparse:bestcell_sg»`. `START` is `work1`, `SIZE` is
`work1b = work1 + n/2`, `NNTCELL` is `work2`, `HITS` is `work3` and
`COUNT` is `work4`.
-/

namespace NautyVerified.Proofs.Sparse.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat)
open NautyVerified.Proofs.Sparse.Testcanlab (vde jloop)

namespace id
abbrev g : Common.AST.ident := sparse.id.g
abbrev lab : Common.AST.ident := sparse.id.lab
abbrev ptn : Common.AST.ident := sparse.id.ptn
abbrev level : Common.AST.ident := sparse.id.level
abbrev n : Common.AST.ident := sparse.id.n
abbrev v : Common.AST.ident := sparse.id.v
abbrev d : Common.AST.ident := sparse.id.d
abbrev e : Common.AST.ident := sparse.id.e
abbrev i : Common.AST.ident := sparse.id.i
abbrev j : Common.AST.ident := sparse.id.j
abbrev k : Common.AST.ident := sparse.id.k
abbrev di : Common.AST.ident := sparse.id.di
abbrev vi : Common.AST.ident := sparse.id.vi
abbrev nnt : Common.AST.ident := sparse.id.nnt
abbrev maxcnt : Common.AST.ident := sparse.id.maxcnt
abbrev work1b : Common.AST.ident := sparse.id.work1b
abbrev work1 : Common.AST.ident := sparse.id.«nausparse:work1»
abbrev work1Sz : Common.AST.ident := sparse.id.«nausparse:work1_sz»
abbrev work2 : Common.AST.ident := sparse.id.«nausparse:work2»
abbrev work2Sz : Common.AST.ident := sparse.id.«nausparse:work2_sz»
abbrev work3 : Common.AST.ident := sparse.id.«nausparse:work3»
abbrev work3Sz : Common.AST.ident := sparse.id.«nausparse:work3_sz»
abbrev work4 : Common.AST.ident := sparse.id.«nausparse:work4»
abbrev work4Sz : Common.AST.ident := sparse.id.«nausparse:work4_sz»
abbrev t0 : Common.AST.ident := idOf 711
abbrev tj : Common.AST.ident := idOf 712
abbrev tz : Common.AST.ident := idOf 713
abbrev th : Common.AST.ident := idOf 714
end id

/-- `w[a]` for the `int *` global `w`. -/
abbrev gat (w : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar w (tptr tint)) a (tptr tint)) tint

/-- `NNTCELL[e[vi+j]]`. -/
abbrev nntAt : expr := gat id.work2 (iat id.e (.Ebinop .Oadd (tl id.vi) (tl id.j) tulong))

/-- `lab[START[i]]`. -/
abbrev firstV : expr := iat id.lab (gat id.work1 (tv id.i))

/-- The nontrivial cell at `i`: `START[nnt] = i; j = i;
do NNTCELL[lab[j]] = nnt; while (ptn[j++] > level); SIZE[nnt] = j-i; ++nnt; i = j;` -/
abbrev nontriv : statement :=
  .Ssequence
    (sk (.Sassign (gat id.work1 (tv id.nnt)) (tv id.i)))
    (.Ssequence
      (sk (.Sset id.j (.Ecast (tv id.i) tulong)))
      (.Ssequence
        (.Sloop
          (sk (.Sassign (gat id.work2 (.Ederef (.Ebinop .Oadd (.Etempvar id.lab (tptr tint)) (tl id.j)
            (tptr tint)) tint)) (tv id.nnt)))
          (.Ssequence
            (.Ssequence
              (sk (.Sset id.tj (tl id.j)))
              (.Sset id.j (.Ebinop .Oadd (tl id.tj) (ci 1 tint) tulong)))
            (.Sifthenelse (.Ebinop .Ogt (.Ederef (.Ebinop .Oadd (.Etempvar id.ptn (tptr tint)) (tl id.tj)
              (tptr tint)) tint) (tv id.level) tint) .Sskip .Sbreak)))
        (.Ssequence
          (sk (.Sassign (iat id.work1b (tv id.nnt)) (.Ebinop .Osub (tl id.j) (tv id.i) tulong)))
          (.Ssequence
            (sk (.Sset id.nnt (.Ebinop .Oadd (tv id.nnt) (ci 1 tint) tint)))
            (sk (.Sset id.i (.Ecast (tl id.j) tint)))))))

/-- A singleton at `i`: `NNTCELL[lab[i]] = n; ++i;` -/
abbrev single : statement :=
  .Ssequence
    (sk (.Sassign (gat id.work2 (iat id.lab (tv id.i))) (tv id.n)))
    (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint)))

/-- `while (i < n) { if (ptn[i] > level) nontriv else single }` -/
abbrev cellLoop : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak))
      (sk (.Sifthenelse (.Ebinop .Ogt (iat id.ptn (tv id.i)) (tv id.level) tint) nontriv single)))
    .Sskip

/-- `for (i = 0; i < nnt; ++i) <s>` -/
abbrev cloop (s : statement) : statement :=
  .Ssequence
    (sk (.Sset id.i (ci 0 tint)))
    (.Sloop
      (.Ssequence (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.nnt) tint) .Sskip .Sbreak)) s)
      (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))))

/-- `HITS[i] = COUNT[i] = 0;` -/
abbrev zero : statement :=
  .Ssequence
    (.Ssequence
      (sk (.Sset id.tz (.Ecast (ci 0 tint) tint)))
      (.Sassign (gat id.work4 (tv id.i)) (tv id.tz)))
    (.Sassign (gat id.work3 (tv id.i)) (tv id.tz))

/-- `k = NNTCELL[e[vi+j]]; if (k != n) ++HITS[k];` -/
abbrev hitBody : statement :=
  .Ssequence
    (sk (.Sset id.k nntAt))
    (sk (.Sifthenelse (.Ebinop .One (tv id.k) (tv id.n) tint)
      (sk (.Sassign (gat id.work3 (tv id.k)) (.Ebinop .Oadd (gat id.work3 (tv id.k)) (ci 1 tint) tint)))
      .Sskip))

/-- `k = NNTCELL[e[vi+j]]; if (k != n) { if (HITS[k] > 0 && HITS[k] < SIZE[k]) ++COUNT[i];
HITS[k] = 0; }` -/
abbrev countBody : statement :=
  .Ssequence
    (sk (.Sset id.k nntAt))
    (sk (.Sifthenelse (.Ebinop .One (tv id.k) (tv id.n) tint)
      (.Ssequence
        (.Ssequence
          (sk (.Sifthenelse (.Ebinop .Ogt (gat id.work3 (tv id.k)) (ci 0 tint) tint)
            (sk (.Sset id.th (.Ecast (.Ebinop .Olt (gat id.work3 (tv id.k)) (iat id.work1b (tv id.k)) tint)
              tbool)))
            (.Sset id.th (ci 0 tint))))
          (.Sifthenelse (tv id.th)
            (sk (.Sassign (gat id.work4 (tv id.i)) (.Ebinop .Oadd (gat id.work4 (tv id.i)) (ci 1 tint) tint)))
            .Sskip))
        (sk (.Sassign (gat id.work3 (tv id.k)) (ci 0 tint))))
      .Sskip))

/-- The joins of cell `i`. -/
abbrev cellJoins : statement :=
  .Ssequence
    (sk (.Sset id.vi (lat id.v firstV)))
    (.Ssequence
      (sk (.Sset id.di (iat id.d firstV)))
      (.Ssequence (jloop hitBody) (jloop countBody)))

/-- `for (i = 1; i < nnt; ++i) if (COUNT[i] > maxcnt) { j = i; maxcnt = COUNT[i]; }` -/
abbrev argLoop : statement :=
  .Ssequence
    (sk (.Sset id.i (ci 1 tint)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.nnt) tint) .Sskip .Sbreak))
        (sk (.Sifthenelse (.Ebinop .Ogt (gat id.work4 (tv id.i)) (tv id.maxcnt) tint)
          (.Ssequence
            (sk (.Sset id.j (.Ecast (tv id.i) tulong)))
            (sk (.Sset id.maxcnt (gat id.work4 (tv id.i)))))
          .Sskip)))
      (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))))

/-- `DYNALLOC1(int, work<k>, work<k>_sz, n, "bestcell_sg")`. -/
abbrev dyn (gs gp t1 t2 : Common.AST.ident) : statement :=
  Alloc.dynalloc1 gs gp tint (tv id.n) t1 t2 sparse.id.«nausparse:__stringlit_7» 12

abbrev body : statement :=
  .Ssequence (vde id.g id.v id.d id.e)
    (.Ssequence (dyn id.work1Sz id.work1 (idOf 703) (idOf 704))
      (.Ssequence (dyn id.work2Sz id.work2 (idOf 705) (idOf 706))
        (.Ssequence (dyn id.work3Sz id.work3 (idOf 707) (idOf 708))
          (.Ssequence (dyn id.work4Sz id.work4 (idOf 709) (idOf 710))
            (.Ssequence
              (sk (.Sset id.work1b (.Ebinop .Oadd (.Evar id.work1 (tptr tint))
                (.Ebinop .Odiv (tv id.n) (ci 2 tint) tint) (tptr tint))))
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk (.Sset id.t0 (.Ecast (ci 0 tint) tint)))
                    (.Sset id.nnt (tv id.t0)))
                  (.Sset id.i (tv id.t0)))
                (.Ssequence cellLoop
                  (.Ssequence
                    (sk (.Sifthenelse (.Ebinop .Oeq (tv id.nnt) (ci 0 tint) tint)
                      (sk (.Sreturn (some (tv id.n)))) .Sskip))
                    (.Ssequence (cloop zero)
                      (.Ssequence (cloop cellJoins)
                        (.Ssequence
                          (sk (.Sset id.j (.Ecast (ci 0 tint) tulong)))
                          (.Ssequence
                            (sk (.Sset id.maxcnt (gat id.work4 (ci 0 tint))))
                            (.Ssequence argLoop
                              (sk (.Sreturn (some (.Ecast (.Ederef (.Ebinop .Oadd
                                (.Evar id.work1 (tptr tint)) (tl id.j) (tptr tint)) tint)
                                tint)))))))))))))))))

kernel_rfl body_eq : sparse.body.«nausparse:bestcell_sg» = body

end NautyVerified.Proofs.Sparse.Bestcell

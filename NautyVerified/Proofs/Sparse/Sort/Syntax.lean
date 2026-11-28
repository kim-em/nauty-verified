import NautyVerified.Proofs.Syntax
import NautyVerified.Source.Sparse

/-!
# `sortindirect`, factored

The Clight of nausparse.c's `sortindirect` (sorttemplates.c with
`SORT_OF_SORT 3`, `int` keys `y[x[i]]`), in named pieces; `body_eq` pins it
to `sparse.body.«nausparse:sortindirect»`. `shiftLoop`/`insLoop` are the
insertion sort below 11 entries, `pivot` the median (of nine from 320
entries), `scanL`/`scanR` the two scans of `partLoop` (Bentley and
McIlroy's three-way partition), `swapLoop` the two block swaps after it, and
`pushes` the two pushes, smaller side on top.
-/

namespace NautyVerified.Proofs.Sparse.Sort

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source

namespace id
abbrev «x» : Common.AST.ident := sparse.id.«x»
abbrev «y» : Common.AST.ident := sparse.id.«y»
abbrev «n» : Common.AST.ident := sparse.id.«n»
abbrev «top» : Common.AST.ident := sparse.id.«top»
abbrev «stack» : Common.AST.ident := sparse.id.«stack»
abbrev «x0» : Common.AST.ident := sparse.id.«x0»
abbrev «nn» : Common.AST.ident := sparse.id.«nn»
abbrev «i» : Common.AST.ident := sparse.id.«i»
abbrev «j» : Common.AST.ident := sparse.id.«j»
abbrev «tmp1» : Common.AST.ident := sparse.id.«tmp1»
abbrev «tmp2» : Common.AST.ident := sparse.id.«tmp2»
abbrev «v» : Common.AST.ident := sparse.id.«v»
abbrev «v1» : Common.AST.ident := sparse.id.«v1»
abbrev «v2» : Common.AST.ident := sparse.id.«v2»
abbrev «v3» : Common.AST.ident := sparse.id.«v3»
abbrev «xa» : Common.AST.ident := sparse.id.«xa»
abbrev «xb» : Common.AST.ident := sparse.id.«xb»
abbrev «xc» : Common.AST.ident := sparse.id.«xc»
abbrev «xd» : Common.AST.ident := sparse.id.«xd»
abbrev «xl» : Common.AST.ident := sparse.id.«xl»
abbrev «xh» : Common.AST.ident := sparse.id.«xh»
abbrev «a» : Common.AST.ident := sparse.id.«a»
abbrev «ba» : Common.AST.ident := sparse.id.«ba»
abbrev «d» : Common.AST.ident := sparse.id.«d»
abbrev «dc» : Common.AST.ident := sparse.id.«dc»
abbrev «s» : Common.AST.ident := sparse.id.«s»
abbrev «addr» : Common.AST.ident := sparse.id.«addr»
abbrev «len» : Common.AST.ident := sparse.id.«len»
abbrev «_1759» : Common.AST.ident := sparse.id.«_1759»
end id

/-- `.Ssequence .Sskip s`, SimplExpr's shape for a statement. -/
abbrev sk (s : statement) : statement := .Ssequence .Sskip s
abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint
abbrev pv (x : Common.AST.ident) : expr := .Etempvar x (tptr tint)
/-- `p[a]`. -/
abbrev ix (p : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (pv p) a (tptr tint)) tint
/-- `*p`. -/
abbrev dr (p : Common.AST.ident) : expr := .Ederef (pv p) tint
abbrev castT (t : Common.AST.ident) : statement := .Sset t (.Ecast (tv t) tint)

/-- `t = SORT_MEDIAN_OF_3(a, b, c)`, as SimplExpr lowers the conditional. -/
abbrev med3 (t : Common.AST.ident) (a b c : expr) : statement :=
  sk (.Sifthenelse (.Ebinop .Ole a b tint)
    (sk (.Sifthenelse (.Ebinop .Ole b c tint)
      (.Ssequence (sk (.Sset t (.Ecast b tint))) (castT t))
      (sk (.Sifthenelse (.Ebinop .Ole c a tint)
        (.Ssequence (.Ssequence (sk (.Sset t (.Ecast a tint))) (castT t)) (castT t))
        (.Ssequence (.Ssequence (sk (.Sset t (.Ecast c tint))) (castT t)) (castT t))))))
    (sk (.Sifthenelse (.Ebinop .Ole a c tint)
      (.Ssequence (sk (.Sset t (.Ecast a tint))) (castT t))
      (sk (.Sifthenelse (.Ebinop .Ole c b tint)
        (.Ssequence (.Ssequence (sk (.Sset t (.Ecast b tint))) (castT t)) (castT t))
        (.Ssequence (.Ssequence (sk (.Sset t (.Ecast c tint))) (castT t)) (castT t)))))))

/-- The stack entry type `struct {int *addr; int len;}`. -/
abbrev entry : type := Tstruct id.«_1759» noattr

/-- `stack[top].f`. -/
abbrev stk (f : Common.AST.ident) (t : type) : expr :=
  .Efield (.Ederef (.Ebinop .Oadd (.Evar id.«stack» (tarray entry 40)) (tv id.«top») (tptr entry))
    entry) f t

/-- `stack[top].addr = p; stack[top].len = l; ++top;` -/
abbrev push (p l : expr) : statement :=
  .Ssequence (sk (.Sassign (stk id.«addr» (tptr tint)) p))
    (.Ssequence (sk (.Sassign (stk id.«len» tint) l))
      (sk (.Sset id.«top» (.Ebinop .Oadd (tv id.«top») (ci 1 tint) tint))))

/-- `SORT_SWAP1(*p, *q)`, then `r`. -/
abbrev swapThen (p q : Common.AST.ident) (r : statement) : statement :=
  .Ssequence (sk (.Sset id.«tmp1» (dr p)))
    (.Ssequence (sk (.Sassign (dr p) (dr q))) (.Ssequence (sk (.Sassign (dr q) (tv id.«tmp1»))) r))

abbrev shiftLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Ogt
            (ix id.«y» (ix id.«x0» (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint)))
            (tv id.«tmp2»)
            tint)
          .Sskip
          .Sbreak))
      (.Ssequence
        (sk
          (.Sassign
            (ix id.«x0» (tv id.«j»))
            (ix id.«x0» (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint))))
        (.Ssequence
          (.Ssequence
            (sk (.Sset (idOf 703) (.Ecast (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) tint)))
            (.Sset id.«j» (tv (idOf 703))))
          (.Sifthenelse (.Ebinop .Oeq (tv (idOf 703)) (ci 0 tint) tint) .Sbreak .Sskip))))
    .Sskip)

abbrev insLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.«i») (tv id.«nn») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sset id.«tmp1» (ix id.«x0» (tv id.«i»))))
        (.Ssequence
          (sk (.Sset id.«tmp2» (ix id.«y» (tv id.«tmp1»))))
          (.Ssequence
            (.Ssequence (sk (.Sset id.«j» (tv id.«i»))) shiftLoop)
            (sk (.Sassign (ix id.«x0» (tv id.«j»)) (tv id.«tmp1»)))))))
    (sk (.Sset id.«i» (.Ebinop .Oadd (tv id.«i») (ci 1 tint) tint))))

abbrev pivot : statement :=
  (.Sifthenelse
    (.Ebinop .Olt (tv id.«nn») (ci 320 tint) tint)
    (.Ssequence
      (med3
        (idOf 704)
        (ix id.«y» (ix id.«x0» (ci 0 tint)))
        (ix id.«y» (ix id.«x0» (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint)))
        (ix id.«y» (ix id.«x0» (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint))))
      (.Sset id.«v» (tv (idOf 704))))
    (.Ssequence
      (.Ssequence
        (med3
          (idOf 705)
          (ix id.«y» (ix id.«x0» (ci 0 tint)))
          (ix id.«y» (ix id.«x0» (ci 1 tint)))
          (ix id.«y» (ix id.«x0» (ci 2 tint))))
        (.Sset id.«v1» (tv (idOf 705))))
      (.Ssequence
        (.Ssequence
          (med3
            (idOf 706)
            (ix id.«y»
              (ix id.«x0»
                (.Ebinop .Osub (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint) (ci 1 tint) tint)))
            (ix id.«y» (ix id.«x0» (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint)))
            (ix id.«y»
              (ix id.«x0»
                (.Ebinop .Oadd (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint) (ci 1 tint) tint))))
          (.Sset id.«v2» (tv (idOf 706))))
        (.Ssequence
          (.Ssequence
            (med3
              (idOf 707)
              (ix id.«y» (ix id.«x0» (.Ebinop .Osub (tv id.«nn») (ci 3 tint) tint)))
              (ix id.«y» (ix id.«x0» (.Ebinop .Osub (tv id.«nn») (ci 2 tint) tint)))
              (ix id.«y» (ix id.«x0» (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint))))
            (.Sset id.«v3» (tv (idOf 707))))
          (.Ssequence
            (med3 (idOf 708) (tv id.«v1») (tv id.«v2») (tv id.«v3»))
            (.Sset id.«v» (tv (idOf 708))))))))

abbrev scanL : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Ole (pv id.«xb») (pv id.«xc») tint)
            (sk
              (.Sset
                (idOf 711)
                (.Ecast (.Ebinop .Ole (ix id.«y» (dr id.«xb»)) (tv id.«v») tint) tbool)))
            (.Sset (idOf 711) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 711)) .Sskip .Sbreak))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Oeq (ix id.«y» (dr id.«xb»)) (tv id.«v») tint)
            (swapThen id.«xa» id.«xb»
              (sk (.Sset id.«xa» (.Ebinop .Oadd (pv id.«xa») (ci 1 tint) (tptr tint)))))
            .Sskip))
        (sk (.Sset id.«xb» (.Ebinop .Oadd (pv id.«xb») (ci 1 tint) (tptr tint))))))
    .Sskip)

abbrev scanR : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Oge (pv id.«xc») (pv id.«xb») tint)
            (sk
              (.Sset
                (idOf 712)
                (.Ecast (.Ebinop .Oge (ix id.«y» (dr id.«xc»)) (tv id.«v») tint) tbool)))
            (.Sset (idOf 712) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 712)) .Sskip .Sbreak))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Oeq (ix id.«y» (dr id.«xc»)) (tv id.«v») tint)
            (swapThen id.«xc» id.«xd»
              (sk (.Sset id.«xd» (.Ebinop .Osub (pv id.«xd») (ci 1 tint) (tptr tint)))))
            .Sskip))
        (sk (.Sset id.«xc» (.Ebinop .Osub (pv id.«xc») (ci 1 tint) (tptr tint))))))
    .Sskip)

abbrev partLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk .Sskip)
      (.Ssequence scanL
        (.Ssequence scanR
          (.Ssequence
            (sk (.Sifthenelse (.Ebinop .Ogt (pv id.«xb») (pv id.«xc») tint) .Sbreak .Sskip))
            (swapThen id.«xb» id.«xc»
              (.Ssequence
                (sk (.Sset id.«xb» (.Ebinop .Oadd (pv id.«xb») (ci 1 tint) (tptr tint))))
                (sk (.Sset id.«xc» (.Ebinop .Osub (pv id.«xc») (ci 1 tint) (tptr tint))))))))))
    .Sskip)

abbrev swapLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ogt (tv id.«s») (ci 0 tint) tint) .Sskip .Sbreak))
      (swapThen id.«xl» id.«xh»
        (.Ssequence
          (sk (.Sset id.«xl» (.Ebinop .Oadd (pv id.«xl») (ci 1 tint) (tptr tint))))
          (sk (.Sset id.«xh» (.Ebinop .Oadd (pv id.«xh») (ci 1 tint) (tptr tint)))))))
    (sk (.Sset id.«s» (.Ebinop .Osub (tv id.«s») (ci 1 tint) tint))))

abbrev pushes : statement :=
  (.Sifthenelse
    (.Ebinop .Ogt (tv id.«ba») (tv id.«dc») tint)
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Ogt (tv id.«ba») (ci 1 tint) tint)
          (push (pv id.«x0») (tv id.«ba»))
          .Sskip))
      (sk
        (.Sifthenelse
          (.Ebinop .Ogt (tv id.«dc») (ci 1 tint) tint)
          (push
            (.Ebinop .Oadd (pv id.«x0») (.Ebinop .Osub (tv id.«nn») (tv id.«dc») tint) (tptr tint))
            (tv id.«dc»))
          .Sskip)))
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Ogt (tv id.«dc») (ci 1 tint) tint)
          (push
            (.Ebinop .Oadd (pv id.«x0») (.Ebinop .Osub (tv id.«nn») (tv id.«dc») tint) (tptr tint))
            (tv id.«dc»))
          .Sskip))
      (sk
        (.Sifthenelse
          (.Ebinop .Ogt (tv id.«ba») (ci 1 tint) tint)
          (push (pv id.«x0») (tv id.«ba»))
          .Sskip))))

abbrev mainLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ogt (tv id.«top») (ci 0 tint) tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sset id.«top» (.Ebinop .Osub (tv id.«top») (ci 1 tint) tint)))
        (.Ssequence
          (sk (.Sset id.«x0» (stk id.«addr» (tptr tint))))
          (.Ssequence
            (sk (.Sset id.«nn» (stk id.«len» tint)))
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .Olt (tv id.«nn») (ci 11 tint) tint)
                  (.Ssequence (.Ssequence (sk (.Sset id.«i» (ci 1 tint))) insLoop) .Scontinue)
                  .Sskip))
              (.Ssequence
                (sk pivot)
                (.Ssequence
                  (.Ssequence
                    (.Ssequence
                      (sk (.Sset (idOf 709) (.Ecast (pv id.«x0») (tptr tint))))
                      (.Sset id.«xb» (pv (idOf 709))))
                    (.Sset id.«xa» (pv (idOf 709))))
                  (.Ssequence
                    (.Ssequence
                      (.Ssequence
                        (sk
                          (.Sset
                            (idOf 710)
                            (.Ecast
                              (.Ebinop .Oadd
                                (pv id.«x0»)
                                (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint)
                                (tptr tint))
                              (tptr tint))))
                        (.Sset id.«xd» (pv (idOf 710))))
                      (.Sset id.«xc» (pv (idOf 710))))
                    (.Ssequence partLoop
                      (.Ssequence
                        (sk
                          (.Sset id.«a»
                            (.Ecast (.Ebinop .Osub (pv id.«xa») (pv id.«x0») tlong) tint)))
                        (.Ssequence
                          (sk
                            (.Sset id.«ba»
                              (.Ecast (.Ebinop .Osub (pv id.«xb») (pv id.«xa») tlong) tint)))
                          (.Ssequence
                            (sk
                              (.Sifthenelse
                                (.Ebinop .Ogt (tv id.«ba») (tv id.«a») tint)
                                (sk (.Sset id.«s» (tv id.«a»)))
                                (sk (.Sset id.«s» (tv id.«ba»)))))
                            (.Ssequence
                              (.Ssequence
                                (.Ssequence
                                  (sk (.Sset id.«xl» (pv id.«x0»)))
                                  (.Sset id.«xh»
                                    (.Ebinop .Osub (pv id.«xb») (tv id.«s») (tptr tint))))
                                swapLoop)
                              (.Ssequence
                                (sk
                                  (.Sset id.«d»
                                    (.Ecast (.Ebinop .Osub (pv id.«xd») (pv id.«x0») tlong) tint)))
                                (.Ssequence
                                  (sk
                                    (.Sset id.«dc»
                                      (.Ecast (.Ebinop .Osub (pv id.«xd») (pv id.«xc») tlong) tint)))
                                  (.Ssequence
                                    (sk
                                      (.Sifthenelse
                                        (.Ebinop .Ogt
                                          (tv id.«dc»)
                                          (.Ebinop .Osub
                                            (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint)
                                            (tv id.«d»)
                                            tint)
                                          tint)
                                        (sk
                                          (.Sset id.«s»
                                            (.Ebinop .Osub
                                              (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint)
                                              (tv id.«d»)
                                              tint)))
                                        (sk (.Sset id.«s» (tv id.«dc»)))))
                                    (.Ssequence
                                      (.Ssequence
                                        (.Ssequence
                                          (sk (.Sset id.«xl» (pv id.«xb»)))
                                          (.Sset id.«xh»
                                            (.Ebinop .Oadd
                                              (pv id.«x0»)
                                              (.Ebinop .Osub (tv id.«nn») (tv id.«s») tint)
                                              (tptr tint))))
                                        swapLoop)
                                      (sk pushes))))))))))))))))))
    .Sskip)

abbrev body : statement :=
  (.Ssequence
    (sk (.Sset id.«top» (ci 0 tint)))
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Ogt (tv id.«n») (ci 1 tint) tint)
          (push (pv id.«x») (tv id.«n»))
          .Sskip))
      mainLoop))

kernel_rfl body_eq : NautyVerified.Source.sparse.body.«nausparse:sortindirect» = body

end NautyVerified.Proofs.Sparse.Sort

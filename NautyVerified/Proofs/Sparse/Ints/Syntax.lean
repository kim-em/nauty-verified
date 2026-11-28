import NautyVerified.Proofs.Sparse.Sort.Syntax

/-!
# `sortints`, factored

The Clight of nausparse.c's `sortints` (sorttemplates.c with
`SORT_OF_SORT 1`, `int` keys `x[i]`), in named pieces; `body_eq` pins it to
`sparse.body.«nausparse:sortints»`. The pieces are those of `sortindirect`
(`Proofs/Sparse/Sort/Syntax.lean`) with direct keys, except that the
equal-key moves write the pivot `v` instead of swapping: in the scans
(`*xb = *xa; *xa = v`, `*xc = *xd; *xd = v`) and in the block moves
(`swapLoop`: `*xl = *xh; *xh = v`, `swapLoop2`: `*xh = *xl; *xl = v`).
The work stack has the same layout under another struct name.
-/

namespace NautyVerified.Proofs.Sparse.Sort.Ints

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source

/-- The stack entry type `struct {int *addr; int len;}`. -/
abbrev entry : type := Tstruct sparse.id.«_1786» noattr

/-- `stack[top].f`. -/
abbrev stk (f : Common.AST.ident) (t : type) : expr :=
  .Efield (.Ederef (.Ebinop .Oadd (.Evar id.«stack» (tarray entry 40)) (tv id.«top») (tptr entry))
    entry) f t

/-- `stack[top].addr = p; stack[top].len = l; ++top;` -/
abbrev push (p l : expr) : statement :=
  .Ssequence (sk (.Sassign (stk id.«addr» (tptr tint)) p))
    (.Ssequence (sk (.Sassign (stk id.«len» tint) l))
      (sk (.Sset id.«top» (.Ebinop .Oadd (tv id.«top») (ci 1 tint) tint))))

abbrev shiftLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Ogt
            (ix id.«x0» (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint))
            (tv id.«tmp1»)
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
          (.Ssequence (sk (.Sset id.«j» (tv id.«i»))) shiftLoop)
          (sk (.Sassign (ix id.«x0» (tv id.«j»)) (tv id.«tmp1»))))))
    (sk (.Sset id.«i» (.Ebinop .Oadd (tv id.«i») (ci 1 tint) tint))))

abbrev pivot : statement :=
  (.Sifthenelse
    (.Ebinop .Olt (tv id.«nn») (ci 320 tint) tint)
    (.Ssequence
      (med3
        (idOf 704)
        (ix id.«x0» (ci 0 tint))
        (ix id.«x0» (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint))
        (ix id.«x0» (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint)))
      (.Sset id.«v» (tv (idOf 704))))
    (.Ssequence
      (.Ssequence
        (med3 (idOf 705) (ix id.«x0» (ci 0 tint)) (ix id.«x0» (ci 1 tint)) (ix id.«x0» (ci 2 tint)))
        (.Sset id.«v1» (tv (idOf 705))))
      (.Ssequence
        (.Ssequence
          (med3
            (idOf 706)
            (ix id.«x0»
              (.Ebinop .Osub (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint) (ci 1 tint) tint))
            (ix id.«x0» (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint))
            (ix id.«x0»
              (.Ebinop .Oadd (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint) (ci 1 tint) tint)))
          (.Sset id.«v2» (tv (idOf 706))))
        (.Ssequence
          (.Ssequence
            (med3
              (idOf 707)
              (ix id.«x0» (.Ebinop .Osub (tv id.«nn») (ci 3 tint) tint))
              (ix id.«x0» (.Ebinop .Osub (tv id.«nn») (ci 2 tint) tint))
              (ix id.«x0» (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint)))
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
            (sk (.Sset (idOf 711) (.Ecast (.Ebinop .Ole (dr id.«xb») (tv id.«v») tint) tbool)))
            (.Sset (idOf 711) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 711)) .Sskip .Sbreak))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Oeq (dr id.«xb») (tv id.«v») tint)
            (.Ssequence
              (sk (.Sassign (dr id.«xb») (dr id.«xa»)))
              (.Ssequence
                (sk (.Sassign (dr id.«xa») (tv id.«v»)))
                (sk (.Sset id.«xa» (.Ebinop .Oadd (pv id.«xa») (ci 1 tint) (tptr tint))))))
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
            (sk (.Sset (idOf 712) (.Ecast (.Ebinop .Oge (dr id.«xc») (tv id.«v») tint) tbool)))
            (.Sset (idOf 712) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 712)) .Sskip .Sbreak))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Oeq (dr id.«xc») (tv id.«v») tint)
            (.Ssequence
              (sk (.Sassign (dr id.«xc») (dr id.«xd»)))
              (.Ssequence
                (sk (.Sassign (dr id.«xd») (tv id.«v»)))
                (sk (.Sset id.«xd» (.Ebinop .Osub (pv id.«xd») (ci 1 tint) (tptr tint))))))
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
      (.Ssequence
        (sk (.Sassign (dr id.«xl») (dr id.«xh»)))
        (.Ssequence
          (sk (.Sassign (dr id.«xh») (tv id.«v»)))
          (.Ssequence
            (sk (.Sset id.«xl» (.Ebinop .Oadd (pv id.«xl») (ci 1 tint) (tptr tint))))
            (sk (.Sset id.«xh» (.Ebinop .Oadd (pv id.«xh») (ci 1 tint) (tptr tint))))))))
    (sk (.Sset id.«s» (.Ebinop .Osub (tv id.«s») (ci 1 tint) tint))))

abbrev swapLoop2 : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ogt (tv id.«s») (ci 0 tint) tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sassign (dr id.«xh») (dr id.«xl»)))
        (.Ssequence
          (sk (.Sassign (dr id.«xl») (tv id.«v»)))
          (.Ssequence
            (sk (.Sset id.«xl» (.Ebinop .Oadd (pv id.«xl») (ci 1 tint) (tptr tint))))
            (sk (.Sset id.«xh» (.Ebinop .Oadd (pv id.«xh») (ci 1 tint) (tptr tint))))))))
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
                                        swapLoop2)
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

kernel_rfl body_eq : NautyVerified.Source.sparse.body.«nausparse:sortints» = body

end NautyVerified.Proofs.Sparse.Sort.Ints

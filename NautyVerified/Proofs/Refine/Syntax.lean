import NautyVerified.Proofs.Set.Bit
import NautyVerified.Proofs.Alloc.Dyn

/-!
# `refine`, factored

The Clight of nauty's general `refine` (naugraph.c, `MAXM != 1`), in named
pieces; `body_eq` pins it to `dense.body.refine`. The pieces were cut out of
the printed body by `scripts/factor_clight.py` with `scripts/factor/refine.py`.

- `guard`: `*numcells < n` and the choice of `split1` (the hint, else the
  next active position after it, else the least active position);
- `step`: `DELELEMENT(active, split1)`, `split2`, the code, then `trivial` or
  `nontrivial`;
- `trivial`: the pass over all cells for a singleton splitter (`cellLoopT`,
  its two-pointer partition `swapLoop` and bookkeeping `trivSplit`);
- `nontrivial`: the splitter's vertex set (`fillWS`), then the pass over all
  cells (`cellLoopN`, `cellN`): neighbour counts (`countRest`), the window scan
  (`scanLoop`), the counting-sort placement (`placeLoop`, `copyLoop`) and the
  active-set fix (`fixN`);
- `finish`: the final code.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv setWord bitOf isElement addElementB delElementB)
open NautyVerified.Proofs.Alloc (dynalloc1)

abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint
abbrev pi (x : Common.AST.ident) : expr := .Etempvar x (tptr tint)

/-- `p[a]` for an `int *` temporary `p`. -/
abbrev ix (p : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (pi p) a (tptr tint)) tint

/-- `p[a]` for an `int *` global `p`. -/
abbrev gix (p : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar p (tptr tint)) a (tptr tint)) tint

/-- `longcode = MASH(longcode, e)`. -/
abbrev mash (e : expr) : statement :=
  .Sset dense.id.«longcode» (.Ebinop .Oand (.Ebinop .Oadd (.Ebinop .Oxor
    (.Etempvar dense.id.«longcode» tlong) (ci 27421 tint) tlong) e tlong) (ci 32767 tint) tlong)

/-- `for (x = y; ptn[x] > level; ++x) {}` -/
abbrev scanEnd (x y : Common.AST.ident) : statement :=
  .Ssequence (sk (.Sset x (tv y)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Ogt (ix dense.id.«ptn» (tv x)) (tv dense.id.«level») tint)
          .Sskip .Sbreak))
        .Sskip)
      (sk (.Sset x (.Ebinop .Oadd (tv x) (ci 1 tint) tint))))

/-- `bytecount[x >> k & 0xFF]`. -/
abbrev byteAt (k : Int) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar dense.id.«naugraph:bytecount» (tarray tint 256))
    (.Ebinop .Oand (.Ebinop .Oshr (.Etempvar dense.id.«x» tulong) (ci k tint) tulong)
      (ci 255 tint) tulong) (tptr tint)) tint

/-- `bytecount[x & 0xFF]`. -/
abbrev byte0 : expr :=
  .Ederef (.Ebinop .Oadd (.Evar dense.id.«naugraph:bytecount» (tarray tint 256))
    (.Ebinop .Oand (.Etempvar dense.id.«x» tulong) (ci 255 tint) tulong) (tptr tint)) tint

/-- `POPCOUNT(x)` from the `bytecount` table. -/
abbrev popcount : expr :=
  .Ebinop .Oadd (.Ebinop .Oadd (.Ebinop .Oadd (.Ebinop .Oadd (.Ebinop .Oadd (.Ebinop .Oadd
    (.Ebinop .Oadd (byteAt 56) (byteAt 48) tint) (byteAt 40) tint) (byteAt 32) tint)
    (byteAt 24) tint) (byteAt 16) tint) (byteAt 8) tint) byte0 tint

/-- `for (c1 = m; --c1 >= 0;) if ((x = *set1++ & *set2++) != 0) cnt += POPCOUNT(x);`
with SimplExpr's temporaries `a b c d`. -/
abbrev popLoop (a b c d : Common.AST.ident) : statement :=
  .Ssequence (sk (.Sset dense.id.«c1» (tv dense.id.«m»)))
    (.Sloop
      (.Ssequence
        (.Ssequence
          (.Ssequence (sk (.Sset a (.Ecast (.Ebinop .Osub (tv dense.id.«c1») (ci 1 tint) tint) tint)))
            (.Sset dense.id.«c1» (tv a)))
          (.Sifthenelse (.Ebinop .Oge (tv a) (ci 0 tint) tint) .Sskip .Sbreak))
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk (.Sset b (pv dense.id.«set1»)))
                    (.Sset dense.id.«set1» (.Ebinop .Oadd (pv b) (ci 1 tint) (tptr tulong))))
                  (.Sset c (pv dense.id.«set2»)))
                (.Sset dense.id.«set2» (.Ebinop .Oadd (pv c) (ci 1 tint) (tptr tulong))))
              (.Sset d (.Ecast (.Ebinop .Oand (.Ederef (pv b) tulong) (.Ederef (pv c) tulong) tulong)
                tulong)))
            (.Sset dense.id.«x» (.Etempvar d tulong)))
          (.Sifthenelse (.Ebinop .One (.Etempvar d tulong) (ci 0 tint) tint)
            (sk (.Sset dense.id.«cnt» (.Ebinop .Oadd (tv dense.id.«cnt») popcount tint))) .Sskip)))
      .Sskip)

abbrev guard : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Olt (.Ederef (pi dense.id.«numcells») tint) (tv dense.id.«n») tint)
        (.Ssequence
          (.Ssequence
            (sk (.Sset dense.id.«split1» (tv dense.id.«hint»)))
            (.Sifthenelse
              (isElement dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«split1»))
              (.Sset (idOf 710) (ci 1 tint))
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Scall
                        (some (idOf 711))
                        (.Evar dense.id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
                        [(pv dense.id.«active»), (tv dense.id.«m»), (tv dense.id.«split1»)]))
                    (.Sset (idOf 712) (.Ecast (tv (idOf 711)) tint)))
                  (.Sset dense.id.«split1» (tv (idOf 712))))
                (.Sset (idOf 710) (.Ecast (.Ebinop .Oge (tv (idOf 712)) (ci 0 tint) tint) tbool)))))
          (.Sifthenelse
            (tv (idOf 710))
            (sk (.Sset (idOf 709) (.Ecast (ci 1 tint) tbool)))
            (.Ssequence
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Scall
                        (some (idOf 713))
                        (.Evar dense.id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
                        [(pv dense.id.«active»), (tv dense.id.«m»), (.Eunop .Oneg (ci 1 tint) tint)]))
                    (.Sset (idOf 714) (.Ecast (tv (idOf 713)) tint)))
                  (.Sset dense.id.«split1» (tv (idOf 714))))
                (.Sset (idOf 709) (.Ecast (.Ebinop .Oge (tv (idOf 714)) (ci 0 tint) tint) tbool)))
              (.Sset (idOf 709) (.Ecast (tv (idOf 709)) tbool)))))
        (.Sset (idOf 709) (ci 0 tint))))
    (.Sifthenelse (tv (idOf 709)) .Sskip .Sbreak))

abbrev swapLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«c1») (tv dense.id.«c2») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sset dense.id.«labc1» (ix dense.id.«lab» (tv dense.id.«c1»))))
        (sk
          (.Sifthenelse
            (isElement dense.id.«gptr» dense.id.«naugraph:bit» (tv dense.id.«labc1»))
            (sk (.Sset dense.id.«c1» (.Ebinop .Oadd (tv dense.id.«c1») (ci 1 tint) tint)))
            (.Ssequence
              (sk (.Sassign (ix dense.id.«lab» (tv dense.id.«c1»)) (ix dense.id.«lab» (tv dense.id.«c2»))))
              (.Ssequence
                (sk (.Sassign (ix dense.id.«lab» (tv dense.id.«c2»)) (tv dense.id.«labc1»)))
                (sk (.Sset dense.id.«c2» (.Ebinop .Osub (tv dense.id.«c2») (ci 1 tint) tint)))))))))
    .Sskip)

abbrev trivSplit : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Oge (tv dense.id.«c2») (tv dense.id.«cell1») tint)
        (sk (.Sset (idOf 716) (.Ecast (.Ebinop .Ole (tv dense.id.«c1») (tv dense.id.«cell2») tint) tbool)))
        (.Sset (idOf 716) (ci 0 tint))))
    (.Sifthenelse
      (tv (idOf 716))
      (.Ssequence
        (sk (.Sassign (ix dense.id.«ptn» (tv dense.id.«c2»)) (tv dense.id.«level»)))
        (.Ssequence
          (sk (mash (tv dense.id.«c2»)))
          (.Ssequence
            (sk
              (.Sassign
                (.Ederef (pi dense.id.«numcells») tint)
                (.Ebinop .Oadd (.Ederef (pi dense.id.«numcells») tint) (ci 1 tint) tint)))
            (.Ssequence
              (sk
                (.Sifthenelse
                  (isElement dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«cell1»))
                  (.Sset (idOf 715) (ci 1 tint))
                  (sk
                    (.Sset
                      (idOf 715)
                      (.Ecast
                        (.Ebinop .Oge
                          (.Ebinop .Osub (tv dense.id.«c2») (tv dense.id.«cell1») tint)
                          (.Ebinop .Osub (tv dense.id.«cell2») (tv dense.id.«c1») tint)
                          tint)
                        tbool)))))
              (.Sifthenelse
                (tv (idOf 715))
                (.Ssequence
                  (addElementB dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«c1»))
                  (sk
                    (.Sifthenelse
                      (.Ebinop .Oeq (tv dense.id.«c1») (tv dense.id.«cell2») tint)
                      (sk (.Sset dense.id.«hint» (tv dense.id.«c1»)))
                      .Sskip)))
                (.Ssequence
                  (addElementB dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«cell1»))
                  (sk
                    (.Sifthenelse
                      (.Ebinop .Oeq (tv dense.id.«c2») (tv dense.id.«cell1») tint)
                      (sk (.Sset dense.id.«hint» (tv dense.id.«cell1»)))
                      .Sskip))))))))
      .Sskip))

abbrev cellLoopT : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«cell1») (tv dense.id.«n») tint) .Sskip .Sbreak))
      (.Ssequence
        (scanEnd dense.id.«cell2» dense.id.«cell1»)
        (.Ssequence
          (sk (.Sifthenelse (.Ebinop .Oeq (tv dense.id.«cell1») (tv dense.id.«cell2») tint) .Scontinue .Sskip))
          (.Ssequence
            (sk (.Sset dense.id.«c1» (tv dense.id.«cell1»)))
            (.Ssequence (sk (.Sset dense.id.«c2» (tv dense.id.«cell2»))) (.Ssequence swapLoop trivSplit))))))
    (sk (.Sset dense.id.«cell1» (.Ebinop .Oadd (tv dense.id.«cell2») (ci 1 tint) tint))))

abbrev trivial : statement :=
  (.Ssequence
    (sk
      (.Sset dense.id.«gptr»
        (.Ebinop .Oadd
          (.Ecast (pv dense.id.«g») (tptr tulong))
          (.Ebinop .Omul (tv dense.id.«m») (.Ecast (ix dense.id.«lab» (tv dense.id.«split1»)) tulong) tulong)
          (tptr tulong))))
    (.Ssequence (sk (.Sset dense.id.«cell1» (ci 0 tint))) cellLoopT))

abbrev fillWS : statement :=
  (.Ssequence
    (sk (.Sset dense.id.«i» (tv dense.id.«split1»)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«i») (tv dense.id.«split2») tint) .Sskip .Sbreak))
        (sk
          (.Sassign
            (.Ederef
              (.Ebinop .Oadd
                (.Evar dense.id.«naugraph:workset» (tptr tulong))
                (.Ebinop .Oshr (ix dense.id.«lab» (tv dense.id.«i»)) (ci 6 tint) tint)
                (tptr tulong))
              tulong)
            (.Ebinop .Oor
              (.Ederef
                (.Ebinop .Oadd
                  (.Evar dense.id.«naugraph:workset» (tptr tulong))
                  (.Ebinop .Oshr (ix dense.id.«lab» (tv dense.id.«i»)) (ci 6 tint) tint)
                  (tptr tulong))
                tulong)
              (bitOf dense.id.«naugraph:bit» (ix dense.id.«lab» (tv dense.id.«i»)))
              tulong))))
      (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint)))))

abbrev countRest : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (sk (.Sset (idOf 724) (.Ecast (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint) tint)))
          (.Sset dense.id.«i» (tv (idOf 724))))
        (.Sifthenelse (.Ebinop .Ole (tv (idOf 724)) (tv dense.id.«cell2») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sset dense.id.«set1» (.Evar dense.id.«naugraph:workset» (tptr tulong))))
        (.Ssequence
          (sk
            (.Sset dense.id.«set2»
              (.Ebinop .Oadd
                (.Ecast (pv dense.id.«g») (tptr tulong))
                (.Ebinop .Omul (tv dense.id.«m») (.Ecast (ix dense.id.«lab» (tv dense.id.«i»)) tulong) tulong)
                (tptr tulong))))
          (.Ssequence
            (sk (.Sset dense.id.«cnt» (ci 0 tint)))
            (.Ssequence
              (popLoop (idOf 725) (idOf 726) (idOf 727) (idOf 728))
              (.Ssequence
                (.Sloop
                  (.Ssequence
                    (sk
                      (.Sifthenelse (.Ebinop .Ogt (tv dense.id.«bmin») (tv dense.id.«cnt») tint) .Sskip .Sbreak))
                    (.Ssequence
                      (.Ssequence
                        (sk
                          (.Sset
                            (idOf 729)
                            (.Ecast (.Ebinop .Osub (tv dense.id.«bmin») (ci 1 tint) tint) tint)))
                        (.Sset dense.id.«bmin» (tv (idOf 729))))
                      (.Sassign (gix dense.id.«naugraph:bucket» (tv (idOf 729))) (ci 0 tint))))
                  .Sskip)
                (.Ssequence
                  (.Sloop
                    (.Ssequence
                      (sk
                        (.Sifthenelse
                          (.Ebinop .Olt (tv dense.id.«bmax») (tv dense.id.«cnt») tint)
                          .Sskip
                          .Sbreak))
                      (.Ssequence
                        (.Ssequence
                          (sk
                            (.Sset
                              (idOf 730)
                              (.Ecast (.Ebinop .Oadd (tv dense.id.«bmax») (ci 1 tint) tint) tint)))
                          (.Sset dense.id.«bmax» (tv (idOf 730))))
                        (.Sassign (gix dense.id.«naugraph:bucket» (tv (idOf 730))) (ci 0 tint))))
                    .Sskip)
                  (.Ssequence
                    (sk
                      (.Sassign
                        (gix dense.id.«naugraph:bucket» (tv dense.id.«cnt»))
                        (.Ebinop .Oadd (gix dense.id.«naugraph:bucket» (tv dense.id.«cnt»)) (ci 1 tint) tint)))
                    (sk (.Sassign (ix dense.id.«count» (tv dense.id.«i»)) (tv dense.id.«cnt»)))))))))))
    .Sskip)

abbrev scanLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«i») (tv dense.id.«bmax») tint) .Sskip .Sbreak))
      (sk
        (.Sifthenelse
          (gix dense.id.«naugraph:bucket» (tv dense.id.«i»))
          (.Ssequence
            (sk
              (.Sset dense.id.«c2»
                (.Ebinop .Oadd (tv dense.id.«c1») (gix dense.id.«naugraph:bucket» (tv dense.id.«i»)) tint)))
            (.Ssequence
              (sk (.Sassign (gix dense.id.«naugraph:bucket» (tv dense.id.«i»)) (tv dense.id.«c1»)))
              (.Ssequence
                (sk (mash (.Ebinop .Oadd (tv dense.id.«i») (tv dense.id.«c1») tint)))
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Ebinop .Ogt
                        (.Ebinop .Osub (tv dense.id.«c2») (tv dense.id.«c1») tint)
                        (tv dense.id.«maxcell»)
                        tint)
                      (.Ssequence
                        (sk (.Sset dense.id.«maxcell» (.Ebinop .Osub (tv dense.id.«c2») (tv dense.id.«c1») tint)))
                        (sk (.Sset dense.id.«maxpos» (tv dense.id.«c1»))))
                      .Sskip))
                  (.Ssequence
                    (sk
                      (.Sifthenelse
                        (.Ebinop .One (tv dense.id.«c1») (tv dense.id.«cell1») tint)
                        (.Ssequence
                          (addElementB dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«c1»))
                          (.Ssequence
                            (sk
                              (.Sifthenelse
                                (.Ebinop .Oeq
                                  (.Ebinop .Osub (tv dense.id.«c2») (tv dense.id.«c1») tint)
                                  (ci 1 tint)
                                  tint)
                                (sk (.Sset dense.id.«hint» (tv dense.id.«c1»)))
                                .Sskip))
                            (sk
                              (.Sassign
                                (.Ederef (pi dense.id.«numcells») tint)
                                (.Ebinop .Oadd (.Ederef (pi dense.id.«numcells») tint) (ci 1 tint) tint)))))
                        .Sskip))
                    (.Ssequence
                      (sk
                        (.Sifthenelse
                          (.Ebinop .Ole (tv dense.id.«c2») (tv dense.id.«cell2») tint)
                          (sk
                            (.Sassign
                              (ix dense.id.«ptn» (.Ebinop .Osub (tv dense.id.«c2») (ci 1 tint) tint))
                              (tv dense.id.«level»)))
                          .Sskip))
                      (sk (.Sset dense.id.«c1» (tv dense.id.«c2»)))))))))
          .Sskip)))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev placeLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«i») (tv dense.id.«cell2») tint) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence
          (sk (.Sset (idOf 731) (gix dense.id.«naugraph:bucket» (ix dense.id.«count» (tv dense.id.«i»)))))
          (.Sassign
            (gix dense.id.«naugraph:bucket» (ix dense.id.«count» (tv dense.id.«i»)))
            (.Ebinop .Oadd (tv (idOf 731)) (ci 1 tint) tint)))
        (.Sassign (gix dense.id.«naugraph:workperm» (tv (idOf 731))) (ix dense.id.«lab» (tv dense.id.«i»)))))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev copyLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«i») (tv dense.id.«cell2») tint) .Sskip .Sbreak))
      (sk (.Sassign (ix dense.id.«lab» (tv dense.id.«i»)) (gix dense.id.«naugraph:workperm» (tv dense.id.«i»)))))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev fixN : statement :=
  (.Sifthenelse
    (.Eunop .Onotbool (isElement dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«cell1»)) tint)
    (.Ssequence
      (addElementB dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«cell1»))
      (delElementB dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«maxpos»)))
    .Sskip)

abbrev splitN : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Oeq (tv dense.id.«bmin») (tv dense.id.«bmax») tint)
        (.Ssequence (sk (mash (.Ebinop .Oadd (tv dense.id.«bmin») (tv dense.id.«cell1») tint))) .Scontinue)
        .Sskip))
    (.Ssequence
      (sk (.Sset dense.id.«c1» (tv dense.id.«cell1»)))
      (.Ssequence
        (sk (.Sset dense.id.«maxcell» (.Eunop .Oneg (ci 1 tint) tint)))
        (.Ssequence
          (.Ssequence (sk (.Sset dense.id.«i» (tv dense.id.«bmin»))) scanLoop)
          (.Ssequence
            (.Ssequence (sk (.Sset dense.id.«i» (tv dense.id.«cell1»))) placeLoop)
            (.Ssequence (.Ssequence (sk (.Sset dense.id.«i» (tv dense.id.«cell1»))) copyLoop) (sk fixN)))))))

abbrev cellN : statement :=
  (.Ssequence
    (sk (.Sset dense.id.«i» (tv dense.id.«cell1»)))
    (.Ssequence
      (sk (.Sset dense.id.«set1» (.Evar dense.id.«naugraph:workset» (tptr tulong))))
      (.Ssequence
        (sk
          (.Sset dense.id.«set2»
            (.Ebinop .Oadd
              (.Ecast (pv dense.id.«g») (tptr tulong))
              (.Ebinop .Omul (tv dense.id.«m») (.Ecast (ix dense.id.«lab» (tv dense.id.«i»)) tulong) tulong)
              (tptr tulong))))
        (.Ssequence
          (sk (.Sset dense.id.«cnt» (ci 0 tint)))
          (.Ssequence
            (popLoop (idOf 718) (idOf 719) (idOf 720) (idOf 721))
            (.Ssequence
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (.Ssequence
                      (sk (.Sset (idOf 722) (.Ecast (tv dense.id.«cnt») tint)))
                      (.Sset dense.id.«bmax» (tv (idOf 722))))
                    (.Sset (idOf 723) (.Ecast (tv (idOf 722)) tint)))
                  (.Sset dense.id.«bmin» (tv (idOf 723))))
                (.Sassign (ix dense.id.«count» (tv dense.id.«i»)) (tv (idOf 723))))
              (.Ssequence
                (sk (.Sassign (gix dense.id.«naugraph:bucket» (tv dense.id.«cnt»)) (ci 1 tint)))
                (.Ssequence countRest splitN))))))))

abbrev cellLoopN : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«cell1») (tv dense.id.«n») tint) .Sskip .Sbreak))
      (.Ssequence
        (scanEnd dense.id.«cell2» dense.id.«cell1»)
        (.Ssequence
          (sk (.Sifthenelse (.Ebinop .Oeq (tv dense.id.«cell1») (tv dense.id.«cell2») tint) .Scontinue .Sskip))
          cellN)))
    (sk (.Sset dense.id.«cell1» (.Ebinop .Oadd (tv dense.id.«cell2») (ci 1 tint) tint))))

abbrev nontrivial : statement :=
  (.Ssequence
    (.Ssequence
      (sk
        (.Sset dense.id.«es_»
          (.Ebinop .Oadd
            (.Ecast (.Evar dense.id.«naugraph:workset» (tptr tulong)) (tptr tulong))
            (tv dense.id.«m»)
            (tptr tulong))))
      (.Sloop
        (.Ssequence
          (sk
            (.Sifthenelse
              (.Ebinop .Ogt
                (pv dense.id.«es_»)
                (.Ecast (.Evar dense.id.«naugraph:workset» (tptr tulong)) (tptr tulong))
                tint)
              .Sskip
              .Sbreak))
          (.Ssequence
            (.Ssequence
              (sk
                (.Sset
                  (idOf 717)
                  (.Ecast (.Ebinop .Osub (pv dense.id.«es_») (ci 1 tint) (tptr tulong)) (tptr tulong))))
              (.Sset dense.id.«es_» (pv (idOf 717))))
            (.Sassign (.Ederef (pv (idOf 717)) tulong) (ci 0 tint))))
        .Sskip))
    (.Ssequence fillWS
      (.Ssequence
        (sk
          (mash
            (.Ebinop .Oadd (.Ebinop .Osub (tv dense.id.«split2») (tv dense.id.«split1») tint) (ci 1 tint) tint)))
        (.Ssequence (sk (.Sset dense.id.«cell1» (ci 0 tint))) cellLoopN))))

abbrev step : statement :=
  (.Ssequence
    (delElementB dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«split1»))
    (.Ssequence
      (scanEnd dense.id.«split2» dense.id.«split1»)
      (.Ssequence
        (sk (mash (.Ebinop .Oadd (tv dense.id.«split1») (tv dense.id.«split2») tint)))
        (sk (.Sifthenelse (.Ebinop .Oeq (tv dense.id.«split1») (tv dense.id.«split2») tint) trivial nontrivial)))))

abbrev mainLoop : statement :=
  (.Sloop (.Ssequence guard step) .Sskip)

abbrev finish : statement :=
  (.Ssequence
    (sk (mash (.Ederef (pi dense.id.«numcells») tint)))
    (sk
      (.Sassign
        (.Ederef (pi dense.id.«code») tint)
        (.Ecast (.Ebinop .Omod (.Etempvar dense.id.«longcode» tlong) (ci 32767 tint) tlong) tint))))

abbrev body : statement :=
  (.Ssequence
    (dynalloc1 dense.id.«naugraph:workperm_sz» dense.id.«naugraph:workperm» tint
      (tv dense.id.«n»)
      (idOf 703)
      (idOf 704)
      dense.id.«naugraph:__stringlit_3»
      7)
    (.Ssequence
      (dynalloc1 dense.id.«naugraph:workset_sz» dense.id.«naugraph:workset» tulong
        (tv dense.id.«m»)
        (idOf 705)
        (idOf 706)
        dense.id.«naugraph:__stringlit_3»
        7)
      (.Ssequence
        (dynalloc1 dense.id.«naugraph:bucket_sz» dense.id.«naugraph:bucket» tint
          (.Ebinop .Oadd (tv dense.id.«n») (ci 2 tint) tint)
          (idOf 707)
          (idOf 708)
          dense.id.«naugraph:__stringlit_3»
          7)
        (.Ssequence
          (sk (.Sset dense.id.«longcode» (.Ecast (.Ederef (pi dense.id.«numcells») tint) tlong)))
          (.Ssequence
            (sk (.Sset dense.id.«split1» (.Eunop .Oneg (ci 1 tint) tint)))
            (.Ssequence
              (sk (.Sset dense.id.«hint» (ci 0 tint)))
              (.Ssequence (sk (.Sset dense.id.«maxpos» (ci 0 tint))) (.Ssequence mainLoop finish))))))))

kernel_rfl body_eq : dense.body.refine = body

end NautyVerified.Proofs.Refine

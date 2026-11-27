import NautyVerified.Proofs.Refine.Syntax
import NautyVerified.Proofs.Set.One

/-!
# `refine1`, factored

The Clight of naugraph.c's `refine1` (`refine` for `m = 1`), in named pieces
with the same names as `refine`'s (`Proofs/Refine/Syntax.lean`); `body_eq`
pins it to `dense.body.refine1`. The pieces were cut out by
`scripts/factor_clight.py` with `scripts/factor/refine1.py`. They differ
from `refine`'s in the one-word set macros, the literal `1` for `m`, the
temporary `workset0` for the splitter set, the one-word neighbour count, the
numbering of SimplExpr's temporaries, and the two `DYNALLOC1`s (no
`workset`).
-/

namespace NautyVerified.Proofs.Refine1

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv bit1 isElement1 addElement1 delElement1)
open NautyVerified.Proofs.Alloc (dynalloc1)
open NautyVerified.Proofs.Refine (tv pi ix gix mash scanEnd byteAt byte0 popcount)

abbrev guard : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Olt (.Ederef (pi dense.id.«numcells») tint) (tv dense.id.«n») tint)
        (.Ssequence
          (.Ssequence
            (sk (.Sset dense.id.«split1» (tv dense.id.«hint»)))
            (.Sifthenelse
              (isElement1 dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«split1»))
              (.Sset (idOf 708) (ci 1 tint))
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Scall
                        (some (idOf 709))
                        (.Evar dense.id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
                        [(pv dense.id.«active»), (ci 1 tint), (tv dense.id.«split1»)]))
                    (.Sset (idOf 710) (.Ecast (tv (idOf 709)) tint)))
                  (.Sset dense.id.«split1» (tv (idOf 710))))
                (.Sset (idOf 708) (.Ecast (.Ebinop .Oge (tv (idOf 710)) (ci 0 tint) tint) tbool)))))
          (.Sifthenelse
            (tv (idOf 708))
            (sk (.Sset (idOf 707) (.Ecast (ci 1 tint) tbool)))
            (.Ssequence
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Scall
                        (some (idOf 711))
                        (.Evar dense.id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
                        [(pv dense.id.«active»), (ci 1 tint), (.Eunop .Oneg (ci 1 tint) tint)]))
                    (.Sset (idOf 712) (.Ecast (tv (idOf 711)) tint)))
                  (.Sset dense.id.«split1» (tv (idOf 712))))
                (.Sset (idOf 707) (.Ecast (.Ebinop .Oge (tv (idOf 712)) (ci 0 tint) tint) tbool)))
              (.Sset (idOf 707) (.Ecast (tv (idOf 707)) tbool)))))
        (.Sset (idOf 707) (ci 0 tint))))
    (.Sifthenelse (tv (idOf 707)) .Sskip .Sbreak))

abbrev swapLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«c1») (tv dense.id.«c2») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sset dense.id.«labc1» (ix dense.id.«lab» (tv dense.id.«c1»))))
        (sk
          (.Sifthenelse
            (isElement1 dense.id.«gptr» dense.id.«naugraph:bit» (tv dense.id.«labc1»))
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
        (sk (.Sset (idOf 714) (.Ecast (.Ebinop .Ole (tv dense.id.«c1») (tv dense.id.«cell2») tint) tbool)))
        (.Sset (idOf 714) (ci 0 tint))))
    (.Sifthenelse
      (tv (idOf 714))
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
                  (isElement1 dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«cell1»))
                  (.Sset (idOf 713) (ci 1 tint))
                  (sk
                    (.Sset
                      (idOf 713)
                      (.Ecast
                        (.Ebinop .Oge
                          (.Ebinop .Osub (tv dense.id.«c2») (tv dense.id.«cell1») tint)
                          (.Ebinop .Osub (tv dense.id.«cell2») (tv dense.id.«c1») tint)
                          tint)
                        tbool)))))
              (.Sifthenelse
                (tv (idOf 713))
                (.Ssequence
                  (addElement1 dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«c1»))
                  (sk
                    (.Sifthenelse
                      (.Ebinop .Oeq (tv dense.id.«c1») (tv dense.id.«cell2») tint)
                      (sk (.Sset dense.id.«hint» (tv dense.id.«c1»)))
                      .Sskip)))
                (.Ssequence
                  (addElement1 dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«cell1»))
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
          (.Ebinop .Omul (ci 1 tint) (.Ecast (ix dense.id.«lab» (tv dense.id.«split1»)) tulong) tulong)
          (tptr tulong))))
    (.Ssequence (sk (.Sset dense.id.«cell1» (ci 0 tint))) cellLoopT))

abbrev countRest : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (sk (.Sset (idOf 718) (.Ecast (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint) tint)))
          (.Sset dense.id.«i» (tv (idOf 718))))
        (.Sifthenelse (.Ebinop .Ole (tv (idOf 718)) (tv dense.id.«cell2») tint) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk
              (.Sset
                (idOf 719)
                (.Ecast
                  (.Ebinop .Oand
                    (.Etempvar dense.id.«workset0» tulong)
                    (.Ederef
                      (.Ebinop .Oadd (pv dense.id.«g») (ix dense.id.«lab» (tv dense.id.«i»)) (tptr tulong))
                      tulong)
                    tulong)
                  tulong)))
            (.Sset dense.id.«x» (.Etempvar (idOf 719) tulong)))
          (.Sifthenelse
            (.Ebinop .One (.Etempvar (idOf 719) tulong) (ci 0 tint) tint)
            (sk (.Sset dense.id.«cnt» (popcount)))
            (sk (.Sset dense.id.«cnt» (ci 0 tint)))))
        (.Ssequence
          (.Sloop
            (.Ssequence
              (sk (.Sifthenelse (.Ebinop .Ogt (tv dense.id.«bmin») (tv dense.id.«cnt») tint) .Sskip .Sbreak))
              (.Ssequence
                (.Ssequence
                  (sk
                    (.Sset (idOf 720) (.Ecast (.Ebinop .Osub (tv dense.id.«bmin») (ci 1 tint) tint) tint)))
                  (.Sset dense.id.«bmin» (tv (idOf 720))))
                (.Sassign (gix dense.id.«naugraph:bucket» (tv (idOf 720))) (ci 0 tint))))
            .Sskip)
          (.Ssequence
            (.Sloop
              (.Ssequence
                (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«bmax») (tv dense.id.«cnt») tint) .Sskip .Sbreak))
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Sset
                        (idOf 721)
                        (.Ecast (.Ebinop .Oadd (tv dense.id.«bmax») (ci 1 tint) tint) tint)))
                    (.Sset dense.id.«bmax» (tv (idOf 721))))
                  (.Sassign (gix dense.id.«naugraph:bucket» (tv (idOf 721))) (ci 0 tint))))
              .Sskip)
            (.Ssequence
              (sk
                (.Sassign
                  (gix dense.id.«naugraph:bucket» (tv dense.id.«cnt»))
                  (.Ebinop .Oadd (gix dense.id.«naugraph:bucket» (tv dense.id.«cnt»)) (ci 1 tint) tint)))
              (sk (.Sassign (ix dense.id.«count» (tv dense.id.«i»)) (tv dense.id.«cnt»))))))))
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
                          (addElement1 dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«c1»))
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
          (sk (.Sset (idOf 722) (gix dense.id.«naugraph:bucket» (ix dense.id.«count» (tv dense.id.«i»)))))
          (.Sassign
            (gix dense.id.«naugraph:bucket» (ix dense.id.«count» (tv dense.id.«i»)))
            (.Ebinop .Oadd (tv (idOf 722)) (ci 1 tint) tint)))
        (.Sassign (gix dense.id.«naugraph:workperm» (tv (idOf 722))) (ix dense.id.«lab» (tv dense.id.«i»)))))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev copyLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«i») (tv dense.id.«cell2») tint) .Sskip .Sbreak))
      (sk (.Sassign (ix dense.id.«lab» (tv dense.id.«i»)) (gix dense.id.«naugraph:workperm» (tv dense.id.«i»)))))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev fixN : statement :=
  (.Sifthenelse
    (.Eunop .Onotbool (isElement1 dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«cell1»)) tint)
    (.Ssequence
      (addElement1 dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«cell1»))
      (delElement1 dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«maxpos»)))
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
      (.Ssequence
        (.Ssequence
          (sk
            (.Sset
              (idOf 715)
              (.Ecast
                (.Ebinop .Oand
                  (.Etempvar dense.id.«workset0» tulong)
                  (.Ederef
                    (.Ebinop .Oadd (pv dense.id.«g») (ix dense.id.«lab» (tv dense.id.«i»)) (tptr tulong))
                    tulong)
                  tulong)
                tulong)))
          (.Sset dense.id.«x» (.Etempvar (idOf 715) tulong)))
        (.Sifthenelse
          (.Ebinop .One (.Etempvar (idOf 715) tulong) (ci 0 tint) tint)
          (sk (.Sset dense.id.«cnt» (popcount)))
          (sk (.Sset dense.id.«cnt» (ci 0 tint)))))
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (.Ssequence
                (sk (.Sset (idOf 716) (.Ecast (tv dense.id.«cnt») tint)))
                (.Sset dense.id.«bmax» (tv (idOf 716))))
              (.Sset (idOf 717) (.Ecast (tv (idOf 716)) tint)))
            (.Sset dense.id.«bmin» (tv (idOf 717))))
          (.Sassign (ix dense.id.«count» (tv dense.id.«i»)) (tv (idOf 717))))
        (.Ssequence
          (sk (.Sassign (gix dense.id.«naugraph:bucket» (tv dense.id.«cnt»)) (ci 1 tint)))
          (.Ssequence countRest splitN)))))

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
    (sk (.Sset dense.id.«workset0» (.Ecast (ci 0 tint) tulong)))
    (.Ssequence
      (.Ssequence
        (sk (.Sset dense.id.«i» (tv dense.id.«split1»)))
        (.Sloop
          (.Ssequence
            (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«i») (tv dense.id.«split2») tint) .Sskip .Sbreak))
            (sk
              (.Sset dense.id.«workset0»
                (.Ebinop .Oor
                  (.Etempvar dense.id.«workset0» tulong)
                  (bit1 dense.id.«naugraph:bit» (ix dense.id.«lab» (tv dense.id.«i»)))
                  tulong))))
          (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint)))))
      (.Ssequence
        (sk
          (mash
            (.Ebinop .Oadd (.Ebinop .Osub (tv dense.id.«split2») (tv dense.id.«split1») tint) (ci 1 tint) tint)))
        (.Ssequence (sk (.Sset dense.id.«cell1» (ci 0 tint))) cellLoopN))))

abbrev step : statement :=
  (.Ssequence
    (delElement1 dense.id.«active» dense.id.«naugraph:bit» (tv dense.id.«split1»))
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
      dense.id.«naugraph:__stringlit_4»
      8)
    (.Ssequence
      (dynalloc1 dense.id.«naugraph:bucket_sz» dense.id.«naugraph:bucket» tint
        (.Ebinop .Oadd (tv dense.id.«n») (ci 2 tint) tint)
        (idOf 705)
        (idOf 706)
        dense.id.«naugraph:__stringlit_4»
        8)
      (.Ssequence
        (sk (.Sset dense.id.«longcode» (.Ecast (.Ederef (pi dense.id.«numcells») tint) tlong)))
        (.Ssequence
          (sk (.Sset dense.id.«split1» (.Eunop .Oneg (ci 1 tint) tint)))
          (.Ssequence
            (sk (.Sset dense.id.«maxpos» (ci 0 tint)))
            (.Ssequence (sk (.Sset dense.id.«hint» (ci 0 tint))) (.Ssequence mainLoop finish)))))))

kernel_rfl body_eq : dense.body.refine1 = body

end NautyVerified.Proofs.Refine1

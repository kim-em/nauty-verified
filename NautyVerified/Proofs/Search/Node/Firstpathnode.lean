import NautyVerified.Proofs.Refine.Syntax
import NautyVerified.Word.Repr

/-!
# `firstpathnode0`, factored

The Clight of nauty.c's `firstpathnode0`, cut by `scripts/factor_clight.py` with
`scripts/factor/firstpathnode.py`; `body_eq` pins it to `dense.body.«nauty:firstpathnode0»`.
-/

namespace NautyVerified.Proofs.Search.Firstpathnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv)

abbrev tcalloc : statement :=
  (.Sifthenelse
    (.Ebinop .Oeq
      (.Etempvar dense.id.«tcnode_this» (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
      (.Ecast (ci 0 tint) (tptr .Tvoid))
      tint)
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (sk
                (.Scall
                  (some (idOf 703))
                  (.Evar dense.id.«nauty_zalloc» (tfun [tulong] (tptr .Tvoid)))
                  [(.Ebinop .Omul
                     (.Ecast (ci 1 tint) tulong)
                     (.Ecast (.Esizeof (Tstruct dense.id.«tcnode_struct» noattr) tulong) tulong)
                     tulong)]))
              (.Sset
                (idOf 704)
                (.Ecast
                  (.Ecast
                    (.Etempvar (idOf 703) (tptr .Tvoid))
                    (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
                  (tptr (Tstruct dense.id.«tcnode_struct» noattr)))))
            (.Sset dense.id.«tcnode_this»
              (.Etempvar (idOf 704) (tptr (Tstruct dense.id.«tcnode_struct» noattr)))))
          (.Sifthenelse
            (.Ebinop .Oeq
              (.Etempvar (idOf 704) (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
              (.Ecast (ci 0 tint) (tptr .Tvoid))
              tint)
            (.Sset (idOf 705) (ci 1 tint))
            (.Ssequence
              (.Ssequence
                (.Ssequence
                  (sk
                    (.Scall
                      (some (idOf 706))
                      (.Evar dense.id.«nauty_zalloc» (tfun [tulong] (tptr .Tvoid)))
                      [(.Ebinop .Omul
                         (.Ecast (.Evar dense.id.«nauty:alloc_m» tint) tulong)
                         (.Ecast (.Esizeof tulong tulong) tulong)
                         tulong)]))
                  (.Sset
                    (idOf 707)
                    (.Ecast
                      (.Ecast (.Etempvar (idOf 706) (tptr .Tvoid)) (tptr tulong))
                      (tptr tulong))))
                (.Sassign
                  (.Efield
                    (.Ederef
                      (.Etempvar dense.id.«tcnode_this» (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
                      (Tstruct dense.id.«tcnode_struct» noattr))
                    dense.id.«tcellptr»
                    (tptr tulong))
                  (.Etempvar (idOf 707) (tptr tulong))))
              (.Sset
                (idOf 705)
                (.Ecast
                  (.Ebinop .Oeq
                    (.Etempvar (idOf 707) (tptr tulong))
                    (.Ecast (ci 0 tint) (tptr .Tvoid))
                    tint)
                  tbool)))))
        (.Sifthenelse
          (tv (idOf 705))
          (sk
            (.Scall none
              (.Evar dense.id.«alloc_error» (tfun [(tptr tschar)] .Tvoid))
              [(.Evar dense.id.«nauty:__stringlit_8» (tarray tschar 6))]))
          .Sskip))
      (.Ssequence
        (sk
          (.Sassign
            (.Efield
              (.Ederef
                (.Etempvar dense.id.«tcnode_parent» (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
                (Tstruct dense.id.«tcnode_struct» noattr))
              dense.id.«next»
              (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
            (.Etempvar dense.id.«tcnode_this» (tptr (Tstruct dense.id.«tcnode_struct» noattr)))))
        (sk
          (.Sassign
            (.Efield
              (.Ederef
                (.Etempvar dense.id.«tcnode_this» (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
                (Tstruct dense.id.«tcnode_struct» noattr))
              dense.id.«next»
              (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
            (.Ecast (ci 0 tint) (tptr .Tvoid))))))
    .Sskip)

abbrev invstat : statement :=
  (.Sifthenelse
    (.Ebinop .Ogt (.Evar dense.id.«qinvar» tint) (ci 0 tint) tint)
    (.Ssequence
      (sk
        (.Sassign
          (.Evar dense.id.«nauty:invapplics» tulong)
          (.Ebinop .Oadd (.Evar dense.id.«nauty:invapplics» tulong) (ci 1 tint) tulong)))
      (sk
        (.Sifthenelse
          (.Ebinop .Oeq (.Evar dense.id.«qinvar» tint) (ci 2 tint) tint)
          (.Ssequence
            (sk
              (.Sassign
                (.Evar dense.id.«nauty:invsuccesses» tulong)
                (.Ebinop .Oadd (.Evar dense.id.«nauty:invsuccesses» tulong) (ci 1 tint) tulong)))
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .Olt (.Evar dense.id.«nauty:mininvarlevel» tint) (ci 0 tint) tint)
                  (sk (.Sassign (.Evar dense.id.«nauty:mininvarlevel» tint) (tv dense.id.«level»)))
                  .Sskip))
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Ebinop .Olt (.Evar dense.id.«nauty:maxinvarlevel» tint) (ci 0 tint) tint)
                    (sk (.Sassign (.Evar dense.id.«nauty:maxinvarlevel» tint) (tv dense.id.«level»)))
                    .Sskip))
                (sk
                  (.Sifthenelse
                    (.Ebinop .Olt (tv dense.id.«level») (.Evar dense.id.«nauty:invarsuclevel» tint) tint)
                    (sk (.Sassign (.Evar dense.id.«nauty:invarsuclevel» tint) (tv dense.id.«level»)))
                    .Sskip)))))
          .Sskip)))
    .Sskip)

abbrev target : statement :=
  (.Sifthenelse
    (.Ebinop .One (.Evar dense.id.«numcells» tint) (.Evar dense.id.«nauty:n» tint) tint)
    (.Ssequence
      (sk
        (.Scall none
          (.Evar dense.id.«maketargetcell»
            (tfun
              [(tptr tulong),
               (tptr tint),
               (tptr tint),
               tint,
               (tptr tulong),
               (tptr tint),
               (tptr tint),
               tint,
               tint,
               tint,
               (tptr
                 (tfun
                   [(tptr tulong), (tptr tint), (tptr tint), tint, tint, tint, tint, tint, tint]
                   tint)),
               tint,
               tint]
              .Tvoid))
          [(.Evar dense.id.«nauty:g» (tptr tulong)),
           (.Etempvar dense.id.«lab» (tptr tint)),
           (.Etempvar dense.id.«ptn» (tptr tint)),
           (tv dense.id.«level»),
           (.Etempvar dense.id.«tcell» (tptr tulong)),
           (.Eaddrof (.Evar dense.id.«tcellsize» tint) (tptr tint)),
           (.Eaddrof (.Evar dense.id.«tc» tint) (tptr tint)),
           (.Evar dense.id.«nauty:tc_level» tint),
           (.Evar dense.id.«nauty:digraph» tint),
           (.Eunop .Oneg (ci 1 tint) tint),
           (.Efield
             (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr))
             dense.id.«targetcell»
             (tptr
               (tfun
                 [(tptr tulong), (tptr tint), (tptr tint), tint, tint, tint, tint, tint, tint]
                 tint))),
           (.Evar dense.id.«nauty:m» tint),
           (.Evar dense.id.«nauty:n» tint)]))
      (sk
        (.Sassign
          (.Efield
            (.Ederef
              (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
              (Tstruct dense.id.«_1024» noattr))
            dense.id.«tctotal»
            tulong)
          (.Ebinop .Oadd
            (.Efield
              (.Ederef
                (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
                (Tstruct dense.id.«_1024» noattr))
              dense.id.«tctotal»
              tulong)
            (.Evar dense.id.«tcellsize» tint)
            tulong))))
    .Sskip)

abbrev leaf : statement :=
  (.Sifthenelse
    (.Ebinop .Oeq (.Evar dense.id.«numcells» tint) (.Evar dense.id.«nauty:n» tint) tint)
    (.Ssequence
      (sk
        (.Scall none
          (.Evar dense.id.«nauty:firstterminal» (tfun [(tptr tint), tint] .Tvoid))
          [(.Etempvar dense.id.«lab» (tptr tint)), (tv dense.id.«level»)]))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .One
              (.Evar dense.id.«nauty:userlevelproc»
                (tptr
                  (tfun
                    [(tptr tint),
                     (tptr tint),
                     tint,
                     (tptr tint),
                     (tptr (Tstruct dense.id.«_1024» noattr)),
                     tint,
                     tint,
                     tint,
                     tint,
                     tint,
                     tint]
                    .Tvoid)))
              (.Ecast (ci 0 tint) (tptr .Tvoid))
              tint)
            (sk
              (.Scall none
                (.Ederef
                  (.Evar dense.id.«nauty:userlevelproc»
                    (tptr
                      (tfun
                        [(tptr tint),
                         (tptr tint),
                         tint,
                         (tptr tint),
                         (tptr (Tstruct dense.id.«_1024» noattr)),
                         tint,
                         tint,
                         tint,
                         tint,
                         tint,
                         tint]
                        .Tvoid)))
                  (tfun
                    [(tptr tint),
                     (tptr tint),
                     tint,
                     (tptr tint),
                     (tptr (Tstruct dense.id.«_1024» noattr)),
                     tint,
                     tint,
                     tint,
                     tint,
                     tint,
                     tint]
                    .Tvoid))
                [(.Etempvar dense.id.«lab» (tptr tint)),
                 (.Etempvar dense.id.«ptn» (tptr tint)),
                 (tv dense.id.«level»),
                 (.Evar dense.id.«nauty:orbits» (tptr tint)),
                 (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr))),
                 (ci 0 tint),
                 (ci 1 tint),
                 (ci 1 tint),
                 (.Evar dense.id.«nauty:n» tint),
                 (ci 0 tint),
                 (.Evar dense.id.«nauty:n» tint)]))
            .Sskip))
        (.Ssequence
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Evar dense.id.«nauty:getcanon» tint)
                (sk
                  (.Sset
                    (idOf 709)
                    (.Ecast
                      (.Ebinop .One
                        (.Evar dense.id.«nauty:usercanonproc»
                          (tptr
                            (tfun
                              [(tptr tulong), (tptr tint), (tptr tulong), tulong, tint, tint, tint]
                              tint)))
                        (.Ecast (ci 0 tint) (tptr .Tvoid))
                        tint)
                      tbool)))
                (.Sset (idOf 709) (ci 0 tint))))
            (.Sifthenelse
              (tv (idOf 709))
              (.Ssequence
                (sk
                  (.Scall none
                    (.Ederef
                      (.Efield
                        (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr))
                        dense.id.«updatecan»
                        (tptr
                          (tfun [(tptr tulong), (tptr tulong), (tptr tint), tint, tint, tint] .Tvoid)))
                      (tfun [(tptr tulong), (tptr tulong), (tptr tint), tint, tint, tint] .Tvoid))
                    [(.Evar dense.id.«nauty:g» (tptr tulong)),
                     (.Evar dense.id.«nauty:canong» (tptr tulong)),
                     (.Evar dense.id.«nauty:canonlab» (tptr tint)),
                     (.Evar dense.id.«nauty:samerows» tint),
                     (.Evar dense.id.«nauty:m» tint),
                     (.Evar dense.id.«nauty:n» tint)]))
                (.Ssequence
                  (sk (.Sassign (.Evar dense.id.«nauty:samerows» tint) (.Evar dense.id.«nauty:n» tint)))
                  (.Ssequence
                    (sk
                      (.Scall
                        (some (idOf 708))
                        (.Ederef
                          (.Evar dense.id.«nauty:usercanonproc»
                            (tptr
                              (tfun
                                [(tptr tulong),
                                 (tptr tint),
                                 (tptr tulong),
                                 tulong,
                                 tint,
                                 tint,
                                 tint]
                                tint)))
                          (tfun
                            [(tptr tulong), (tptr tint), (tptr tulong), tulong, tint, tint, tint]
                            tint))
                        [(.Evar dense.id.«nauty:g» (tptr tulong)),
                         (.Evar dense.id.«nauty:canonlab» (tptr tint)),
                         (.Evar dense.id.«nauty:canong» (tptr tulong)),
                         (.Efield
                           (.Ederef
                             (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
                             (Tstruct dense.id.«_1024» noattr))
                           dense.id.«canupdates»
                           tulong),
                         (.Ecast
                           (.Ederef
                             (.Ebinop .Oadd
                               (.Evar dense.id.«nauty:canoncode» (tptr tshort))
                               (tv dense.id.«level»)
                               (tptr tshort))
                             tshort)
                           tint),
                         (.Evar dense.id.«nauty:m» tint),
                         (.Evar dense.id.«nauty:n» tint)]))
                    (.Sifthenelse
                      (tv (idOf 708))
                      (sk (.Sreturn (some (.Eunop .Oneg (ci 11 tint) tint))))
                      .Sskip))))
              .Sskip))
          (sk (.Sreturn (some (.Ebinop .Osub (tv dense.id.«level») (ci 1 tint) tint)))))))
    .Sskip)

abbrev cheap : statement :=
  (.Sifthenelse
    (.Ebinop .Oge (.Evar dense.id.«nauty:noncheaplevel» tint) (tv dense.id.«level») tint)
    (.Ssequence
      (sk
        (.Scall
          (some (idOf 712))
          (.Ederef
            (.Efield
              (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr))
              dense.id.«cheapautom»
              (tptr (tfun [(tptr tint), tint, tint, tint] tint)))
            (tfun [(tptr tint), tint, tint, tint] tint))
          [(.Etempvar dense.id.«ptn» (tptr tint)),
           (tv dense.id.«level»),
           (.Evar dense.id.«nauty:digraph» tint),
           (.Evar dense.id.«nauty:n» tint)]))
      (.Sset (idOf 711) (.Ecast (.Eunop .Onotbool (tv (idOf 712)) tint) tbool)))
    (.Sset (idOf 711) (ci 0 tint)))

abbrev child : statement :=
  (.Sifthenelse
    (.Ebinop .Oeq
      (.Ederef (.Ebinop .Oadd (.Evar dense.id.«nauty:orbits» (tptr tint)) (tv dense.id.«tv») (tptr tint)) tint)
      (tv dense.id.«tv»)
      tint)
    (.Ssequence
      (sk
        (.Scall none
          (.Evar dense.id.«breakout»
            (tfun [(tptr tint), (tptr tint), tint, tint, tint, (tptr tulong), tint] .Tvoid))
          [(.Etempvar dense.id.«lab» (tptr tint)),
           (.Etempvar dense.id.«ptn» (tptr tint)),
           (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint),
           (.Evar dense.id.«tc» tint),
           (tv dense.id.«tv»),
           (.Evar dense.id.«nauty:active» (tptr tulong)),
           (.Evar dense.id.«nauty:m» tint)]))
      (.Ssequence
        (sk
          (.Sassign
            (.Ederef
              (.Ebinop .Oadd
                (.Evar dense.id.«nauty:fixedpts» (tptr tulong))
                (.Ebinop .Oshr (tv dense.id.«tv») (ci 6 tint) tint)
                (tptr tulong))
              tulong)
            (.Ebinop .Oor
              (.Ederef
                (.Ebinop .Oadd
                  (.Evar dense.id.«nauty:fixedpts» (tptr tulong))
                  (.Ebinop .Oshr (tv dense.id.«tv») (ci 6 tint) tint)
                  (tptr tulong))
                tulong)
              (.Ederef
                (.Ebinop .Oadd
                  (.Evar dense.id.«nauty:bit» (tarray tulong 64))
                  (.Ebinop .Oand (tv dense.id.«tv») (ci 63 tint) tint)
                  (tptr tulong))
                tulong)
              tulong)))
        (.Ssequence
          (sk (.Sassign (.Evar dense.id.«nauty:cosetindex» tint) (tv dense.id.«tv»)))
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .Oeq (tv dense.id.«tv») (tv dense.id.«tv1») tint)
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Scall
                        (some (idOf 716))
                        (.Evar dense.id.«nauty:firstpathnode0»
                          (tfun
                            [(tptr tint),
                             (tptr tint),
                             tint,
                             tint,
                             (tptr (Tstruct dense.id.«tcnode_struct» noattr))]
                            tint))
                        [(.Etempvar dense.id.«lab» (tptr tint)),
                         (.Etempvar dense.id.«ptn» (tptr tint)),
                         (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint),
                         (.Ebinop .Oadd (.Evar dense.id.«numcells» tint) (ci 1 tint) tint),
                         (.Etempvar dense.id.«tcnode_this» (tptr (Tstruct dense.id.«tcnode_struct» noattr)))]))
                    (.Sset dense.id.«rtnlevel» (tv (idOf 716))))
                  (.Ssequence
                    (sk (.Sset dense.id.«childcount» (ci 1 tint)))
                    (.Ssequence
                      (sk (.Sassign (.Evar dense.id.«nauty:gca_first» tint) (tv dense.id.«level»)))
                      (sk (.Sassign (.Evar dense.id.«nauty:stabvertex» tint) (tv dense.id.«tv1»))))))
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Scall
                        (some (idOf 717))
                        (.Evar dense.id.«nauty:othernode0»
                          (tfun
                            [(tptr tint),
                             (tptr tint),
                             tint,
                             tint,
                             (tptr (Tstruct dense.id.«tcnode_struct» noattr))]
                            tint))
                        [(.Etempvar dense.id.«lab» (tptr tint)),
                         (.Etempvar dense.id.«ptn» (tptr tint)),
                         (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint),
                         (.Ebinop .Oadd (.Evar dense.id.«numcells» tint) (ci 1 tint) tint),
                         (.Etempvar dense.id.«tcnode_this» (tptr (Tstruct dense.id.«tcnode_struct» noattr)))]))
                    (.Sset dense.id.«rtnlevel» (tv (idOf 717))))
                  (sk (.Sset dense.id.«childcount» (.Ebinop .Oadd (tv dense.id.«childcount») (ci 1 tint) tint))))))
            (.Ssequence
              (sk
                (.Sassign
                  (.Ederef
                    (.Ebinop .Oadd
                      (.Evar dense.id.«nauty:fixedpts» (tptr tulong))
                      (.Ebinop .Oshr (tv dense.id.«tv») (ci 6 tint) tint)
                      (tptr tulong))
                    tulong)
                  (.Ebinop .Oand
                    (.Ederef
                      (.Ebinop .Oadd
                        (.Evar dense.id.«nauty:fixedpts» (tptr tulong))
                        (.Ebinop .Oshr (tv dense.id.«tv») (ci 6 tint) tint)
                        (tptr tulong))
                      tulong)
                    (.Eunop .Onotint
                      (.Ederef
                        (.Ebinop .Oadd
                          (.Evar dense.id.«nauty:bit» (tarray tulong 64))
                          (.Ebinop .Oand (tv dense.id.«tv») (ci 63 tint) tint)
                          (tptr tulong))
                        tulong)
                      tulong)
                    tulong)))
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Ebinop .Olt (tv dense.id.«rtnlevel») (tv dense.id.«level») tint)
                    (sk (.Sreturn (some (tv dense.id.«rtnlevel»))))
                    .Sskip))
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Evar dense.id.«nauty:needshortprune» tint)
                      (.Ssequence
                        (sk (.Sassign (.Evar dense.id.«nauty:needshortprune» tint) (ci 0 tint)))
                        (sk
                          (.Scall none
                            (.Evar dense.id.«shortprune»
                              (tfun [(tptr tulong), (tptr tulong), tint] .Tvoid))
                            [(.Etempvar dense.id.«tcell» (tptr tulong)),
                             (.Ebinop .Osub
                               (.Evar dense.id.«nauty:fmptr» (tptr tulong))
                               (.Evar dense.id.«nauty:m» tint)
                               (tptr tulong)),
                             (.Evar dense.id.«nauty:m» tint)])))
                      .Sskip))
                  (sk
                    (.Scall none
                      (.Evar dense.id.«nauty:recover» (tfun [(tptr tint), tint] .Tvoid))
                      [(.Etempvar dense.id.«ptn» (tptr tint)), (tv dense.id.«level»)])))))))))
    .Sskip)

abbrev childLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Oge (tv dense.id.«tv») (ci 0 tint) tint) .Sskip .Sbreak))
      (.Ssequence
        (sk child)
        (sk
          (.Sifthenelse
            (.Ebinop .Oeq
              (.Ederef
                (.Ebinop .Oadd (.Evar dense.id.«nauty:orbits» (tptr tint)) (tv dense.id.«tv») (tptr tint))
                tint)
              (tv dense.id.«tv1»)
              tint)
            (sk (.Sset dense.id.«index» (.Ebinop .Oadd (tv dense.id.«index») (ci 1 tint) tint)))
            .Sskip))))
    (.Ssequence
      (sk
        (.Scall
          (some (idOf 715))
          (.Evar dense.id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
          [(.Etempvar dense.id.«tcell» (tptr tulong)), (.Evar dense.id.«nauty:m» tint), (tv dense.id.«tv»)]))
      (.Sset dense.id.«tv» (tv (idOf 715)))))

abbrev grpsize : statement :=
  (.Sifthenelse
    (.Ebinop .Oge
      (.Etempvar (idOf 718) tdouble)
      (.Econst_float
        (CompCert4Lean.Lib.Floats.Float.of_bits (NautyVerified.Word.lr 4756540486875873280))
        tdouble)
      tint)
    (.Ssequence
      (sk
        (.Sassign
          (.Efield
            (.Ederef
              (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
              (Tstruct dense.id.«_1024» noattr))
            dense.id.«grpsize1»
            tdouble)
          (.Ebinop .Odiv
            (.Efield
              (.Ederef
                (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
                (Tstruct dense.id.«_1024» noattr))
              dense.id.«grpsize1»
              tdouble)
            (.Econst_float
              (CompCert4Lean.Lib.Floats.Float.of_bits (NautyVerified.Word.lr 4756540486875873280))
              tdouble)
            tdouble)))
      (sk
        (.Sassign
          (.Efield
            (.Ederef
              (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
              (Tstruct dense.id.«_1024» noattr))
            dense.id.«grpsize2»
            tint)
          (.Ebinop .Oadd
            (.Efield
              (.Ederef
                (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
                (Tstruct dense.id.«_1024» noattr))
              dense.id.«grpsize2»
              tint)
            (ci 10 tint)
            tint))))
    .Sskip)

abbrev allsame : statement :=
  (.Sifthenelse
    (.Ebinop .Oeq (.Evar dense.id.«tcellsize» tint) (tv dense.id.«index») tint)
    (sk
      (.Sset
        (idOf 719)
        (.Ecast
          (.Ebinop .Oeq
            (.Evar dense.id.«nauty:allsamelevel» tint)
            (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint)
            tint)
          tbool)))
    (.Sset (idOf 719) (ci 0 tint)))

abbrev body : statement :=
  (.Ssequence
    (.Sassign (.Evar dense.id.«numcells» tint) (tv dense.id.«numcells»))
    (.Ssequence
      (sk
        (.Sset dense.id.«tcnode_this»
          (.Efield
            (.Ederef
              (.Etempvar dense.id.«tcnode_parent» (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
              (Tstruct dense.id.«tcnode_struct» noattr))
            dense.id.«next»
            (tptr (Tstruct dense.id.«tcnode_struct» noattr)))))
      (.Ssequence
        (sk tcalloc)
        (.Ssequence
          (sk
            (.Sset dense.id.«tcell»
              (.Efield
                (.Ederef
                  (.Etempvar dense.id.«tcnode_this» (tptr (Tstruct dense.id.«tcnode_struct» noattr)))
                  (Tstruct dense.id.«tcnode_struct» noattr))
                dense.id.«tcellptr»
                (tptr tulong))))
          (.Ssequence
            (sk
              (.Sassign
                (.Efield
                  (.Ederef
                    (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
                    (Tstruct dense.id.«_1024» noattr))
                  dense.id.«numnodes»
                  tulong)
                (.Ebinop .Oadd
                  (.Efield
                    (.Ederef
                      (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
                      (Tstruct dense.id.«_1024» noattr))
                    dense.id.«numnodes»
                    tulong)
                  (ci 1 tint)
                  tulong)))
            (.Ssequence
              (sk
                (.Scall none
                  (.Evar dense.id.«doref»
                    (tfun
                      [(tptr tulong),
                       (tptr tint),
                       (tptr tint),
                       tint,
                       (tptr tint),
                       (tptr tint),
                       (tptr tint),
                       (tptr tulong),
                       (tptr tint),
                       (tptr
                         (tfun
                           [(tptr tulong),
                            (tptr tint),
                            (tptr tint),
                            tint,
                            (tptr tint),
                            (tptr tint),
                            (tptr tulong),
                            (tptr tint),
                            tint,
                            tint]
                           .Tvoid)),
                       (tptr
                         (tfun
                           [(tptr tulong),
                            (tptr tint),
                            (tptr tint),
                            tint,
                            tint,
                            tint,
                            (tptr tint),
                            tint,
                            tint,
                            tint,
                            tint]
                           .Tvoid)),
                       tint,
                       tint,
                       tint,
                       tint,
                       tint,
                       tint]
                      .Tvoid))
                  [(.Evar dense.id.«nauty:g» (tptr tulong)),
                   (.Etempvar dense.id.«lab» (tptr tint)),
                   (.Etempvar dense.id.«ptn» (tptr tint)),
                   (tv dense.id.«level»),
                   (.Eaddrof (.Evar dense.id.«numcells» tint) (tptr tint)),
                   (.Eaddrof (.Evar dense.id.«qinvar» tint) (tptr tint)),
                   (.Evar dense.id.«nauty:workperm» (tptr tint)),
                   (.Evar dense.id.«nauty:active» (tptr tulong)),
                   (.Eaddrof (.Evar dense.id.«refcode» tint) (tptr tint)),
                   (.Efield
                     (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr))
                     dense.id.«refine»
                     (tptr
                       (tfun
                         [(tptr tulong),
                          (tptr tint),
                          (tptr tint),
                          tint,
                          (tptr tint),
                          (tptr tint),
                          (tptr tulong),
                          (tptr tint),
                          tint,
                          tint]
                         .Tvoid))),
                   (.Evar dense.id.«nauty:invarproc»
                     (tptr
                       (tfun
                         [(tptr tulong),
                          (tptr tint),
                          (tptr tint),
                          tint,
                          tint,
                          tint,
                          (tptr tint),
                          tint,
                          tint,
                          tint,
                          tint]
                         .Tvoid))),
                   (.Evar dense.id.«nauty:mininvarlevel» tint),
                   (.Evar dense.id.«nauty:maxinvarlevel» tint),
                   (.Evar dense.id.«nauty:invararg» tint),
                   (.Evar dense.id.«nauty:digraph» tint),
                   (.Evar dense.id.«nauty:m» tint),
                   (.Evar dense.id.«nauty:n» tint)]))
              (.Ssequence
                (sk
                  (.Sassign
                    (.Ederef
                      (.Ebinop .Oadd
                        (.Evar dense.id.«nauty:firstcode» (tptr tshort))
                        (tv dense.id.«level»)
                        (tptr tshort))
                      tshort)
                    (.Ecast (.Evar dense.id.«refcode» tint) tshort)))
                (.Ssequence
                  (sk invstat)
                  (.Ssequence
                    (sk (.Sassign (.Evar dense.id.«tc» tint) (.Eunop .Oneg (ci 1 tint) tint)))
                    (.Ssequence
                      (sk target)
                      (.Ssequence
                        (sk
                          (.Sassign
                            (.Ederef
                              (.Ebinop .Oadd
                                (.Evar dense.id.«nauty:firsttc» (tptr tint))
                                (tv dense.id.«level»)
                                (tptr tint))
                              tint)
                            (.Evar dense.id.«tc» tint)))
                        (.Ssequence
                          (sk
                            (.Sifthenelse
                              (.Ebinop .One
                                (.Evar dense.id.«nauty:usernodeproc»
                                  (tptr
                                    (tfun
                                      [(tptr tulong),
                                       (tptr tint),
                                       (tptr tint),
                                       tint,
                                       tint,
                                       tint,
                                       tint,
                                       tint,
                                       tint]
                                      .Tvoid)))
                                (.Ecast (ci 0 tint) (tptr .Tvoid))
                                tint)
                              (sk
                                (.Scall none
                                  (.Ederef
                                    (.Evar dense.id.«nauty:usernodeproc»
                                      (tptr
                                        (tfun
                                          [(tptr tulong),
                                           (tptr tint),
                                           (tptr tint),
                                           tint,
                                           tint,
                                           tint,
                                           tint,
                                           tint,
                                           tint]
                                          .Tvoid)))
                                    (tfun
                                      [(tptr tulong),
                                       (tptr tint),
                                       (tptr tint),
                                       tint,
                                       tint,
                                       tint,
                                       tint,
                                       tint,
                                       tint]
                                      .Tvoid))
                                  [(.Evar dense.id.«nauty:g» (tptr tulong)),
                                   (.Etempvar dense.id.«lab» (tptr tint)),
                                   (.Etempvar dense.id.«ptn» (tptr tint)),
                                   (tv dense.id.«level»),
                                   (.Evar dense.id.«numcells» tint),
                                   (.Evar dense.id.«tc» tint),
                                   (.Ecast
                                     (.Ederef
                                       (.Ebinop .Oadd
                                         (.Evar dense.id.«nauty:firstcode» (tptr tshort))
                                         (tv dense.id.«level»)
                                         (tptr tshort))
                                       tshort)
                                     tint),
                                   (.Evar dense.id.«nauty:m» tint),
                                   (.Evar dense.id.«nauty:n» tint)]))
                              .Sskip))
                          (.Ssequence
                            (sk leaf)
                            (.Ssequence
                              (.Ssequence
                                (sk
                                  (.Sbuiltin
                                    (some (idOf 710))
                                    (.EF_vload .Mint32)
                                    [(tptr (Tint .I32 .Signed vattr))]
                                    [(.Eaddrof
                                       (.Evar dense.id.«nauty_kill_request» (Tint .I32 .Signed vattr))
                                       (tptr (Tint .I32 .Signed vattr)))]))
                                (.Sifthenelse
                                  (.Etempvar (idOf 710) (Tint .I32 .Signed vattr))
                                  (sk (.Sreturn (some (.Eunop .Oneg (ci 12 tint) tint))))
                                  .Sskip))
                              (.Ssequence
                                (.Ssequence
                                  (sk cheap)
                                  (.Sifthenelse
                                    (tv (idOf 711))
                                    (sk
                                      (.Sassign
                                        (.Evar dense.id.«nauty:noncheaplevel» tint)
                                        (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint)))
                                    .Sskip))
                                (.Ssequence
                                  (sk (.Sset dense.id.«index» (ci 0 tint)))
                                  (.Ssequence
                                    (sk (.Sset dense.id.«childcount» (ci 0 tint)))
                                    (.Ssequence
                                      (.Ssequence
                                        (.Ssequence
                                          (.Ssequence
                                            (.Ssequence
                                              (sk
                                                (.Scall
                                                  (some (idOf 713))
                                                  (.Evar dense.id.«nextelement»
                                                    (tfun [(tptr tulong), tint, tint] tint))
                                                  [(.Etempvar dense.id.«tcell» (tptr tulong)),
                                                   (.Evar dense.id.«nauty:m» tint),
                                                   (.Eunop .Oneg (ci 1 tint) tint)]))
                                              (.Sset (idOf 714) (.Ecast (tv (idOf 713)) tint)))
                                            (.Sset dense.id.«tv» (tv (idOf 714))))
                                          (.Sset dense.id.«tv1» (tv (idOf 714))))
                                        childLoop)
                                      (.Ssequence
                                        (.Ssequence
                                          (.Ssequence
                                            (sk
                                              (.Sset
                                                (idOf 718)
                                                (.Ecast
                                                  (.Ebinop .Omul
                                                    (.Efield
                                                      (.Ederef
                                                        (.Evar dense.id.«nauty:stats»
                                                          (tptr (Tstruct dense.id.«_1024» noattr)))
                                                        (Tstruct dense.id.«_1024» noattr))
                                                      dense.id.«grpsize1»
                                                      tdouble)
                                                    (tv dense.id.«index»)
                                                    tdouble)
                                                  tdouble)))
                                            (.Sassign
                                              (.Efield
                                                (.Ederef
                                                  (.Evar dense.id.«nauty:stats»
                                                    (tptr (Tstruct dense.id.«_1024» noattr)))
                                                  (Tstruct dense.id.«_1024» noattr))
                                                dense.id.«grpsize1»
                                                tdouble)
                                              (.Etempvar (idOf 718) tdouble)))
                                          grpsize)
                                        (.Ssequence
                                          (.Ssequence
                                            (sk allsame)
                                            (.Sifthenelse
                                              (tv (idOf 719))
                                              (sk
                                                (.Sassign
                                                  (.Evar dense.id.«nauty:allsamelevel» tint)
                                                  (.Ebinop .Osub
                                                    (.Evar dense.id.«nauty:allsamelevel» tint)
                                                    (ci 1 tint)
                                                    tint)))
                                              .Sskip))
                                          (.Ssequence
                                            (sk
                                              (.Sifthenelse
                                                (.Evar dense.id.«nauty:domarkers» tint)
                                                (sk
                                                  (.Scall none
                                                    (.Evar dense.id.«nauty:writemarker»
                                                      (tfun
                                                        [tint, tint, tint, tint, tint, tint]
                                                        .Tvoid))
                                                    [(tv dense.id.«level»),
                                                     (tv dense.id.«tv1»),
                                                     (tv dense.id.«index»),
                                                     (.Evar dense.id.«tcellsize» tint),
                                                     (.Efield
                                                       (.Ederef
                                                         (.Evar dense.id.«nauty:stats»
                                                           (tptr (Tstruct dense.id.«_1024» noattr)))
                                                         (Tstruct dense.id.«_1024» noattr))
                                                       dense.id.«numorbits»
                                                       tint),
                                                     (.Evar dense.id.«numcells» tint)]))
                                                .Sskip))
                                            (.Ssequence
                                              (sk
                                                (.Sifthenelse
                                                  (.Ebinop .One
                                                    (.Evar dense.id.«nauty:userlevelproc»
                                                      (tptr
                                                        (tfun
                                                          [(tptr tint),
                                                           (tptr tint),
                                                           tint,
                                                           (tptr tint),
                                                           (tptr (Tstruct dense.id.«_1024» noattr)),
                                                           tint,
                                                           tint,
                                                           tint,
                                                           tint,
                                                           tint,
                                                           tint]
                                                          .Tvoid)))
                                                    (.Ecast (ci 0 tint) (tptr .Tvoid))
                                                    tint)
                                                  (sk
                                                    (.Scall none
                                                      (.Ederef
                                                        (.Evar dense.id.«nauty:userlevelproc»
                                                          (tptr
                                                            (tfun
                                                              [(tptr tint),
                                                               (tptr tint),
                                                               tint,
                                                               (tptr tint),
                                                               (tptr (Tstruct dense.id.«_1024» noattr)),
                                                               tint,
                                                               tint,
                                                               tint,
                                                               tint,
                                                               tint,
                                                               tint]
                                                              .Tvoid)))
                                                        (tfun
                                                          [(tptr tint),
                                                           (tptr tint),
                                                           tint,
                                                           (tptr tint),
                                                           (tptr (Tstruct dense.id.«_1024» noattr)),
                                                           tint,
                                                           tint,
                                                           tint,
                                                           tint,
                                                           tint,
                                                           tint]
                                                          .Tvoid))
                                                      [(.Etempvar dense.id.«lab» (tptr tint)),
                                                       (.Etempvar dense.id.«ptn» (tptr tint)),
                                                       (tv dense.id.«level»),
                                                       (.Evar dense.id.«nauty:orbits» (tptr tint)),
                                                       (.Evar dense.id.«nauty:stats»
                                                         (tptr (Tstruct dense.id.«_1024» noattr))),
                                                       (tv dense.id.«tv1»),
                                                       (tv dense.id.«index»),
                                                       (.Evar dense.id.«tcellsize» tint),
                                                       (.Evar dense.id.«numcells» tint),
                                                       (tv dense.id.«childcount»),
                                                       (.Evar dense.id.«nauty:n» tint)]))
                                                  .Sskip))
                                              (sk
                                                (.Sreturn
                                                  (some
                                                    (.Ebinop .Osub (tv dense.id.«level») (ci 1 tint) tint))))))))))))))))))))))))))

kernel_rfl body_eq : dense.body.«nauty:firstpathnode0» = body

end NautyVerified.Proofs.Search.Firstpathnode

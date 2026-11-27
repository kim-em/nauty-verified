import NautyVerified.Proofs.Refine.Syntax

/-!
# `othernode0`, factored

The Clight of nauty.c's `othernode0`, cut by `scripts/factor_clight.py` with
`scripts/factor/othernode.py`; `body_eq` pins it to `dense.body.«nauty:othernode0»`.
-/

namespace NautyVerified.Proofs.Search.Othernode

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

abbrev kill : statement :=
  (.Sifthenelse
    (.Etempvar (idOf 708) (Tint .I32 .Signed vattr))
    (sk (.Sreturn (some (.Eunop .Oneg (ci 12 tint) tint))))
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
            (sk
              (.Sifthenelse
                (.Ebinop .Olt (tv dense.id.«level») (.Evar dense.id.«nauty:invarsuclevel» tint) tint)
                (sk (.Sassign (.Evar dense.id.«nauty:invarsuclevel» tint) (tv dense.id.«level»)))
                .Sskip)))
          .Sskip)))
    .Sskip)

abbrev codeFirst : statement :=
  (.Sifthenelse
    (.Ebinop .Oeq
      (.Evar dense.id.«nauty:eqlev_first» tint)
      (.Ebinop .Osub (tv dense.id.«level») (ci 1 tint) tint)
      tint)
    (sk
      (.Sset
        (idOf 709)
        (.Ecast
          (.Ebinop .Oeq
            (.Etempvar dense.id.«code» tshort)
            (.Ederef
              (.Ebinop .Oadd
                (.Evar dense.id.«nauty:firstcode» (tptr tshort))
                (tv dense.id.«level»)
                (tptr tshort))
              tshort)
            tint)
          tbool)))
    (.Sset (idOf 709) (ci 0 tint)))

abbrev codeCanon : statement :=
  (.Sifthenelse
    (.Evar dense.id.«nauty:getcanon» tint)
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Oeq
            (.Evar dense.id.«nauty:eqlev_canon» tint)
            (.Ebinop .Osub (tv dense.id.«level») (ci 1 tint) tint)
            tint)
          (sk
            (.Sifthenelse
              (.Ebinop .Olt
                (.Etempvar dense.id.«code» tshort)
                (.Ederef
                  (.Ebinop .Oadd
                    (.Evar dense.id.«nauty:canoncode» (tptr tshort))
                    (tv dense.id.«level»)
                    (tptr tshort))
                  tshort)
                tint)
              (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (.Eunop .Oneg (ci 1 tint) tint)))
              (sk
                (.Sifthenelse
                  (.Ebinop .Ogt
                    (.Etempvar dense.id.«code» tshort)
                    (.Ederef
                      (.Ebinop .Oadd
                        (.Evar dense.id.«nauty:canoncode» (tptr tshort))
                        (tv dense.id.«level»)
                        (tptr tshort))
                      tshort)
                    tint)
                  (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 1 tint)))
                  (.Ssequence
                    (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint)))
                    (sk (.Sassign (.Evar dense.id.«nauty:eqlev_canon» tint) (tv dense.id.«level»))))))))
          .Sskip))
      (sk
        (.Sifthenelse
          (.Ebinop .Ogt (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint) tint)
          (sk
            (.Sassign
              (.Ederef
                (.Ebinop .Oadd
                  (.Evar dense.id.«nauty:canoncode» (tptr tshort))
                  (tv dense.id.«level»)
                  (tptr tshort))
                tshort)
              (.Etempvar dense.id.«code» tshort)))
          .Sskip)))
    .Sskip)

abbrev target : statement :=
  (.Sifthenelse
    (.Ebinop .Olt (.Evar dense.id.«numcells» tint) (.Evar dense.id.«nauty:n» tint) tint)
    (sk
      (.Sifthenelse
        (.Ebinop .Oeq (.Evar dense.id.«nauty:eqlev_first» tint) (tv dense.id.«level») tint)
        (sk (.Sset (idOf 711) (.Ecast (ci 1 tint) tbool)))
        (sk
          (.Sifthenelse
            (.Evar dense.id.«nauty:getcanon» tint)
            (.Ssequence
              (.Ssequence
                (sk
                  (.Sset
                    (idOf 711)
                    (.Ecast
                      (.Ebinop .Oge (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint) tint)
                      tbool)))
                (.Sset (idOf 711) (.Ecast (tv (idOf 711)) tbool)))
              (.Sset (idOf 711) (.Ecast (tv (idOf 711)) tbool)))
            (.Ssequence
              (sk (.Sset (idOf 711) (.Ecast (ci 0 tint) tbool)))
              (.Sset (idOf 711) (.Ecast (tv (idOf 711)) tbool)))))))
    (.Sset (idOf 711) (ci 0 tint)))

abbrev prune0 : statement :=
  (.Sifthenelse
    (.Evar dense.id.«nauty:needshortprune» tint)
    (.Ssequence
      (sk (.Sassign (.Evar dense.id.«nauty:needshortprune» tint) (ci 0 tint)))
      (sk
        (.Scall none
          (.Evar dense.id.«shortprune» (tfun [(tptr tulong), (tptr tulong), tint] .Tvoid))
          [(.Etempvar dense.id.«tcell» (tptr tulong)),
           (.Ebinop .Osub
             (.Evar dense.id.«nauty:fmptr» (tptr tulong))
             (.Evar dense.id.«nauty:m» tint)
             (tptr tulong)),
           (.Evar dense.id.«nauty:m» tint)])))
    .Sskip)

abbrev cheap : statement :=
  (.Sifthenelse
    (.Eunop .Onotbool (tv (idOf 713)) tint)
    (sk
      (.Sassign
        (.Evar dense.id.«nauty:noncheaplevel» tint)
        (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint)))
    .Sskip)

abbrev childLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Oge (tv dense.id.«tv») (ci 0 tint) tint) .Sskip .Sbreak))
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
                  (.Ssequence
                    (sk
                      (.Sifthenelse
                        (.Ebinop .Oeq (tv dense.id.«tv») (tv dense.id.«tv1») tint)
                        (.Ssequence
                          (sk
                            (.Scall none
                              (.Evar dense.id.«longprune»
                                (tfun
                                  [(tptr tulong), (tptr tulong), (tptr tulong), (tptr tulong), tint]
                                  .Tvoid))
                              [(.Etempvar dense.id.«tcell» (tptr tulong)),
                               (.Evar dense.id.«nauty:fixedpts» (tptr tulong)),
                               (.Evar dense.id.«nauty:workspace» (tptr tulong)),
                               (.Evar dense.id.«nauty:fmptr» (tptr tulong)),
                               (.Evar dense.id.«nauty:m» tint)]))
                          (sk
                            (.Sifthenelse
                              (.Evar dense.id.«nauty:doschreier» tint)
                              (sk
                                (.Scall none
                                  (.Evar dense.id.«pruneset»
                                    (tfun
                                      [(tptr tulong),
                                       (tptr (Tstruct dense.id.«schreierlevel» noattr)),
                                       (tptr (tptr (Tstruct dense.id.«permnodestruct» noattr))),
                                       (tptr tulong),
                                       tint,
                                       tint]
                                      .Tvoid))
                                  [(.Evar dense.id.«nauty:fixedpts» (tptr tulong)),
                                   (.Evar dense.id.«nauty:gp» (tptr (Tstruct dense.id.«schreierlevel» noattr))),
                                   (.Eaddrof
                                     (.Evar dense.id.«nauty:gens»
                                       (tptr (Tstruct dense.id.«permnodestruct» noattr)))
                                     (tptr (tptr (Tstruct dense.id.«permnodestruct» noattr)))),
                                   (.Etempvar dense.id.«tcell» (tptr tulong)),
                                   (.Evar dense.id.«nauty:m» tint),
                                   (.Evar dense.id.«nauty:n» tint)]))
                              .Sskip)))
                        .Sskip))
                    (sk
                      (.Scall none
                        (.Evar dense.id.«nauty:recover» (tfun [(tptr tint), tint] .Tvoid))
                        [(.Etempvar dense.id.«ptn» (tptr tint)), (tv dense.id.«level»)]))))))))))
    (.Ssequence
      (sk
        (.Scall
          (some (idOf 716))
          (.Evar dense.id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
          [(.Etempvar dense.id.«tcell» (tptr tulong)), (.Evar dense.id.«nauty:m» tint), (tv dense.id.«tv»)]))
      (.Sset dense.id.«tv» (tv (idOf 716)))))

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
            (.Ssequence
              (sk
                (.Sbuiltin
                  (some (idOf 708))
                  (.EF_vload .Mint32)
                  [(tptr (Tint .I32 .Signed vattr))]
                  [(.Eaddrof
                     (.Evar dense.id.«nauty_kill_request» (Tint .I32 .Signed vattr))
                     (tptr (Tint .I32 .Signed vattr)))]))
              kill)
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
                  (sk (.Sset dense.id.«code» (.Ecast (.Ecast (.Evar dense.id.«refcode» tint) tshort) tshort)))
                  (.Ssequence
                    (sk invstat)
                    (.Ssequence
                      (.Ssequence
                        (sk codeFirst)
                        (.Sifthenelse
                          (tv (idOf 709))
                          (sk (.Sassign (.Evar dense.id.«nauty:eqlev_first» tint) (tv dense.id.«level»)))
                          .Sskip))
                      (.Ssequence
                        (sk codeCanon)
                        (.Ssequence
                          (sk (.Sassign (.Evar dense.id.«tc» tint) (.Eunop .Oneg (ci 1 tint) tint)))
                          (.Ssequence
                            (.Ssequence
                              (sk target)
                              (.Sifthenelse
                                (tv (idOf 711))
                                (.Ssequence
                                  (.Ssequence
                                    (sk
                                      (.Sifthenelse
                                        (.Eunop .Onotbool (.Evar dense.id.«nauty:getcanon» tint) tint)
                                        (.Sset (idOf 710) (ci 1 tint))
                                        (sk
                                          (.Sset
                                            (idOf 710)
                                            (.Ecast
                                              (.Ebinop .Olt
                                                (.Evar dense.id.«nauty:comp_canon» tint)
                                                (ci 0 tint)
                                                tint)
                                              tbool)))))
                                    (.Sifthenelse
                                      (tv (idOf 710))
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
                                                     [(tptr tulong),
                                                      (tptr tint),
                                                      (tptr tint),
                                                      tint,
                                                      tint,
                                                      tint,
                                                      tint,
                                                      tint,
                                                      tint]
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
                                             (.Ederef
                                               (.Ebinop .Oadd
                                                 (.Evar dense.id.«nauty:firsttc» (tptr tint))
                                                 (tv dense.id.«level»)
                                                 (tptr tint))
                                               tint),
                                             (.Efield
                                               (.Evar dense.id.«nauty:dispatch»
                                                 (Tstruct dense.id.«_1027» noattr))
                                               dense.id.«targetcell»
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
                                                   tint))),
                                             (.Evar dense.id.«nauty:m» tint),
                                             (.Evar dense.id.«nauty:n» tint)]))
                                        (sk
                                          (.Sifthenelse
                                            (.Ebinop .One
                                              (.Evar dense.id.«tc» tint)
                                              (.Ederef
                                                (.Ebinop .Oadd
                                                  (.Evar dense.id.«nauty:firsttc» (tptr tint))
                                                  (tv dense.id.«level»)
                                                  (tptr tint))
                                                tint)
                                              tint)
                                            (sk
                                              (.Sassign
                                                (.Evar dense.id.«nauty:eqlev_first» tint)
                                                (.Ebinop .Osub (tv dense.id.«level») (ci 1 tint) tint)))
                                            .Sskip)))
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
                                                   [(tptr tulong),
                                                    (tptr tint),
                                                    (tptr tint),
                                                    tint,
                                                    tint,
                                                    tint,
                                                    tint,
                                                    tint,
                                                    tint]
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
                                                 [(tptr tulong),
                                                  (tptr tint),
                                                  (tptr tint),
                                                  tint,
                                                  tint,
                                                  tint,
                                                  tint,
                                                  tint,
                                                  tint]
                                                 tint))),
                                           (.Evar dense.id.«nauty:m» tint),
                                           (.Evar dense.id.«nauty:n» tint)]))))
                                  (sk
                                    (.Sassign
                                      (.Efield
                                        (.Ederef
                                          (.Evar dense.id.«nauty:stats»
                                            (tptr (Tstruct dense.id.«_1024» noattr)))
                                          (Tstruct dense.id.«_1024» noattr))
                                        dense.id.«tctotal»
                                        tulong)
                                      (.Ebinop .Oadd
                                        (.Efield
                                          (.Ederef
                                            (.Evar dense.id.«nauty:stats»
                                              (tptr (Tstruct dense.id.«_1024» noattr)))
                                            (Tstruct dense.id.«_1024» noattr))
                                          dense.id.«tctotal»
                                          tulong)
                                        (.Evar dense.id.«tcellsize» tint)
                                        tulong))))
                                .Sskip))
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
                                       (.Ecast (.Etempvar dense.id.«code» tshort) tint),
                                       (.Evar dense.id.«nauty:m» tint),
                                       (.Evar dense.id.«nauty:n» tint)]))
                                  .Sskip))
                              (.Ssequence
                                (.Ssequence
                                  (sk
                                    (.Scall
                                      (some (idOf 712))
                                      (.Evar dense.id.«nauty:processnode»
                                        (tfun [(tptr tint), (tptr tint), tint, tint] tint))
                                      [(.Etempvar dense.id.«lab» (tptr tint)),
                                       (.Etempvar dense.id.«ptn» (tptr tint)),
                                       (tv dense.id.«level»),
                                       (.Evar dense.id.«numcells» tint)]))
                                  (.Sset dense.id.«rtnlevel» (tv (idOf 712))))
                                (.Ssequence
                                  (sk
                                    (.Sifthenelse
                                      (.Ebinop .Olt (tv dense.id.«rtnlevel») (tv dense.id.«level») tint)
                                      (sk (.Sreturn (some (tv dense.id.«rtnlevel»))))
                                      .Sskip))
                                  (.Ssequence
                                    (sk prune0)
                                    (.Ssequence
                                      (.Ssequence
                                        (sk
                                          (.Scall
                                            (some (idOf 713))
                                            (.Ederef
                                              (.Efield
                                                (.Evar dense.id.«nauty:dispatch»
                                                  (Tstruct dense.id.«_1027» noattr))
                                                dense.id.«cheapautom»
                                                (tptr (tfun [(tptr tint), tint, tint, tint] tint)))
                                              (tfun [(tptr tint), tint, tint, tint] tint))
                                            [(.Etempvar dense.id.«ptn» (tptr tint)),
                                             (tv dense.id.«level»),
                                             (.Evar dense.id.«nauty:digraph» tint),
                                             (.Evar dense.id.«nauty:n» tint)]))
                                        cheap)
                                      (.Ssequence
                                        (.Ssequence
                                          (.Ssequence
                                            (.Ssequence
                                              (.Ssequence
                                                (sk
                                                  (.Scall
                                                    (some (idOf 714))
                                                    (.Evar dense.id.«nextelement»
                                                      (tfun [(tptr tulong), tint, tint] tint))
                                                    [(.Etempvar dense.id.«tcell» (tptr tulong)),
                                                     (.Evar dense.id.«nauty:m» tint),
                                                     (.Eunop .Oneg (ci 1 tint) tint)]))
                                                (.Sset (idOf 715) (.Ecast (tv (idOf 714)) tint)))
                                              (.Sset dense.id.«tv» (tv (idOf 715))))
                                            (.Sset dense.id.«tv1» (tv (idOf 715))))
                                          childLoop)
                                        (sk
                                          (.Sreturn
                                            (some (.Ebinop .Osub (tv dense.id.«level») (ci 1 tint) tint)))))))))))))))))))))))

kernel_rfl body_eq : dense.body.«nauty:othernode0» = body

end NautyVerified.Proofs.Search.Othernode

import NautyVerified.Proofs.Search.Ops

/-!
# `processnode`, factored

The Clight of nauty.c's `processnode`, cut by `scripts/factor_clight.py` with
`scripts/factor/processnode.py`; `body_eq` pins it. `classifyC` computes the
code (0 to 4) that `caseN` acts on, through the `switch`.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source NautyVerified.Logic
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv ix)
open NautyVerified.Proofs.Alloc (gat)
open NautyVerified.Proofs.Search (gats statsF)

abbrev classifyC : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .One (.Evar dense.id.«nauty:eqlev_first» tint) (tv dense.id.«level») tint)
        (sk
          (.Sifthenelse
            (.Eunop .Onotbool (.Evar dense.id.«nauty:getcanon» tint) tint)
            (sk (.Sset (idOf 706) (.Ecast (ci 1 tint) tbool)))
            (.Ssequence
              (sk
                (.Sset
                  (idOf 706)
                  (.Ecast (.Ebinop .Olt (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint) tint) tbool)))
              (.Sset (idOf 706) (.Ecast (tv (idOf 706)) tbool)))))
        (.Sset (idOf 706) (ci 0 tint))))
    (.Sifthenelse
      (tv (idOf 706))
      (sk (.Sset dense.id.«code» (ci 4 tint)))
      (sk
        (.Sifthenelse
          (.Ebinop .Oeq (tv dense.id.«numcells») (.Evar dense.id.«nauty:n» tint) tint)
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .Oeq (.Evar dense.id.«nauty:eqlev_first» tint) (tv dense.id.«level») tint)
                (.Ssequence
                  (forLoopC dense.id.«i»
                    (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
                    (sk
                      (.Sassign
                        (gat dense.id.«nauty:workperm» (gat dense.id.«nauty:firstlab» (tv dense.id.«i»)))
                        (ix dense.id.«lab» (tv dense.id.«i»)))))
                  (.Ssequence
                    (sk
                      (.Sifthenelse
                        (.Ebinop .Oge
                          (.Evar dense.id.«nauty:gca_first» tint)
                          (.Evar dense.id.«nauty:noncheaplevel» tint)
                          tint)
                        (.Sset (idOf 703) (ci 1 tint))
                        (.Ssequence
                          (sk
                            (.Scall
                              (some (idOf 704))
                              (.Ederef
                                (.Efield
                                  (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr))
                                  dense.id.«isautom»
                                  (tptr (tfun [(tptr tulong), (tptr tint), tint, tint, tint] tint)))
                                (tfun [(tptr tulong), (tptr tint), tint, tint, tint] tint))
                              [(.Evar dense.id.«nauty:g» (tptr tulong)),
                               (.Evar dense.id.«nauty:workperm» (tptr tint)),
                               (.Evar dense.id.«nauty:digraph» tint),
                               (.Evar dense.id.«nauty:m» tint),
                               (.Evar dense.id.«nauty:n» tint)]))
                          (.Sset (idOf 703) (.Ecast (tv (idOf 704)) tbool)))))
                    (.Sifthenelse (tv (idOf 703)) (sk (.Sset dense.id.«code» (ci 1 tint))) .Sskip)))
                .Sskip))
            (sk
              (.Sifthenelse
                (.Ebinop .Oeq (tv dense.id.«code») (ci 0 tint) tint)
                (sk
                  (.Sifthenelse
                    (.Evar dense.id.«nauty:getcanon» tint)
                    (.Ssequence
                      (sk (.Sassign (.Evar dense.id.«sr» tint) (ci 0 tint)))
                      (.Ssequence
                        (sk
                          (.Sifthenelse
                            (.Ebinop .Oeq (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint) tint)
                            (sk
                              (.Sifthenelse
                                (.Ebinop .Olt
                                  (tv dense.id.«level»)
                                  (.Evar dense.id.«nauty:canonlevel» tint)
                                  tint)
                                (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 1 tint)))
                                (.Ssequence
                                  (sk
                                    (.Scall none
                                      (.Ederef
                                        (.Efield
                                          (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr))
                                          dense.id.«updatecan»
                                          (tptr
                                            (tfun
                                              [(tptr tulong),
                                               (tptr tulong),
                                               (tptr tint),
                                               tint,
                                               tint,
                                               tint]
                                              .Tvoid)))
                                        (tfun
                                          [(tptr tulong),
                                           (tptr tulong),
                                           (tptr tint),
                                           tint,
                                           tint,
                                           tint]
                                          .Tvoid))
                                      [(.Evar dense.id.«nauty:g» (tptr tulong)),
                                       (.Evar dense.id.«nauty:canong» (tptr tulong)),
                                       (.Evar dense.id.«nauty:canonlab» (tptr tint)),
                                       (.Evar dense.id.«nauty:samerows» tint),
                                       (.Evar dense.id.«nauty:m» tint),
                                       (.Evar dense.id.«nauty:n» tint)]))
                                  (.Ssequence
                                    (sk
                                      (.Sassign
                                        (.Evar dense.id.«nauty:samerows» tint)
                                        (.Evar dense.id.«nauty:n» tint)))
                                    (.Ssequence
                                      (sk
                                        (.Scall
                                          (some (idOf 705))
                                          (.Ederef
                                            (.Efield
                                              (.Evar dense.id.«nauty:dispatch»
                                                (Tstruct dense.id.«_1027» noattr))
                                              dense.id.«testcanlab»
                                              (tptr
                                                (tfun
                                                  [(tptr tulong),
                                                   (tptr tulong),
                                                   (tptr tint),
                                                   (tptr tint),
                                                   tint,
                                                   tint]
                                                  tint)))
                                            (tfun
                                              [(tptr tulong),
                                               (tptr tulong),
                                               (tptr tint),
                                               (tptr tint),
                                               tint,
                                               tint]
                                              tint))
                                          [(.Evar dense.id.«nauty:g» (tptr tulong)),
                                           (.Evar dense.id.«nauty:canong» (tptr tulong)),
                                           (.Etempvar dense.id.«lab» (tptr tint)),
                                           (.Eaddrof (.Evar dense.id.«sr» tint) (tptr tint)),
                                           (.Evar dense.id.«nauty:m» tint),
                                           (.Evar dense.id.«nauty:n» tint)]))
                                      (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (tv (idOf 705))))))))
                            .Sskip))
                        (sk
                          (.Sifthenelse
                            (.Ebinop .Oeq (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint) tint)
                            (.Ssequence
                              (forLoopC dense.id.«i»
                                (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
                                (sk
                                  (.Sassign
                                    (gat dense.id.«nauty:workperm» (gat dense.id.«nauty:canonlab» (tv dense.id.«i»)))
                                    (ix dense.id.«lab» (tv dense.id.«i»)))))
                              (sk (.Sset dense.id.«code» (ci 2 tint))))
                            (sk
                              (.Sifthenelse
                                (.Ebinop .Ogt (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint) tint)
                                (sk (.Sset dense.id.«code» (ci 3 tint)))
                                (sk (.Sset dense.id.«code» (ci 4 tint)))))))))
                    (sk (.Sset dense.id.«code» (ci 4 tint)))))
                .Sskip)))
          .Sskip))))

abbrev case0 : statement :=
  (sk (.Sreturn (some (tv dense.id.«level»))))

abbrev case1 : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Oeq
          (.Evar dense.id.«nauty:fmptr» (tptr tulong))
          (.Evar dense.id.«nauty:worktop» (tptr tulong))
          tint)
        (sk
          (.Sassign
            (.Evar dense.id.«nauty:fmptr» (tptr tulong))
            (.Ebinop .Osub
              (.Evar dense.id.«nauty:fmptr» (tptr tulong))
              (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint)
              (tptr tulong))))
        .Sskip))
    (.Ssequence
      (sk
        (.Scall none
          (.Evar dense.id.«fmperm» (tfun [(tptr tint), (tptr tulong), (tptr tulong), tint, tint] .Tvoid))
          [(.Evar dense.id.«nauty:workperm» (tptr tint)),
           (.Evar dense.id.«nauty:fmptr» (tptr tulong)),
           (.Ebinop .Oadd
             (.Evar dense.id.«nauty:fmptr» (tptr tulong))
             (.Evar dense.id.«nauty:m» tint)
             (tptr tulong)),
           (.Evar dense.id.«nauty:m» tint),
           (.Evar dense.id.«nauty:n» tint)]))
      (.Ssequence
        (sk
          (.Sassign
            (.Evar dense.id.«nauty:fmptr» (tptr tulong))
            (.Ebinop .Oadd
              (.Evar dense.id.«nauty:fmptr» (tptr tulong))
              (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint)
              (tptr tulong))))
        (.Ssequence
          (sk
            (.Sifthenelse
              (.Evar dense.id.«nauty:writeautoms» tint)
              (sk
                (.Scall none
                  (.Evar dense.id.«writeperm»
                    (tfun
                      [(tptr (Tstruct dense.id.«_IO_FILE» noattr)), (tptr tint), tint, tint, tint]
                      .Tvoid))
                  [(.Evar dense.id.«nauty:outfile» (tptr (Tstruct dense.id.«_IO_FILE» noattr))),
                   (.Evar dense.id.«nauty:workperm» (tptr tint)),
                   (.Evar dense.id.«nauty:cartesian» tint),
                   (.Evar dense.id.«nauty:linelength» tint),
                   (.Evar dense.id.«nauty:n» tint)]))
              .Sskip))
          (.Ssequence
            (.Ssequence
              (sk
                (.Scall
                  (some (idOf 708))
                  (.Evar dense.id.«orbjoin» (tfun [(tptr tint), (tptr tint), tint] tint))
                  [(.Evar dense.id.«nauty:orbits» (tptr tint)),
                   (.Evar dense.id.«nauty:workperm» (tptr tint)),
                   (.Evar dense.id.«nauty:n» tint)]))
              (.Sassign (statsF dense.id.«numorbits» tint) (tv (idOf 708))))
            (.Ssequence
              (sk
                (.Sassign
                  (statsF dense.id.«numgenerators» tint)
                  (.Ebinop .Oadd (statsF dense.id.«numgenerators» tint) (ci 1 tint) tint)))
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Ebinop .One
                      (.Evar dense.id.«nauty:userautomproc»
                        (tptr (tfun [tint, (tptr tint), (tptr tint), tint, tint, tint] .Tvoid)))
                      (.Ecast (ci 0 tint) (tptr .Tvoid))
                      tint)
                    (sk
                      (.Scall none
                        (.Ederef
                          (.Evar dense.id.«nauty:userautomproc»
                            (tptr (tfun [tint, (tptr tint), (tptr tint), tint, tint, tint] .Tvoid)))
                          (tfun [tint, (tptr tint), (tptr tint), tint, tint, tint] .Tvoid))
                        [(statsF dense.id.«numgenerators» tint),
                         (.Evar dense.id.«nauty:workperm» (tptr tint)),
                         (.Evar dense.id.«nauty:orbits» (tptr tint)),
                         (statsF dense.id.«numorbits» tint),
                         (.Evar dense.id.«nauty:stabvertex» tint),
                         (.Evar dense.id.«nauty:n» tint)]))
                    .Sskip))
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Evar dense.id.«nauty:doschreier» tint)
                      (sk
                        (.Scall none
                          (.Evar dense.id.«addgenerator»
                            (tfun
                              [(tptr (tptr (Tstruct dense.id.«schreierlevel» noattr))),
                               (tptr (tptr (Tstruct dense.id.«permnodestruct» noattr))),
                               (tptr tint),
                               tint]
                              tint))
                          [(.Eaddrof
                             (.Evar dense.id.«nauty:gp» (tptr (Tstruct dense.id.«schreierlevel» noattr)))
                             (tptr (tptr (Tstruct dense.id.«schreierlevel» noattr)))),
                           (.Eaddrof
                             (.Evar dense.id.«nauty:gens» (tptr (Tstruct dense.id.«permnodestruct» noattr)))
                             (tptr (tptr (Tstruct dense.id.«permnodestruct» noattr)))),
                           (.Evar dense.id.«nauty:workperm» (tptr tint)),
                           (.Evar dense.id.«nauty:n» tint)]))
                      .Sskip))
                  (sk (.Sreturn (some (.Evar dense.id.«nauty:gca_first» tint))))))))))))

abbrev case2 : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Oeq
          (.Evar dense.id.«nauty:fmptr» (tptr tulong))
          (.Evar dense.id.«nauty:worktop» (tptr tulong))
          tint)
        (sk
          (.Sassign
            (.Evar dense.id.«nauty:fmptr» (tptr tulong))
            (.Ebinop .Osub
              (.Evar dense.id.«nauty:fmptr» (tptr tulong))
              (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint)
              (tptr tulong))))
        .Sskip))
    (.Ssequence
      (sk
        (.Scall none
          (.Evar dense.id.«fmperm» (tfun [(tptr tint), (tptr tulong), (tptr tulong), tint, tint] .Tvoid))
          [(.Evar dense.id.«nauty:workperm» (tptr tint)),
           (.Evar dense.id.«nauty:fmptr» (tptr tulong)),
           (.Ebinop .Oadd
             (.Evar dense.id.«nauty:fmptr» (tptr tulong))
             (.Evar dense.id.«nauty:m» tint)
             (tptr tulong)),
           (.Evar dense.id.«nauty:m» tint),
           (.Evar dense.id.«nauty:n» tint)]))
      (.Ssequence
        (sk
          (.Sassign
            (.Evar dense.id.«nauty:fmptr» (tptr tulong))
            (.Ebinop .Oadd
              (.Evar dense.id.«nauty:fmptr» (tptr tulong))
              (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint)
              (tptr tulong))))
        (.Ssequence
          (sk (.Sset dense.id.«save» (statsF dense.id.«numorbits» tint)))
          (.Ssequence
            (.Ssequence
              (sk
                (.Scall
                  (some (idOf 709))
                  (.Evar dense.id.«orbjoin» (tfun [(tptr tint), (tptr tint), tint] tint))
                  [(.Evar dense.id.«nauty:orbits» (tptr tint)),
                   (.Evar dense.id.«nauty:workperm» (tptr tint)),
                   (.Evar dense.id.«nauty:n» tint)]))
              (.Sassign (statsF dense.id.«numorbits» tint) (tv (idOf 709))))
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .Oeq (statsF dense.id.«numorbits» tint) (tv dense.id.«save») tint)
                  (.Ssequence
                    (sk
                      (.Sifthenelse
                        (.Ebinop .One
                          (.Evar dense.id.«nauty:gca_canon» tint)
                          (.Evar dense.id.«nauty:gca_first» tint)
                          tint)
                        (sk (.Sassign (.Evar dense.id.«nauty:needshortprune» tint) (ci 1 tint)))
                        .Sskip))
                    (sk (.Sreturn (some (.Evar dense.id.«nauty:gca_canon» tint)))))
                  .Sskip))
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Evar dense.id.«nauty:writeautoms» tint)
                    (sk
                      (.Scall none
                        (.Evar dense.id.«writeperm»
                          (tfun
                            [(tptr (Tstruct dense.id.«_IO_FILE» noattr)), (tptr tint), tint, tint, tint]
                            .Tvoid))
                        [(.Evar dense.id.«nauty:outfile» (tptr (Tstruct dense.id.«_IO_FILE» noattr))),
                         (.Evar dense.id.«nauty:workperm» (tptr tint)),
                         (.Evar dense.id.«nauty:cartesian» tint),
                         (.Evar dense.id.«nauty:linelength» tint),
                         (.Evar dense.id.«nauty:n» tint)]))
                    .Sskip))
                (.Ssequence
                  (sk
                    (.Sassign
                      (statsF dense.id.«numgenerators» tint)
                      (.Ebinop .Oadd (statsF dense.id.«numgenerators» tint) (ci 1 tint) tint)))
                  (.Ssequence
                    (sk
                      (.Sifthenelse
                        (.Ebinop .One
                          (.Evar dense.id.«nauty:userautomproc»
                            (tptr (tfun [tint, (tptr tint), (tptr tint), tint, tint, tint] .Tvoid)))
                          (.Ecast (ci 0 tint) (tptr .Tvoid))
                          tint)
                        (sk
                          (.Scall none
                            (.Ederef
                              (.Evar dense.id.«nauty:userautomproc»
                                (tptr
                                  (tfun [tint, (tptr tint), (tptr tint), tint, tint, tint] .Tvoid)))
                              (tfun [tint, (tptr tint), (tptr tint), tint, tint, tint] .Tvoid))
                            [(statsF dense.id.«numgenerators» tint),
                             (.Evar dense.id.«nauty:workperm» (tptr tint)),
                             (.Evar dense.id.«nauty:orbits» (tptr tint)),
                             (statsF dense.id.«numorbits» tint),
                             (.Evar dense.id.«nauty:stabvertex» tint),
                             (.Evar dense.id.«nauty:n» tint)]))
                        .Sskip))
                    (.Ssequence
                      (sk
                        (.Sifthenelse
                          (.Evar dense.id.«nauty:doschreier» tint)
                          (sk
                            (.Scall none
                              (.Evar dense.id.«addgenerator»
                                (tfun
                                  [(tptr (tptr (Tstruct dense.id.«schreierlevel» noattr))),
                                   (tptr (tptr (Tstruct dense.id.«permnodestruct» noattr))),
                                   (tptr tint),
                                   tint]
                                  tint))
                              [(.Eaddrof
                                 (.Evar dense.id.«nauty:gp» (tptr (Tstruct dense.id.«schreierlevel» noattr)))
                                 (tptr (tptr (Tstruct dense.id.«schreierlevel» noattr)))),
                               (.Eaddrof
                                 (.Evar dense.id.«nauty:gens» (tptr (Tstruct dense.id.«permnodestruct» noattr)))
                                 (tptr (tptr (Tstruct dense.id.«permnodestruct» noattr)))),
                               (.Evar dense.id.«nauty:workperm» (tptr tint)),
                               (.Evar dense.id.«nauty:n» tint)]))
                          .Sskip))
                      (.Ssequence
                        (sk
                          (.Sifthenelse
                            (.Ebinop .Olt
                              (gat dense.id.«nauty:orbits» (.Evar dense.id.«nauty:cosetindex» tint))
                              (.Evar dense.id.«nauty:cosetindex» tint)
                              tint)
                            (sk (.Sreturn (some (.Evar dense.id.«nauty:gca_first» tint))))
                            .Sskip))
                        (.Ssequence
                          (sk
                            (.Sifthenelse
                              (.Ebinop .One
                                (.Evar dense.id.«nauty:gca_canon» tint)
                                (.Evar dense.id.«nauty:gca_first» tint)
                                tint)
                              (sk (.Sassign (.Evar dense.id.«nauty:needshortprune» tint) (ci 1 tint)))
                              .Sskip))
                          (sk (.Sreturn (some (.Evar dense.id.«nauty:gca_canon» tint))))))))))))))))

abbrev case3 : statement :=
  (.Ssequence
    (sk
      (.Sassign
        (statsF dense.id.«canupdates» tulong)
        (.Ebinop .Oadd (statsF dense.id.«canupdates» tulong) (ci 1 tint) tulong)))
    (.Ssequence
      (forLoopC dense.id.«i»
        (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
        (sk (.Sassign (gat dense.id.«nauty:canonlab» (tv dense.id.«i»)) (ix dense.id.«lab» (tv dense.id.«i»)))))
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (.Ssequence
                (sk (.Sset (idOf 710) (.Ecast (tv dense.id.«level») tint)))
                (.Sassign (.Evar dense.id.«nauty:gca_canon» tint) (tv (idOf 710))))
              (.Sset (idOf 711) (.Ecast (tv (idOf 710)) tint)))
            (.Sassign (.Evar dense.id.«nauty:eqlev_canon» tint) (tv (idOf 711))))
          (.Sassign (.Evar dense.id.«nauty:canonlevel» tint) (tv (idOf 711))))
        (.Ssequence
          (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint)))
          (.Ssequence
            (sk
              (.Sassign
                (gats dense.id.«nauty:canoncode» (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint))
                (ci 32767 tint)))
            (.Ssequence
              (sk (.Sassign (.Evar dense.id.«nauty:samerows» tint) (.Evar dense.id.«sr» tint)))
              (.Ssequence
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Evar dense.id.«nauty:getcanon» tint)
                      (sk
                        (.Sset
                          (idOf 713)
                          (.Ecast
                            (.Ebinop .One
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
                              (.Ecast (ci 0 tint) (tptr .Tvoid))
                              tint)
                            tbool)))
                      (.Sset (idOf 713) (ci 0 tint))))
                  (.Sifthenelse
                    (tv (idOf 713))
                    (.Ssequence
                      (sk
                        (.Scall none
                          (.Ederef
                            (.Efield
                              (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr))
                              dense.id.«updatecan»
                              (tptr
                                (tfun
                                  [(tptr tulong), (tptr tulong), (tptr tint), tint, tint, tint]
                                  .Tvoid)))
                            (tfun
                              [(tptr tulong), (tptr tulong), (tptr tint), tint, tint, tint]
                              .Tvoid))
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
                              (some (idOf 712))
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
                                  [(tptr tulong),
                                   (tptr tint),
                                   (tptr tulong),
                                   tulong,
                                   tint,
                                   tint,
                                   tint]
                                  tint))
                              [(.Evar dense.id.«nauty:g» (tptr tulong)),
                               (.Evar dense.id.«nauty:canonlab» (tptr tint)),
                               (.Evar dense.id.«nauty:canong» (tptr tulong)),
                               (statsF dense.id.«canupdates» tulong),
                               (.Ecast (gats dense.id.«nauty:canoncode» (tv dense.id.«level»)) tint),
                               (.Evar dense.id.«nauty:m» tint),
                               (.Evar dense.id.«nauty:n» tint)]))
                          (.Sifthenelse
                            (tv (idOf 712))
                            (sk (.Sreturn (some (.Eunop .Oneg (ci 11 tint) tint))))
                            .Sskip))))
                    .Sskip))
                .Sbreak)))))))

abbrev case4 : statement :=
  (.Ssequence
    (sk
      (.Sassign
        (statsF dense.id.«numbadleaves» tulong)
        (.Ebinop .Oadd (statsF dense.id.«numbadleaves» tulong) (ci 1 tint) tulong)))
    .Sbreak)

abbrev body : statement :=
  (.Ssequence
    (sk (.Sset dense.id.«code» (ci 0 tint)))
    (.Ssequence classifyC
      (.Ssequence
        (.Ssequence
          (sk
            (.Sifthenelse
              (.Ebinop .One (tv dense.id.«code») (ci 0 tint) tint)
              (sk
                (.Sset
                  (idOf 707)
                  (.Ecast (.Ebinop .Ogt (tv dense.id.«level») (statsF dense.id.«maxlevel» tint) tint) tbool)))
              (.Sset (idOf 707) (ci 0 tint))))
          (.Sifthenelse
            (tv (idOf 707))
            (sk (.Sassign (statsF dense.id.«maxlevel» tint) (tv dense.id.«level»)))
            .Sskip))
        (.Ssequence
          (sk
            (.Sswitch
              (tv dense.id.«code»)
              (.LScons
                (some (zOfInt 0))
                case0
                (.LScons
                  (some (zOfInt 1))
                  case1
                  (.LScons
                    (some (zOfInt 2))
                    case2
                    (.LScons (some (zOfInt 3)) case3 (.LScons (some (zOfInt 4)) case4 .LSnil)))))))
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .One (tv dense.id.«level») (.Evar dense.id.«nauty:noncheaplevel» tint) tint)
                (.Ssequence
                  (sk (.Sset dense.id.«ispruneok» (ci 1 tint)))
                  (.Ssequence
                    (sk
                      (.Sifthenelse
                        (.Ebinop .Oeq
                          (.Evar dense.id.«nauty:fmptr» (tptr tulong))
                          (.Evar dense.id.«nauty:worktop» (tptr tulong))
                          tint)
                        (sk
                          (.Sassign
                            (.Evar dense.id.«nauty:fmptr» (tptr tulong))
                            (.Ebinop .Osub
                              (.Evar dense.id.«nauty:fmptr» (tptr tulong))
                              (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint)
                              (tptr tulong))))
                        .Sskip))
                    (.Ssequence
                      (sk
                        (.Scall none
                          (.Evar dense.id.«fmptn»
                            (tfun
                              [(tptr tint),
                               (tptr tint),
                               tint,
                               (tptr tulong),
                               (tptr tulong),
                               tint,
                               tint]
                              .Tvoid))
                          [(.Etempvar dense.id.«lab» (tptr tint)),
                           (.Etempvar dense.id.«ptn» (tptr tint)),
                           (.Evar dense.id.«nauty:noncheaplevel» tint),
                           (.Evar dense.id.«nauty:fmptr» (tptr tulong)),
                           (.Ebinop .Oadd
                             (.Evar dense.id.«nauty:fmptr» (tptr tulong))
                             (.Evar dense.id.«nauty:m» tint)
                             (tptr tulong)),
                           (.Evar dense.id.«nauty:m» tint),
                           (.Evar dense.id.«nauty:n» tint)]))
                      (sk
                        (.Sassign
                          (.Evar dense.id.«nauty:fmptr» (tptr tulong))
                          (.Ebinop .Oadd
                            (.Evar dense.id.«nauty:fmptr» (tptr tulong))
                            (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint)
                            (tptr tulong)))))))
                (sk (.Sset dense.id.«ispruneok» (ci 0 tint)))))
            (.Ssequence
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Ebinop .Ogt
                      (.Evar dense.id.«nauty:allsamelevel» tint)
                      (.Evar dense.id.«nauty:eqlev_canon» tint)
                      tint)
                    (sk
                      (.Sset
                        (idOf 714)
                        (.Ecast
                          (.Ebinop .Osub (.Evar dense.id.«nauty:allsamelevel» tint) (ci 1 tint) tint)
                          tint)))
                    (sk (.Sset (idOf 714) (.Ecast (.Evar dense.id.«nauty:eqlev_canon» tint) tint)))))
                (.Sset dense.id.«save» (tv (idOf 714))))
              (.Ssequence
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Ebinop .Ole (.Evar dense.id.«nauty:noncheaplevel» tint) (tv dense.id.«save») tint)
                      (sk
                        (.Sset
                          (idOf 715)
                          (.Ecast
                            (.Ebinop .Osub (.Evar dense.id.«nauty:noncheaplevel» tint) (ci 1 tint) tint)
                            tint)))
                      (sk (.Sset (idOf 715) (.Ecast (tv dense.id.«save») tint)))))
                  (.Sset dense.id.«newlevel» (tv (idOf 715))))
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Sifthenelse
                        (tv dense.id.«ispruneok»)
                        (sk
                          (.Sset
                            (idOf 716)
                            (.Ecast
                              (.Ebinop .One
                                (tv dense.id.«newlevel»)
                                (.Evar dense.id.«nauty:gca_first» tint)
                                tint)
                              tbool)))
                        (.Sset (idOf 716) (ci 0 tint))))
                    (.Sifthenelse
                      (tv (idOf 716))
                      (sk (.Sassign (.Evar dense.id.«nauty:needshortprune» tint) (ci 1 tint)))
                      .Sskip))
                  (sk (.Sreturn (some (tv dense.id.«newlevel»))))))))))))


kernel_rfl body_eq : dense.body.«nauty:processnode» = body

end NautyVerified.Proofs.Search.Processnode

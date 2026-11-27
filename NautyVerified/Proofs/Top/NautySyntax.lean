import NautyVerified.Proofs.Refine.Syntax

/-!
# `nauty`, factored

The Clight of nauty.c's `nauty`, cut by `scripts/factor_clight.py` with
`scripts/factor/nauty.py`; `body_eq` pins it to `dense.body.nauty`. The body
is a chain of statements; its suffixes are named by stage:

- `tSizes`: the `m` and `n` size checks; `tZero`: the `n == 0` case
  (`zeroIf`); `tMain`: copies of `m` and `n`, `nautil_check` and
  `dispatch.check`; `tAlloc`: the nine `DYNALLOC1`s; `tTc`: the target-cell
  list reset when `m > alloc_m` (`tcIf`);
- `tOpts`: the option copies; `tPtn`: the partition and active set
  (`ptnIf`); `tInit`: `g`, `canong`, `dispatch.init`; `tOrbits`: the
  identity orbits; `tStats`: the statistics and `EMPTYSET(fixedpts)`;
  `tWork`: the workspace, `fmptr` and the remaining counters;
- `tRoot`: the call of `firstpathnode0`; `tPost`: `updatecan` and the copy of
  `canonlab` into `lab` (`postIf`); `tFree`: the `n >= 320` release
  (`freeIf`), `dispatch.cleanup` and the Schreier release.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open CompCert4Lean.Foundation.Numbers.Rocq.Coq (zOfInt)
open NautyVerified.Proofs.Set (sk pv)
open NautyVerified.Proofs.Refine (tv pi)
open NautyVerified.Proofs.Alloc (dynalloc1)

namespace Nauty

abbrev zeroIf : statement :=
  (.Sifthenelse
    (.Ebinop .Oeq (tv dense.id.«n_arg») (ci 0 tint) tint)
    (.Ssequence
      (sk
        (.Sassign
          (.Efield
            (.Ederef
              (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
              (.Tstruct dense.id.«_1024» noattr))
            dense.id.«grpsize1»
            tdouble)
          (.Econst_float
            (CompCert4Lean.Lib.Floats.Float.of_bits (NautyVerified.Word.lr 4607182418800017408))
            tdouble)))
      (.Ssequence
        (sk
          (.Sassign
            (.Efield
              (.Ederef
                (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                (.Tstruct dense.id.«_1024» noattr))
              dense.id.«grpsize2»
              tint)
            (ci 0 tint)))
        (.Ssequence
          (sk
            (.Sassign
              (.Efield
                (.Ederef
                  (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                  (.Tstruct dense.id.«_1024» noattr))
                dense.id.«numorbits»
                tint)
              (ci 0 tint)))
          (.Ssequence
            (sk
              (.Sassign
                (.Efield
                  (.Ederef
                    (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                    (.Tstruct dense.id.«_1024» noattr))
                  dense.id.«numgenerators»
                  tint)
                (ci 0 tint)))
            (.Ssequence
              (sk
                (.Sassign
                  (.Efield
                    (.Ederef
                      (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                      (.Tstruct dense.id.«_1024» noattr))
                    dense.id.«errstatus»
                    tint)
                  (ci 0 tint)))
              (.Ssequence
                (sk
                  (.Sassign
                    (.Efield
                      (.Ederef
                        (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                        (.Tstruct dense.id.«_1024» noattr))
                      dense.id.«numnodes»
                      tulong)
                    (ci 1 tint)))
                (.Ssequence
                  (sk
                    (.Sassign
                      (.Efield
                        (.Ederef
                          (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                          (.Tstruct dense.id.«_1024» noattr))
                        dense.id.«numbadleaves»
                        tulong)
                      (ci 0 tint)))
                  (.Ssequence
                    (sk
                      (.Sassign
                        (.Efield
                          (.Ederef
                            (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                            (.Tstruct dense.id.«_1024» noattr))
                          dense.id.«maxlevel»
                          tint)
                        (ci 1 tint)))
                    (.Ssequence
                      (sk
                        (.Sassign
                          (.Efield
                            (.Ederef
                              (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                              (.Tstruct dense.id.«_1024» noattr))
                            dense.id.«tctotal»
                            tulong)
                          (ci 0 tint)))
                      (.Ssequence
                        (sk
                          (.Sassign
                            (.Efield
                              (.Ederef
                                (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                                (.Tstruct dense.id.«_1024» noattr))
                              dense.id.«canupdates»
                              tulong)
                            (.Ebinop .One
                              (.Efield
                                (.Ederef
                                  (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                  (.Tstruct dense.id.«optionstruct» noattr))
                                dense.id.«getcanon»
                                tint)
                              (ci 0 tint)
                              tint)))
                        (.Ssequence
                          (sk
                            (.Sassign
                              (.Efield
                                (.Ederef
                                  (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                                  (.Tstruct dense.id.«_1024» noattr))
                                dense.id.«invapplics»
                                tulong)
                              (ci 0 tint)))
                          (.Ssequence
                            (sk
                              (.Sassign
                                (.Efield
                                  (.Ederef
                                    (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                                    (.Tstruct dense.id.«_1024» noattr))
                                  dense.id.«invsuccesses»
                                  tulong)
                                (ci 0 tint)))
                            (.Ssequence
                              (sk
                                (.Sassign
                                  (.Efield
                                    (.Ederef
                                      (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                                      (.Tstruct dense.id.«_1024» noattr))
                                    dense.id.«invarsuclevel»
                                    tint)
                                  (ci 0 tint)))
                              (.Ssequence
                                (.Ssequence
                                  (.Ssequence
                                    (sk
                                      (.Sset
                                        (idOf 708)
                                        (.Ecast (.Ecast (ci 0 tint) (tptr .Tvoid)) (tptr tulong))))
                                    (.Sassign
                                      (.Evar dense.id.«nauty:canong» (tptr tulong))
                                      (pv (idOf 708))))
                                  (.Sassign (.Evar dense.id.«nauty:g» (tptr tulong)) (pv (idOf 708))))
                                (.Ssequence
                                  (sk (.Sassign (.Evar dense.id.«initstatus» tint) (ci 0 tint)))
                                  (.Ssequence
                                    (sk
                                      (.Sifthenelse
                                        (.Ebinop .One
                                          (.Efield
                                            (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                                            dense.id.«init»
                                            (tptr
                                              (tfun
                                                [(tptr tulong),
                                                 (tptr (tptr tulong)),
                                                 (tptr tulong),
                                                 (tptr (tptr tulong)),
                                                 (tptr tint),
                                                 (tptr tint),
                                                 (tptr tulong),
                                                 (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                                                 (tptr tint),
                                                 tint,
                                                 tint]
                                                .Tvoid)))
                                          (.Ecast (ci 0 tint) (tptr .Tvoid))
                                          tint)
                                        (sk
                                          (.Scall none
                                            (.Ederef
                                              (.Efield
                                                (.Evar dense.id.«nauty:dispatch»
                                                  (.Tstruct dense.id.«_1027» noattr))
                                                dense.id.«init»
                                                (tptr
                                                  (tfun
                                                    [(tptr tulong),
                                                     (tptr (tptr tulong)),
                                                     (tptr tulong),
                                                     (tptr (tptr tulong)),
                                                     (tptr tint),
                                                     (tptr tint),
                                                     (tptr tulong),
                                                     (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                                                     (tptr tint),
                                                     tint,
                                                     tint]
                                                    .Tvoid)))
                                              (tfun
                                                [(tptr tulong),
                                                 (tptr (tptr tulong)),
                                                 (tptr tulong),
                                                 (tptr (tptr tulong)),
                                                 (tptr tint),
                                                 (tptr tint),
                                                 (tptr tulong),
                                                 (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                                                 (tptr tint),
                                                 tint,
                                                 tint]
                                                .Tvoid))
                                            [(pv dense.id.«g_arg»),
                                             (.Eaddrof
                                               (.Evar dense.id.«nauty:g» (tptr tulong))
                                               (tptr (tptr tulong))),
                                             (pv dense.id.«canong_arg»),
                                             (.Eaddrof
                                               (.Evar dense.id.«nauty:canong» (tptr tulong))
                                               (tptr (tptr tulong))),
                                             (pi dense.id.«lab»),
                                             (pi dense.id.«ptn»),
                                             (.Evar dense.id.«nauty:active» (tptr tulong)),
                                             (.Etempvar dense.id.«options»
                                               (tptr (.Tstruct dense.id.«optionstruct» noattr))),
                                             (.Eaddrof (.Evar dense.id.«initstatus» tint) (tptr tint)),
                                             (.Evar dense.id.«nauty:m» tint),
                                             (.Evar dense.id.«nauty:n» tint)]))
                                        .Sskip))
                                    (.Ssequence
                                      (sk
                                        (.Sifthenelse
                                          (.Evar dense.id.«initstatus» tint)
                                          (sk
                                            (.Sassign
                                              (.Efield
                                                (.Ederef
                                                  (.Evar dense.id.«nauty:stats»
                                                    (tptr (.Tstruct dense.id.«_1024» noattr)))
                                                  (.Tstruct dense.id.«_1024» noattr))
                                                dense.id.«errstatus»
                                                tint)
                                              (.Evar dense.id.«initstatus» tint)))
                                          .Sskip))
                                      (.Ssequence
                                        (sk
                                          (.Sifthenelse
                                            (.Ebinop .Oeq
                                              (.Evar dense.id.«nauty:g» (tptr tulong))
                                              (.Ecast (ci 0 tint) (tptr .Tvoid))
                                              tint)
                                            (sk
                                              (.Sassign
                                                (.Evar dense.id.«nauty:g» (tptr tulong))
                                                (pv dense.id.«g_arg»)))
                                            .Sskip))
                                        (.Ssequence
                                          (sk
                                            (.Sifthenelse
                                              (.Ebinop .Oeq
                                                (.Evar dense.id.«nauty:canong» (tptr tulong))
                                                (.Ecast (ci 0 tint) (tptr .Tvoid))
                                                tint)
                                              (sk
                                                (.Sassign
                                                  (.Evar dense.id.«nauty:canong» (tptr tulong))
                                                  (pv dense.id.«canong_arg»)))
                                              .Sskip))
                                          (.Ssequence
                                            (sk
                                              (.Sifthenelse
                                                (.Ebinop .One
                                                  (.Efield
                                                    (.Evar dense.id.«nauty:dispatch»
                                                      (.Tstruct dense.id.«_1027» noattr))
                                                    dense.id.«cleanup»
                                                    (tptr
                                                      (tfun
                                                        [(tptr tulong),
                                                         (tptr (tptr tulong)),
                                                         (tptr tulong),
                                                         (tptr (tptr tulong)),
                                                         (tptr tint),
                                                         (tptr tint),
                                                         (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                                                         (tptr (.Tstruct dense.id.«_1024» noattr)),
                                                         tint,
                                                         tint]
                                                        .Tvoid)))
                                                  (.Ecast (ci 0 tint) (tptr .Tvoid))
                                                  tint)
                                                (sk
                                                  (.Scall none
                                                    (.Ederef
                                                      (.Efield
                                                        (.Evar dense.id.«nauty:dispatch»
                                                          (.Tstruct dense.id.«_1027» noattr))
                                                        dense.id.«cleanup»
                                                        (tptr
                                                          (tfun
                                                            [(tptr tulong),
                                                             (tptr (tptr tulong)),
                                                             (tptr tulong),
                                                             (tptr (tptr tulong)),
                                                             (tptr tint),
                                                             (tptr tint),
                                                             (tptr
                                                               (.Tstruct dense.id.«optionstruct» noattr)),
                                                             (tptr (.Tstruct dense.id.«_1024» noattr)),
                                                             tint,
                                                             tint]
                                                            .Tvoid)))
                                                      (tfun
                                                        [(tptr tulong),
                                                         (tptr (tptr tulong)),
                                                         (tptr tulong),
                                                         (tptr (tptr tulong)),
                                                         (tptr tint),
                                                         (tptr tint),
                                                         (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                                                         (tptr (.Tstruct dense.id.«_1024» noattr)),
                                                         tint,
                                                         tint]
                                                        .Tvoid))
                                                    [(pv dense.id.«g_arg»),
                                                     (.Eaddrof
                                                       (.Evar dense.id.«nauty:g» (tptr tulong))
                                                       (tptr (tptr tulong))),
                                                     (pv dense.id.«canong_arg»),
                                                     (.Eaddrof
                                                       (.Evar dense.id.«nauty:canong» (tptr tulong))
                                                       (tptr (tptr tulong))),
                                                     (pi dense.id.«lab»),
                                                     (pi dense.id.«ptn»),
                                                     (.Etempvar dense.id.«options»
                                                       (tptr (.Tstruct dense.id.«optionstruct» noattr))),
                                                     (.Etempvar dense.id.«stats_arg»
                                                       (tptr (.Tstruct dense.id.«_1024» noattr))),
                                                     (.Evar dense.id.«nauty:m» tint),
                                                     (.Evar dense.id.«nauty:n» tint)]))
                                                .Sskip))
                                            (.Sreturn none)))))))))))))))))))))
    .Sskip)

abbrev tcIf : statement :=
  (.Sifthenelse
    (.Ebinop .Ogt (.Evar dense.id.«nauty:m» tint) (.Evar dense.id.«nauty:alloc_m» tint) tint)
    (.Ssequence
      (sk
        (.Sset dense.id.«tcp»
          (.Efield
            (.Evar dense.id.«nauty:tcnode0» (.Tstruct dense.id.«tcnode_struct» noattr))
            dense.id.«next»
            (tptr (.Tstruct dense.id.«tcnode_struct» noattr)))))
      (.Ssequence
        (.Sloop
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .One
                  (.Etempvar dense.id.«tcp» (tptr (.Tstruct dense.id.«tcnode_struct» noattr)))
                  (.Ecast (ci 0 tint) (tptr .Tvoid))
                  tint)
                .Sskip
                .Sbreak))
            (.Ssequence
              (sk
                (.Sset dense.id.«tcq»
                  (.Efield
                    (.Ederef
                      (.Etempvar dense.id.«tcp» (tptr (.Tstruct dense.id.«tcnode_struct» noattr)))
                      (.Tstruct dense.id.«tcnode_struct» noattr))
                    dense.id.«next»
                    (tptr (.Tstruct dense.id.«tcnode_struct» noattr)))))
              (.Ssequence
                (sk
                  (.Scall none
                    (.Evar dense.id.«free» (tfun [(tptr .Tvoid)] .Tvoid))
                    [(.Efield
                       (.Ederef
                         (.Etempvar dense.id.«tcp» (tptr (.Tstruct dense.id.«tcnode_struct» noattr)))
                         (.Tstruct dense.id.«tcnode_struct» noattr))
                       dense.id.«tcellptr»
                       (tptr tulong))]))
                (.Ssequence
                  (sk
                    (.Scall none
                      (.Evar dense.id.«free» (tfun [(tptr .Tvoid)] .Tvoid))
                      [(.Etempvar dense.id.«tcp» (tptr (.Tstruct dense.id.«tcnode_struct» noattr)))]))
                  (sk
                    (.Sset dense.id.«tcp» (.Etempvar dense.id.«tcq» (tptr (.Tstruct dense.id.«tcnode_struct» noattr)))))))))
          .Sskip)
        (.Ssequence
          (sk (.Sassign (.Evar dense.id.«nauty:alloc_m» tint) (.Evar dense.id.«nauty:m» tint)))
          (sk
            (.Sassign
              (.Efield
                (.Evar dense.id.«nauty:tcnode0» (.Tstruct dense.id.«tcnode_struct» noattr))
                dense.id.«next»
                (tptr (.Tstruct dense.id.«tcnode_struct» noattr)))
              (.Ecast (ci 0 tint) (tptr .Tvoid)))))))
    .Sskip)

abbrev ptnIf : statement :=
  (.Sifthenelse
    (.Efield
      (.Ederef
        (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
        (.Tstruct dense.id.«optionstruct» noattr))
      dense.id.«defaultptn»
      tint)
    (.Ssequence
      (.Ssequence
        (sk (.Sset dense.id.«i» (ci 0 tint)))
        (.Sloop
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
                .Sskip
                .Sbreak))
            (.Ssequence
              (sk
                (.Sassign
                  (.Ederef (.Ebinop .Oadd (pi dense.id.«lab») (tv dense.id.«i») (tptr tint)) tint)
                  (tv dense.id.«i»)))
              (sk
                (.Sassign
                  (.Ederef (.Ebinop .Oadd (pi dense.id.«ptn») (tv dense.id.«i») (tptr tint)) tint)
                  (ci 2000000002 tint)))))
          (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint)))))
      (.Ssequence
        (sk
          (.Sassign
            (.Ederef
              (.Ebinop .Oadd
                (pi dense.id.«ptn»)
                (.Ebinop .Osub (.Evar dense.id.«nauty:n» tint) (ci 1 tint) tint)
                (tptr tint))
              tint)
            (ci 0 tint)))
        (.Ssequence
          (.Ssequence
            (sk
              (.Sset dense.id.«es_»
                (.Ebinop .Oadd
                  (.Ecast (.Evar dense.id.«nauty:active» (tptr tulong)) (tptr tulong))
                  (.Evar dense.id.«nauty:m» tint)
                  (tptr tulong))))
            (.Sloop
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Ebinop .Ogt
                      (pv dense.id.«es_»)
                      (.Ecast (.Evar dense.id.«nauty:active» (tptr tulong)) (tptr tulong))
                      tint)
                    .Sskip
                    .Sbreak))
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Sset
                        (idOf 730)
                        (.Ecast
                          (.Ebinop .Osub (pv dense.id.«es_») (ci 1 tint) (tptr tulong))
                          (tptr tulong))))
                    (.Sset dense.id.«es_» (pv (idOf 730))))
                  (.Sassign (.Ederef (pv (idOf 730)) tulong) (ci 0 tint))))
              .Sskip))
          (.Ssequence
            (sk
              (.Sassign
                (.Ederef
                  (.Ebinop .Oadd
                    (.Evar dense.id.«nauty:active» (tptr tulong))
                    (.Ebinop .Oshr (ci 0 tint) (ci 6 tint) tint)
                    (tptr tulong))
                  tulong)
                (.Ebinop .Oor
                  (.Ederef
                    (.Ebinop .Oadd
                      (.Evar dense.id.«nauty:active» (tptr tulong))
                      (.Ebinop .Oshr (ci 0 tint) (ci 6 tint) tint)
                      (tptr tulong))
                    tulong)
                  (.Ederef
                    (.Ebinop .Oadd
                      (.Evar dense.id.«nauty:bit» (tarray tulong 64))
                      (.Ebinop .Oand (ci 0 tint) (ci 63 tint) tint)
                      (tptr tulong))
                    tulong)
                  tulong)))
            (sk (.Sset dense.id.«numcells» (ci 1 tint)))))))
    (.Ssequence
      (sk
        (.Sassign
          (.Ederef
            (.Ebinop .Oadd
              (pi dense.id.«ptn»)
              (.Ebinop .Osub (.Evar dense.id.«nauty:n» tint) (ci 1 tint) tint)
              (tptr tint))
            tint)
          (ci 0 tint)))
      (.Ssequence
        (sk (.Sset dense.id.«numcells» (ci 0 tint)))
        (.Ssequence
          (.Ssequence
            (sk (.Sset dense.id.«i» (ci 0 tint)))
            (.Sloop
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
                    .Sskip
                    .Sbreak))
                (sk
                  (.Sifthenelse
                    (.Ebinop .One
                      (.Ederef (.Ebinop .Oadd (pi dense.id.«ptn») (tv dense.id.«i») (tptr tint)) tint)
                      (ci 0 tint)
                      tint)
                    (sk
                      (.Sassign
                        (.Ederef (.Ebinop .Oadd (pi dense.id.«ptn») (tv dense.id.«i») (tptr tint)) tint)
                        (ci 2000000002 tint)))
                    (sk (.Sset dense.id.«numcells» (.Ebinop .Oadd (tv dense.id.«numcells») (ci 1 tint) tint))))))
              (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint)))))
          (sk
            (.Sifthenelse
              (.Ebinop .Oeq (pv dense.id.«active_arg») (.Ecast (ci 0 tint) (tptr .Tvoid)) tint)
              (.Ssequence
                (.Ssequence
                  (sk
                    (.Sset dense.id.«es___1»
                      (.Ebinop .Oadd
                        (.Ecast (.Evar dense.id.«nauty:active» (tptr tulong)) (tptr tulong))
                        (.Evar dense.id.«nauty:m» tint)
                        (tptr tulong))))
                  (.Sloop
                    (.Ssequence
                      (sk
                        (.Sifthenelse
                          (.Ebinop .Ogt
                            (pv dense.id.«es___1»)
                            (.Ecast (.Evar dense.id.«nauty:active» (tptr tulong)) (tptr tulong))
                            tint)
                          .Sskip
                          .Sbreak))
                      (.Ssequence
                        (.Ssequence
                          (sk
                            (.Sset
                              (idOf 731)
                              (.Ecast
                                (.Ebinop .Osub (pv dense.id.«es___1») (ci 1 tint) (tptr tulong))
                                (tptr tulong))))
                          (.Sset dense.id.«es___1» (pv (idOf 731))))
                        (.Sassign (.Ederef (pv (idOf 731)) tulong) (ci 0 tint))))
                    .Sskip))
                (.Ssequence
                  (sk (.Sset dense.id.«i» (ci 0 tint)))
                  (.Sloop
                    (.Ssequence
                      (sk
                        (.Sifthenelse
                          (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
                          .Sskip
                          .Sbreak))
                      (.Ssequence
                        (sk
                          (.Sassign
                            (.Ederef
                              (.Ebinop .Oadd
                                (.Evar dense.id.«nauty:active» (tptr tulong))
                                (.Ebinop .Oshr (tv dense.id.«i») (ci 6 tint) tint)
                                (tptr tulong))
                              tulong)
                            (.Ebinop .Oor
                              (.Ederef
                                (.Ebinop .Oadd
                                  (.Evar dense.id.«nauty:active» (tptr tulong))
                                  (.Ebinop .Oshr (tv dense.id.«i») (ci 6 tint) tint)
                                  (tptr tulong))
                                tulong)
                              (.Ederef
                                (.Ebinop .Oadd
                                  (.Evar dense.id.«nauty:bit» (tarray tulong 64))
                                  (.Ebinop .Oand (tv dense.id.«i») (ci 63 tint) tint)
                                  (tptr tulong))
                                tulong)
                              tulong)))
                        (.Sloop
                          (.Ssequence
                            (sk
                              (.Sifthenelse
                                (.Ederef (.Ebinop .Oadd (pi dense.id.«ptn») (tv dense.id.«i») (tptr tint)) tint)
                                .Sskip
                                .Sbreak))
                            (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))
                          .Sskip)))
                    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))))
              (.Ssequence
                (sk (.Sset dense.id.«i» (ci 0 tint)))
                (.Sloop
                  (.Ssequence
                    (sk
                      (.Sifthenelse
                        (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:m» tint) tint)
                        .Sskip
                        .Sbreak))
                    (sk
                      (.Sassign
                        (.Ederef
                          (.Ebinop .Oadd
                            (.Evar dense.id.«nauty:active» (tptr tulong))
                            (tv dense.id.«i»)
                            (tptr tulong))
                          tulong)
                        (.Ederef
                          (.Ebinop .Oadd (pv dense.id.«active_arg») (tv dense.id.«i») (tptr tulong))
                          tulong))))
                  (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint)))))))))))

abbrev postIf : statement :=
  (.Sifthenelse
    (.Ebinop .Oeq (tv dense.id.«retval») (.Eunop .Oneg (ci 11 tint) tint) tint)
    (sk
      (.Sassign
        (.Efield
          (.Ederef
            (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
            (.Tstruct dense.id.«_1024» noattr))
          dense.id.«errstatus»
          tint)
        (ci 4 tint)))
    (sk
      (.Sifthenelse
        (.Ebinop .Oeq (tv dense.id.«retval») (.Eunop .Oneg (ci 12 tint) tint) tint)
        (sk
          (.Sassign
            (.Efield
              (.Ederef
                (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                (.Tstruct dense.id.«_1024» noattr))
              dense.id.«errstatus»
              tint)
            (ci 5 tint)))
        (.Ssequence
          (sk
            (.Sifthenelse
              (.Evar dense.id.«nauty:getcanon» tint)
              (.Ssequence
                (sk
                  (.Scall none
                    (.Ederef
                      (.Efield
                        (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
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
                  (sk (.Sset dense.id.«i» (ci 0 tint)))
                  (.Sloop
                    (.Ssequence
                      (sk
                        (.Sifthenelse
                          (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
                          .Sskip
                          .Sbreak))
                      (sk
                        (.Sassign
                          (.Ederef (.Ebinop .Oadd (pi dense.id.«lab») (tv dense.id.«i») (tptr tint)) tint)
                          (.Ederef
                            (.Ebinop .Oadd
                              (.Evar dense.id.«nauty:canonlab» (tptr tint))
                              (tv dense.id.«i»)
                              (tptr tint))
                            tint))))
                    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))))
              .Sskip))
          (.Ssequence
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .Oeq (.Evar dense.id.«nauty:invarsuclevel» tint) (ci 2000000002 tint) tint)
                  (sk (.Sset (idOf 736) (.Ecast (ci 0 tint) tint)))
                  (sk (.Sset (idOf 736) (.Ecast (.Evar dense.id.«nauty:invarsuclevel» tint) tint)))))
              (.Sassign
                (.Efield
                  (.Ederef
                    (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                    (.Tstruct dense.id.«_1024» noattr))
                  dense.id.«invarsuclevel»
                  tint)
                (tv (idOf 736))))
            (.Ssequence
              (sk
                (.Sassign
                  (.Efield
                    (.Ederef
                      (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                      (.Tstruct dense.id.«_1024» noattr))
                    dense.id.«invapplics»
                    tulong)
                  (.Evar dense.id.«nauty:invapplics» tulong)))
              (sk
                (.Sassign
                  (.Efield
                    (.Ederef
                      (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                      (.Tstruct dense.id.«_1024» noattr))
                    dense.id.«invsuccesses»
                    tulong)
                  (.Evar dense.id.«nauty:invsuccesses» tulong)))))))))

abbrev freeIf : statement :=
  (.Sifthenelse
    (.Ebinop .Oge (.Evar dense.id.«nauty:n» tint) (ci 320 tint) tint)
    (.Ssequence
      (sk (.Scall none (.Evar dense.id.«nautil_freedyn» (tfun [] .Tvoid)) []))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .One
              (.Efield
                (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                dense.id.«freedyn»
                (tptr (tfun [] .Tvoid)))
              (.Ecast (ci 0 tint) (tptr .Tvoid))
              tint)
            (sk
              (.Scall none
                (.Ederef
                  (.Efield
                    (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                    dense.id.«freedyn»
                    (tptr (tfun [] .Tvoid)))
                  (tfun [] .Tvoid))
                []))
            .Sskip))
        (sk (.Scall none (.Evar dense.id.«nauty_freedyn» (tfun [] .Tvoid)) []))))
    .Sskip)

abbrev tFree : statement :=
  (.Ssequence
    (sk freeIf)
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .One
            (.Efield
              (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
              dense.id.«cleanup»
              (tptr
                (tfun
                  [(tptr tulong),
                   (tptr (tptr tulong)),
                   (tptr tulong),
                   (tptr (tptr tulong)),
                   (tptr tint),
                   (tptr tint),
                   (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                   (tptr (.Tstruct dense.id.«_1024» noattr)),
                   tint,
                   tint]
                  .Tvoid)))
            (.Ecast (ci 0 tint) (tptr .Tvoid))
            tint)
          (sk
            (.Scall none
              (.Ederef
                (.Efield
                  (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                  dense.id.«cleanup»
                  (tptr
                    (tfun
                      [(tptr tulong),
                       (tptr (tptr tulong)),
                       (tptr tulong),
                       (tptr (tptr tulong)),
                       (tptr tint),
                       (tptr tint),
                       (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                       (tptr (.Tstruct dense.id.«_1024» noattr)),
                       tint,
                       tint]
                      .Tvoid)))
                (tfun
                  [(tptr tulong),
                   (tptr (tptr tulong)),
                   (tptr tulong),
                   (tptr (tptr tulong)),
                   (tptr tint),
                   (tptr tint),
                   (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                   (tptr (.Tstruct dense.id.«_1024» noattr)),
                   tint,
                   tint]
                  .Tvoid))
              [(pv dense.id.«g_arg»),
               (.Eaddrof (.Evar dense.id.«nauty:g» (tptr tulong)) (tptr (tptr tulong))),
               (pv dense.id.«canong_arg»),
               (.Eaddrof (.Evar dense.id.«nauty:canong» (tptr tulong)) (tptr (tptr tulong))),
               (pi dense.id.«lab»),
               (pi dense.id.«ptn»),
               (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr))),
               (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr))),
               (.Evar dense.id.«nauty:m» tint),
               (.Evar dense.id.«nauty:n» tint)]))
          .Sskip))
      (sk
        (.Sifthenelse
          (.Evar dense.id.«nauty:doschreier» tint)
          (.Ssequence
            (sk
              (.Scall none
                (.Evar dense.id.«freeschreier»
                  (tfun
                    [(tptr (tptr (.Tstruct dense.id.«schreierlevel» noattr))),
                     (tptr (tptr (.Tstruct dense.id.«permnodestruct» noattr)))]
                    .Tvoid))
                [(.Eaddrof
                   (.Evar dense.id.«nauty:gp» (tptr (.Tstruct dense.id.«schreierlevel» noattr)))
                   (tptr (tptr (.Tstruct dense.id.«schreierlevel» noattr)))),
                 (.Eaddrof
                   (.Evar dense.id.«nauty:gens» (tptr (.Tstruct dense.id.«permnodestruct» noattr)))
                   (tptr (tptr (.Tstruct dense.id.«permnodestruct» noattr))))]))
            (sk
              (.Sifthenelse
                (.Ebinop .Oge (.Evar dense.id.«nauty:n» tint) (ci 320 tint) tint)
                (sk (.Scall none (.Evar dense.id.«schreier_freedyn» (tfun [] .Tvoid)) []))
                .Sskip)))
          .Sskip))))

abbrev tPost : statement :=
  (.Ssequence (sk postIf) tFree)

abbrev tRoot : statement :=
  (.Ssequence
    (.Ssequence
      (sk
        (.Scall
          (some (idOf 735))
          (.Evar dense.id.«nauty:firstpathnode0»
            (tfun
              [(tptr tint), (tptr tint), tint, tint, (tptr (.Tstruct dense.id.«tcnode_struct» noattr))]
              tint))
          [(pi dense.id.«lab»),
           (pi dense.id.«ptn»),
           (ci 1 tint),
           (tv dense.id.«numcells»),
           (.Eaddrof
             (.Evar dense.id.«nauty:tcnode0» (.Tstruct dense.id.«tcnode_struct» noattr))
             (tptr (.Tstruct dense.id.«tcnode_struct» noattr)))]))
      (.Sset dense.id.«retval» (tv (idOf 735))))
    tPost)

abbrev tWork : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Oge
          (tv dense.id.«worksize»)
          (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint)
          tint)
        (sk (.Sassign (.Evar dense.id.«nauty:workspace» (tptr tulong)) (pv dense.id.«ws_arg»)))
        (.Ssequence
          (sk
            (.Sassign
              (.Evar dense.id.«nauty:workspace» (tptr tulong))
              (.Evar dense.id.«nauty:defltwork» (tptr tulong))))
          (sk (.Sset dense.id.«worksize» (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint))))))
    (.Ssequence
      (sk
        (.Sassign
          (.Evar dense.id.«nauty:worktop» (tptr tulong))
          (.Ebinop .Oadd
            (.Evar dense.id.«nauty:workspace» (tptr tulong))
            (.Ebinop .Osub
              (tv dense.id.«worksize»)
              (.Ebinop .Omod
                (tv dense.id.«worksize»)
                (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint)
                tint)
              tint)
            (tptr tulong))))
      (.Ssequence
        (sk
          (.Sassign
            (.Evar dense.id.«nauty:fmptr» (tptr tulong))
            (.Evar dense.id.«nauty:workspace» (tptr tulong))))
        (.Ssequence
          (sk
            (.Sassign
              (.Efield
                (.Ederef
                  (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                  (.Tstruct dense.id.«_1024» noattr))
                dense.id.«errstatus»
                tint)
              (ci 0 tint)))
          (.Ssequence
            (sk (.Sassign (.Evar dense.id.«nauty:needshortprune» tint) (ci 0 tint)))
            (.Ssequence
              (sk (.Sassign (.Evar dense.id.«nauty:invarsuclevel» tint) (ci 2000000002 tint)))
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk (.Sset (idOf 734) (.Ecast (ci 0 tint) tulong)))
                    (.Sassign (.Evar dense.id.«nauty:invsuccesses» tulong) (.Etempvar (idOf 734) tulong)))
                  (.Sassign (.Evar dense.id.«nauty:invapplics» tulong) (.Etempvar (idOf 734) tulong)))
                tRoot)))))))

abbrev tStats : statement :=
  (.Ssequence
    (sk
      (.Sassign
        (.Efield
          (.Ederef
            (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
            (.Tstruct dense.id.«_1024» noattr))
          dense.id.«grpsize1»
          tdouble)
        (.Econst_float
          (CompCert4Lean.Lib.Floats.Float.of_bits (NautyVerified.Word.lr 4607182418800017408))
          tdouble)))
    (.Ssequence
      (sk
        (.Sassign
          (.Efield
            (.Ederef
              (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
              (.Tstruct dense.id.«_1024» noattr))
            dense.id.«grpsize2»
            tint)
          (ci 0 tint)))
      (.Ssequence
        (sk
          (.Sassign
            (.Efield
              (.Ederef
                (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                (.Tstruct dense.id.«_1024» noattr))
              dense.id.«numgenerators»
              tint)
            (ci 0 tint)))
        (.Ssequence
          (sk
            (.Sassign
              (.Efield
                (.Ederef
                  (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                  (.Tstruct dense.id.«_1024» noattr))
                dense.id.«numnodes»
                tulong)
              (ci 0 tint)))
          (.Ssequence
            (sk
              (.Sassign
                (.Efield
                  (.Ederef
                    (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                    (.Tstruct dense.id.«_1024» noattr))
                  dense.id.«numbadleaves»
                  tulong)
                (ci 0 tint)))
            (.Ssequence
              (sk
                (.Sassign
                  (.Efield
                    (.Ederef
                      (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                      (.Tstruct dense.id.«_1024» noattr))
                    dense.id.«tctotal»
                    tulong)
                  (ci 0 tint)))
              (.Ssequence
                (sk
                  (.Sassign
                    (.Efield
                      (.Ederef
                        (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                        (.Tstruct dense.id.«_1024» noattr))
                      dense.id.«canupdates»
                      tulong)
                    (ci 0 tint)))
                (.Ssequence
                  (sk
                    (.Sassign
                      (.Efield
                        (.Ederef
                          (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                          (.Tstruct dense.id.«_1024» noattr))
                        dense.id.«numorbits»
                        tint)
                      (.Evar dense.id.«nauty:n» tint)))
                  (.Ssequence
                    (.Ssequence
                      (sk
                        (.Sset dense.id.«es___2»
                          (.Ebinop .Oadd
                            (.Ecast (.Evar dense.id.«nauty:fixedpts» (tptr tulong)) (tptr tulong))
                            (.Evar dense.id.«nauty:m» tint)
                            (tptr tulong))))
                      (.Sloop
                        (.Ssequence
                          (sk
                            (.Sifthenelse
                              (.Ebinop .Ogt
                                (pv dense.id.«es___2»)
                                (.Ecast (.Evar dense.id.«nauty:fixedpts» (tptr tulong)) (tptr tulong))
                                tint)
                              .Sskip
                              .Sbreak))
                          (.Ssequence
                            (.Ssequence
                              (sk
                                (.Sset
                                  (idOf 733)
                                  (.Ecast
                                    (.Ebinop .Osub (pv dense.id.«es___2») (ci 1 tint) (tptr tulong))
                                    (tptr tulong))))
                              (.Sset dense.id.«es___2» (pv (idOf 733))))
                            (.Sassign (.Ederef (pv (idOf 733)) tulong) (ci 0 tint))))
                        .Sskip))
                    (.Ssequence
                      (sk (.Sassign (.Evar dense.id.«nauty:noncheaplevel» tint) (ci 1 tint)))
                      (.Ssequence
                        (sk
                          (.Sassign
                            (.Evar dense.id.«nauty:eqlev_canon» tint)
                            (.Eunop .Oneg (ci 1 tint) tint)))
                        tWork)))))))))))

abbrev tOrbits : statement :=
  (.Ssequence
    (.Ssequence
      (sk (.Sset dense.id.«i» (ci 0 tint)))
      (.Sloop
        (.Ssequence
          (sk
            (.Sifthenelse (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint) .Sskip .Sbreak))
          (sk
            (.Sassign
              (.Ederef
                (.Ebinop .Oadd (.Evar dense.id.«nauty:orbits» (tptr tint)) (tv dense.id.«i») (tptr tint))
                tint)
              (tv dense.id.«i»))))
        (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint)))))
    tStats)

abbrev tInit : statement :=
  (.Ssequence
    (.Ssequence
      (.Ssequence
        (sk (.Sset (idOf 732) (.Ecast (.Ecast (ci 0 tint) (tptr .Tvoid)) (tptr tulong))))
        (.Sassign (.Evar dense.id.«nauty:canong» (tptr tulong)) (pv (idOf 732))))
      (.Sassign (.Evar dense.id.«nauty:g» (tptr tulong)) (pv (idOf 732))))
    (.Ssequence
      (sk (.Sassign (.Evar dense.id.«initstatus» tint) (ci 0 tint)))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .One
              (.Efield
                (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                dense.id.«init»
                (tptr
                  (tfun
                    [(tptr tulong),
                     (tptr (tptr tulong)),
                     (tptr tulong),
                     (tptr (tptr tulong)),
                     (tptr tint),
                     (tptr tint),
                     (tptr tulong),
                     (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                     (tptr tint),
                     tint,
                     tint]
                    .Tvoid)))
              (.Ecast (ci 0 tint) (tptr .Tvoid))
              tint)
            (sk
              (.Scall none
                (.Ederef
                  (.Efield
                    (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                    dense.id.«init»
                    (tptr
                      (tfun
                        [(tptr tulong),
                         (tptr (tptr tulong)),
                         (tptr tulong),
                         (tptr (tptr tulong)),
                         (tptr tint),
                         (tptr tint),
                         (tptr tulong),
                         (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                         (tptr tint),
                         tint,
                         tint]
                        .Tvoid)))
                  (tfun
                    [(tptr tulong),
                     (tptr (tptr tulong)),
                     (tptr tulong),
                     (tptr (tptr tulong)),
                     (tptr tint),
                     (tptr tint),
                     (tptr tulong),
                     (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                     (tptr tint),
                     tint,
                     tint]
                    .Tvoid))
                [(pv dense.id.«g_arg»),
                 (.Eaddrof (.Evar dense.id.«nauty:g» (tptr tulong)) (tptr (tptr tulong))),
                 (pv dense.id.«canong_arg»),
                 (.Eaddrof (.Evar dense.id.«nauty:canong» (tptr tulong)) (tptr (tptr tulong))),
                 (pi dense.id.«lab»),
                 (pi dense.id.«ptn»),
                 (.Evar dense.id.«nauty:active» (tptr tulong)),
                 (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr))),
                 (.Eaddrof (.Evar dense.id.«initstatus» tint) (tptr tint)),
                 (.Evar dense.id.«nauty:m» tint),
                 (.Evar dense.id.«nauty:n» tint)]))
            .Sskip))
        (.Ssequence
          (sk
            (.Sifthenelse
              (.Evar dense.id.«initstatus» tint)
              (.Ssequence
                (sk
                  (.Sassign
                    (.Efield
                      (.Ederef
                        (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
                        (.Tstruct dense.id.«_1024» noattr))
                      dense.id.«errstatus»
                      tint)
                    (.Evar dense.id.«initstatus» tint)))
                (.Sreturn none))
              .Sskip))
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .Oeq
                  (.Evar dense.id.«nauty:g» (tptr tulong))
                  (.Ecast (ci 0 tint) (tptr .Tvoid))
                  tint)
                (sk (.Sassign (.Evar dense.id.«nauty:g» (tptr tulong)) (pv dense.id.«g_arg»)))
                .Sskip))
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .Oeq
                    (.Evar dense.id.«nauty:canong» (tptr tulong))
                    (.Ecast (ci 0 tint) (tptr .Tvoid))
                    tint)
                  (sk (.Sassign (.Evar dense.id.«nauty:canong» (tptr tulong)) (pv dense.id.«canong_arg»)))
                  .Sskip))
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Evar dense.id.«nauty:doschreier» tint)
                    (sk
                      (.Scall none
                        (.Evar dense.id.«newgroup»
                          (tfun
                            [(tptr (tptr (.Tstruct dense.id.«schreierlevel» noattr))),
                             (tptr (tptr (.Tstruct dense.id.«permnodestruct» noattr))),
                             tint]
                            .Tvoid))
                        [(.Eaddrof
                           (.Evar dense.id.«nauty:gp» (tptr (.Tstruct dense.id.«schreierlevel» noattr)))
                           (tptr (tptr (.Tstruct dense.id.«schreierlevel» noattr)))),
                         (.Eaddrof
                           (.Evar dense.id.«nauty:gens» (tptr (.Tstruct dense.id.«permnodestruct» noattr)))
                           (tptr (tptr (.Tstruct dense.id.«permnodestruct» noattr)))),
                         (.Evar dense.id.«nauty:n» tint)]))
                    .Sskip))
                tOrbits)))))))

abbrev tPtn : statement :=
  (.Ssequence (sk ptnIf) tInit)

abbrev tOpts : statement :=
  (.Ssequence
    (sk (.Sassign (.Evar dense.id.«nauty:orbits» (tptr tint)) (pi dense.id.«orbits_arg»)))
    (.Ssequence
      (sk
        (.Sassign
          (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr)))
          (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))))
      (.Ssequence
        (sk
          (.Sassign
            (.Evar dense.id.«nauty:getcanon» tint)
            (.Efield
              (.Ederef
                (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                (.Tstruct dense.id.«optionstruct» noattr))
              dense.id.«getcanon»
              tint)))
        (.Ssequence
          (sk
            (.Sassign
              (.Evar dense.id.«nauty:digraph» tint)
              (.Efield
                (.Ederef
                  (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                  (.Tstruct dense.id.«optionstruct» noattr))
                dense.id.«digraph»
                tint)))
          (.Ssequence
            (sk
              (.Sassign
                (.Evar dense.id.«nauty:writeautoms» tint)
                (.Efield
                  (.Ederef
                    (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                    (.Tstruct dense.id.«optionstruct» noattr))
                  dense.id.«writeautoms»
                  tint)))
            (.Ssequence
              (sk
                (.Sassign
                  (.Evar dense.id.«nauty:domarkers» tint)
                  (.Efield
                    (.Ederef
                      (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                      (.Tstruct dense.id.«optionstruct» noattr))
                    dense.id.«writemarkers»
                    tint)))
              (.Ssequence
                (sk
                  (.Sassign
                    (.Evar dense.id.«nauty:cartesian» tint)
                    (.Efield
                      (.Ederef
                        (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                        (.Tstruct dense.id.«optionstruct» noattr))
                      dense.id.«cartesian»
                      tint)))
                (.Ssequence
                  (sk
                    (.Sassign
                      (.Evar dense.id.«nauty:doschreier» tint)
                      (.Efield
                        (.Ederef
                          (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                          (.Tstruct dense.id.«optionstruct» noattr))
                        dense.id.«schreier»
                        tint)))
                  (.Ssequence
                    (sk
                      (.Sifthenelse
                        (.Evar dense.id.«nauty:doschreier» tint)
                        (sk
                          (.Scall none
                            (.Evar dense.id.«schreier_check» (tfun [tint, tint, tint, tint] .Tvoid))
                            [(ci 64 tint),
                             (.Evar dense.id.«nauty:m» tint),
                             (.Evar dense.id.«nauty:n» tint),
                             (.Ebinop .Oadd (ci 29300 tint) (ci 0 tint) tint)]))
                        .Sskip))
                    (.Ssequence
                      (sk
                        (.Sassign
                          (.Evar dense.id.«nauty:linelength» tint)
                          (.Efield
                            (.Ederef
                              (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                              (.Tstruct dense.id.«optionstruct» noattr))
                            dense.id.«linelength»
                            tint)))
                      (.Ssequence
                        (sk
                          (.Sifthenelse
                            (.Evar dense.id.«nauty:digraph» tint)
                            (sk (.Sassign (.Evar dense.id.«nauty:tc_level» tint) (ci 0 tint)))
                            (sk
                              (.Sassign
                                (.Evar dense.id.«nauty:tc_level» tint)
                                (.Efield
                                  (.Ederef
                                    (.Etempvar dense.id.«options»
                                      (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                    (.Tstruct dense.id.«optionstruct» noattr))
                                  dense.id.«tc_level»
                                  tint)))))
                        (.Ssequence
                          (.Ssequence
                            (sk
                              (.Sifthenelse
                                (.Ebinop .Oeq
                                  (.Efield
                                    (.Ederef
                                      (.Etempvar dense.id.«options»
                                        (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                      (.Tstruct dense.id.«optionstruct» noattr))
                                    dense.id.«outfile»
                                    (tptr (.Tstruct dense.id.«_IO_FILE» noattr)))
                                  (.Ecast (ci 0 tint) (tptr .Tvoid))
                                  tint)
                                (sk
                                  (.Sset
                                    (idOf 727)
                                    (.Ecast
                                      (.Evar dense.id.«stdout» (tptr (.Tstruct dense.id.«_IO_FILE» noattr)))
                                      (tptr (.Tstruct dense.id.«_IO_FILE» noattr)))))
                                (sk
                                  (.Sset
                                    (idOf 727)
                                    (.Ecast
                                      (.Efield
                                        (.Ederef
                                          (.Etempvar dense.id.«options»
                                            (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                          (.Tstruct dense.id.«optionstruct» noattr))
                                        dense.id.«outfile»
                                        (tptr (.Tstruct dense.id.«_IO_FILE» noattr)))
                                      (tptr (.Tstruct dense.id.«_IO_FILE» noattr)))))))
                            (.Sassign
                              (.Evar dense.id.«nauty:outfile» (tptr (.Tstruct dense.id.«_IO_FILE» noattr)))
                              (.Etempvar (idOf 727) (tptr (.Tstruct dense.id.«_IO_FILE» noattr)))))
                          (.Ssequence
                            (sk
                              (.Sassign
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
                                (.Efield
                                  (.Ederef
                                    (.Etempvar dense.id.«options»
                                      (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                    (.Tstruct dense.id.«optionstruct» noattr))
                                  dense.id.«usernodeproc»
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
                                      .Tvoid)))))
                            (.Ssequence
                              (sk
                                (.Sassign
                                  (.Evar dense.id.«nauty:userautomproc»
                                    (tptr
                                      (tfun
                                        [tint, (tptr tint), (tptr tint), tint, tint, tint]
                                        .Tvoid)))
                                  (.Efield
                                    (.Ederef
                                      (.Etempvar dense.id.«options»
                                        (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                      (.Tstruct dense.id.«optionstruct» noattr))
                                    dense.id.«userautomproc»
                                    (tptr
                                      (tfun
                                        [tint, (tptr tint), (tptr tint), tint, tint, tint]
                                        .Tvoid)))))
                              (.Ssequence
                                (sk
                                  (.Sassign
                                    (.Evar dense.id.«nauty:userlevelproc»
                                      (tptr
                                        (tfun
                                          [(tptr tint),
                                           (tptr tint),
                                           tint,
                                           (tptr tint),
                                           (tptr (.Tstruct dense.id.«_1024» noattr)),
                                           tint,
                                           tint,
                                           tint,
                                           tint,
                                           tint,
                                           tint]
                                          .Tvoid)))
                                    (.Efield
                                      (.Ederef
                                        (.Etempvar dense.id.«options»
                                          (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                        (.Tstruct dense.id.«optionstruct» noattr))
                                      dense.id.«userlevelproc»
                                      (tptr
                                        (tfun
                                          [(tptr tint),
                                           (tptr tint),
                                           tint,
                                           (tptr tint),
                                           (tptr (.Tstruct dense.id.«_1024» noattr)),
                                           tint,
                                           tint,
                                           tint,
                                           tint,
                                           tint,
                                           tint]
                                          .Tvoid)))))
                                (.Ssequence
                                  (sk
                                    (.Sassign
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
                                      (.Efield
                                        (.Ederef
                                          (.Etempvar dense.id.«options»
                                            (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                          (.Tstruct dense.id.«optionstruct» noattr))
                                        dense.id.«usercanonproc»
                                        (tptr
                                          (tfun
                                            [(tptr tulong),
                                             (tptr tint),
                                             (tptr tulong),
                                             tulong,
                                             tint,
                                             tint,
                                             tint]
                                            tint)))))
                                  (.Ssequence
                                    (sk
                                      (.Sassign
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
                                              .Tvoid)))
                                        (.Efield
                                          (.Ederef
                                            (.Etempvar dense.id.«options»
                                              (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                            (.Tstruct dense.id.«optionstruct» noattr))
                                          dense.id.«invarproc»
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
                                              .Tvoid)))))
                                    (.Ssequence
                                      (.Ssequence
                                        (sk
                                          (.Sifthenelse
                                            (.Ebinop .Olt
                                              (.Efield
                                                (.Ederef
                                                  (.Etempvar dense.id.«options»
                                                    (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                                  (.Tstruct dense.id.«optionstruct» noattr))
                                                dense.id.«mininvarlevel»
                                                tint)
                                              (ci 0 tint)
                                              tint)
                                            (sk
                                              (.Sset
                                                (idOf 728)
                                                (.Ecast
                                                  (.Efield
                                                    (.Ederef
                                                      (.Etempvar dense.id.«options»
                                                        (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                                      (.Tstruct dense.id.«optionstruct» noattr))
                                                    dense.id.«getcanon»
                                                    tint)
                                                  tbool)))
                                            (.Sset (idOf 728) (ci 0 tint))))
                                        (.Sifthenelse
                                          (tv (idOf 728))
                                          (sk
                                            (.Sassign
                                              (.Evar dense.id.«nauty:mininvarlevel» tint)
                                              (.Eunop .Oneg
                                                (.Efield
                                                  (.Ederef
                                                    (.Etempvar dense.id.«options»
                                                      (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                                    (.Tstruct dense.id.«optionstruct» noattr))
                                                  dense.id.«mininvarlevel»
                                                  tint)
                                                tint)))
                                          (sk
                                            (.Sassign
                                              (.Evar dense.id.«nauty:mininvarlevel» tint)
                                              (.Efield
                                                (.Ederef
                                                  (.Etempvar dense.id.«options»
                                                    (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                                  (.Tstruct dense.id.«optionstruct» noattr))
                                                dense.id.«mininvarlevel»
                                                tint)))))
                                      (.Ssequence
                                        (.Ssequence
                                          (sk
                                            (.Sifthenelse
                                              (.Ebinop .Olt
                                                (.Efield
                                                  (.Ederef
                                                    (.Etempvar dense.id.«options»
                                                      (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                                    (.Tstruct dense.id.«optionstruct» noattr))
                                                  dense.id.«maxinvarlevel»
                                                  tint)
                                                (ci 0 tint)
                                                tint)
                                              (sk
                                                (.Sset
                                                  (idOf 729)
                                                  (.Ecast
                                                    (.Efield
                                                      (.Ederef
                                                        (.Etempvar dense.id.«options»
                                                          (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                                        (.Tstruct dense.id.«optionstruct» noattr))
                                                      dense.id.«getcanon»
                                                      tint)
                                                    tbool)))
                                              (.Sset (idOf 729) (ci 0 tint))))
                                          (.Sifthenelse
                                            (tv (idOf 729))
                                            (sk
                                              (.Sassign
                                                (.Evar dense.id.«nauty:maxinvarlevel» tint)
                                                (.Eunop .Oneg
                                                  (.Efield
                                                    (.Ederef
                                                      (.Etempvar dense.id.«options»
                                                        (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                                      (.Tstruct dense.id.«optionstruct» noattr))
                                                    dense.id.«maxinvarlevel»
                                                    tint)
                                                  tint)))
                                            (sk
                                              (.Sassign
                                                (.Evar dense.id.«nauty:maxinvarlevel» tint)
                                                (.Efield
                                                  (.Ederef
                                                    (.Etempvar dense.id.«options»
                                                      (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                                    (.Tstruct dense.id.«optionstruct» noattr))
                                                  dense.id.«maxinvarlevel»
                                                  tint)))))
                                        (.Ssequence
                                          (sk
                                            (.Sassign
                                              (.Evar dense.id.«nauty:invararg» tint)
                                              (.Efield
                                                (.Ederef
                                                  (.Etempvar dense.id.«options»
                                                    (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                                                  (.Tstruct dense.id.«optionstruct» noattr))
                                                dense.id.«invararg»
                                                tint)))
                                          (.Ssequence
                                            (sk
                                              (.Sifthenelse
                                                (.Evar dense.id.«nauty:getcanon» tint)
                                                (sk
                                                  (.Sifthenelse
                                                    (.Ebinop .Oeq
                                                      (pv dense.id.«canong_arg»)
                                                      (.Ecast (ci 0 tint) (tptr .Tvoid))
                                                      tint)
                                                    (.Ssequence
                                                      (sk
                                                        (.Sassign
                                                          (.Efield
                                                            (.Ederef
                                                              (.Etempvar dense.id.«stats_arg»
                                                                (tptr (.Tstruct dense.id.«_1024» noattr)))
                                                              (.Tstruct dense.id.«_1024» noattr))
                                                            dense.id.«errstatus»
                                                            tint)
                                                          (ci 3 tint)))
                                                      (.Ssequence
                                                        (sk
                                                          (.Scall none
                                                            (.Evar dense.id.«fprintf»
                                                              (.Tfunction
                                                                [(tptr
                                                                   (.Tstruct dense.id.«_IO_FILE» noattr)),
                                                                 (tptr tschar)]
                                                                tint
                                                                ⟨
                                                                (some (zOfInt 2))
                                                                ,
                                                                false
                                                                ,
                                                                false⟩))
                                                            [(.Evar dense.id.«stderr»
                                                               (tptr (.Tstruct dense.id.«_IO_FILE» noattr))),
                                                             (.Evar dense.id.«nauty:__stringlit_7»
                                                               (tarray tschar 47))]))
                                                        (.Sreturn none)))
                                                    .Sskip))
                                                .Sskip))
                                            tPtn)))))))))))))))))))))

abbrev tTc : statement :=
  (.Ssequence (sk tcIf) tOpts)

abbrev tAlloc : statement :=
  (.Ssequence
    (dynalloc1 dense.id.«nauty:defltwork_sz» dense.id.«nauty:defltwork» tulong
      (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint)
      (idOf 709)
      (idOf 710)
      dense.id.«nauty:__stringlit_6»
      6)
    (.Ssequence
      (dynalloc1 dense.id.«nauty:fixedpts_sz» dense.id.«nauty:fixedpts» tulong
        (.Evar dense.id.«nauty:m» tint)
        (idOf 711)
        (idOf 712)
        dense.id.«nauty:__stringlit_6»
        6)
      (.Ssequence
        (dynalloc1 dense.id.«nauty:active_sz» dense.id.«nauty:active» tulong
          (.Evar dense.id.«nauty:m» tint)
          (idOf 713)
          (idOf 714)
          dense.id.«nauty:__stringlit_6»
          6)
        (.Ssequence
          (dynalloc1 dense.id.«nauty:workperm_sz» dense.id.«nauty:workperm» tint
            (.Evar dense.id.«nauty:n» tint)
            (idOf 715)
            (idOf 716)
            dense.id.«nauty:__stringlit_6»
            6)
          (.Ssequence
            (dynalloc1 dense.id.«nauty:firstlab_sz» dense.id.«nauty:firstlab» tint
              (.Evar dense.id.«nauty:n» tint)
              (idOf 717)
              (idOf 718)
              dense.id.«nauty:__stringlit_6»
              6)
            (.Ssequence
              (dynalloc1 dense.id.«nauty:canonlab_sz» dense.id.«nauty:canonlab» tint
                (.Evar dense.id.«nauty:n» tint)
                (idOf 719)
                (idOf 720)
                dense.id.«nauty:__stringlit_6»
                6)
              (.Ssequence
                (dynalloc1 dense.id.«nauty:firstcode_sz» dense.id.«nauty:firstcode» tshort
                  (.Ebinop .Oadd (.Evar dense.id.«nauty:n» tint) (ci 2 tint) tint)
                  (idOf 721)
                  (idOf 722)
                  dense.id.«nauty:__stringlit_6»
                  6)
                (.Ssequence
                  (dynalloc1 dense.id.«nauty:canoncode_sz» dense.id.«nauty:canoncode» tshort
                    (.Ebinop .Oadd (.Evar dense.id.«nauty:n» tint) (ci 2 tint) tint)
                    (idOf 723)
                    (idOf 724)
                    dense.id.«nauty:__stringlit_6»
                    6)
                  (.Ssequence
                    (dynalloc1 dense.id.«nauty:firsttc_sz» dense.id.«nauty:firsttc» tint
                      (.Ebinop .Oadd (.Evar dense.id.«nauty:n» tint) (ci 2 tint) tint)
                      (idOf 725)
                      (idOf 726)
                      dense.id.«nauty:__stringlit_6»
                      6)
                    tTc)))))))))

abbrev tMain : statement :=
  (.Ssequence
    (sk (.Sassign (.Evar dense.id.«nauty:m» tint) (tv dense.id.«m_arg»)))
    (.Ssequence
      (sk (.Sassign (.Evar dense.id.«nauty:n» tint) (tv dense.id.«n_arg»)))
      (.Ssequence
        (sk
          (.Scall none
            (.Evar dense.id.«nautil_check» (tfun [tint, tint, tint, tint] .Tvoid))
            [(ci 64 tint),
             (.Evar dense.id.«nauty:m» tint),
             (.Evar dense.id.«nauty:n» tint),
             (.Ebinop .Oadd (ci 29300 tint) (ci 0 tint) tint)]))
        (.Ssequence
          (sk
            (.Sifthenelse
              (.Ebinop .One
                (.Efield
                  (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                  dense.id.«check»
                  (tptr (tfun [tint, tint, tint, tint] .Tvoid)))
                (.Ecast (ci 0 tint) (tptr .Tvoid))
                tint)
              (sk
                (.Scall none
                  (.Ederef
                    (.Efield
                      (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                      dense.id.«check»
                      (tptr (tfun [tint, tint, tint, tint] .Tvoid)))
                    (tfun [tint, tint, tint, tint] .Tvoid))
                  [(ci 64 tint),
                   (.Evar dense.id.«nauty:m» tint),
                   (.Evar dense.id.«nauty:n» tint),
                   (.Ebinop .Oadd (ci 29300 tint) (ci 0 tint) tint)]))
              .Sskip))
          tAlloc))))

abbrev tZero : statement :=
  (.Ssequence (sk zeroIf) tMain)

abbrev tSizes : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Ogt
          (tv dense.id.«m_arg»)
          (.Ebinop .Oadd (.Ebinop .Odiv (ci 2000000002 tint) (ci 64 tint) tint) (ci 1 tint) tint)
          tint)
        (.Ssequence
          (sk
            (.Sassign
              (.Efield
                (.Ederef
                  (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                  (.Tstruct dense.id.«_1024» noattr))
                dense.id.«errstatus»
                tint)
              (ci 2 tint)))
          (.Ssequence
            (sk
              (.Scall none
                (.Evar dense.id.«fprintf»
                  (.Tfunction
                    [(tptr (.Tstruct dense.id.«_IO_FILE» noattr)), (tptr tschar)]
                    tint
                    ⟨
                    (some (zOfInt 2))
                    ,
                    false
                    ,
                    false⟩))
                [(.Evar dense.id.«stderr» (tptr (.Tstruct dense.id.«_IO_FILE» noattr))),
                 (.Evar dense.id.«nauty:__stringlit_4» (tarray tschar 32)),
                 (.Ebinop .Oadd
                   (.Ebinop .Odiv (ci 2000000002 tint) (ci 64 tint) tint)
                   (ci 1 tint)
                   tint),
                 (tv dense.id.«m_arg»)]))
            (.Sreturn none)))
        .Sskip))
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Ogt
              (tv dense.id.«n_arg»)
              (.Ebinop .Osub (ci 2000000002 tint) (ci 2 tint) tint)
              tint)
            (.Sset (idOf 707) (ci 1 tint))
            (sk
              (.Sset
                (idOf 707)
                (.Ecast
                  (.Ebinop .Ogt
                    (tv dense.id.«n_arg»)
                    (.Ebinop .Omul (ci 64 tint) (tv dense.id.«m_arg») tint)
                    tint)
                  tbool)))))
        (.Sifthenelse
          (tv (idOf 707))
          (.Ssequence
            (sk
              (.Sassign
                (.Efield
                  (.Ederef
                    (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» noattr)))
                    (.Tstruct dense.id.«_1024» noattr))
                  dense.id.«errstatus»
                  tint)
                (ci 1 tint)))
            (.Ssequence
              (sk
                (.Scall none
                  (.Evar dense.id.«fprintf»
                    (.Tfunction
                      [(tptr (.Tstruct dense.id.«_IO_FILE» noattr)), (tptr tschar)]
                      tint
                      ⟨
                      (some (zOfInt 2))
                      ,
                      false
                      ,
                      false⟩))
                  [(.Evar dense.id.«stderr» (tptr (.Tstruct dense.id.«_IO_FILE» noattr))),
                   (.Evar dense.id.«nauty:__stringlit_5» (tarray tschar 42)),
                   (.Ebinop .Osub (ci 2000000002 tint) (ci 2 tint) tint),
                   (ci 64 tint),
                   (tv dense.id.«n_arg»)]))
              (.Sreturn none)))
          .Sskip))
      tZero))

abbrev body : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Oeq
          (.Efield
            (.Ederef
              (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
              (.Tstruct dense.id.«optionstruct» noattr))
            dense.id.«dispatch»
            (tptr (.Tstruct dense.id.«_1027» noattr)))
          (.Ecast (ci 0 tint) (tptr .Tvoid))
          tint)
        (.Ssequence
          (sk
            (.Scall none
              (.Evar dense.id.«fprintf»
                (.Tfunction
                  [(tptr (.Tstruct dense.id.«_IO_FILE» noattr)), (tptr tschar)]
                  tint
                  ⟨
                  (some (zOfInt 2))
                  ,
                  false
                  ,
                  false⟩))
              [(.Evar dense.id.«stderr» (tptr (.Tstruct dense.id.«_IO_FILE» noattr))),
               (.Evar dense.id.«nauty:__stringlit_1» (tarray tschar 32))]))
          (.Ssequence
            (sk
              (.Scall none
                (.Evar dense.id.«fprintf»
                  (.Tfunction
                    [(tptr (.Tstruct dense.id.«_IO_FILE» noattr)), (tptr tschar)]
                    tint
                    ⟨
                    (some (zOfInt 2))
                    ,
                    false
                    ,
                    false⟩))
                [(.Evar dense.id.«stderr» (tptr (.Tstruct dense.id.«_IO_FILE» noattr))),
                 (.Evar dense.id.«nauty:__stringlit_2» (tarray tschar 29))]))
            (sk (.Scall none (.Evar dense.id.«exit» (tfun [tint] .Tvoid)) [(ci 1 tint)]))))
        (sk
          (.Sassign
            (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
            (.Ederef
              (.Efield
                (.Ederef
                  (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                  (.Tstruct dense.id.«optionstruct» noattr))
                dense.id.«dispatch»
                (tptr (.Tstruct dense.id.«_1027» noattr)))
              (.Tstruct dense.id.«_1027» noattr))))))
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Efield
            (.Ederef
              (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
              (.Tstruct dense.id.«optionstruct» noattr))
            dense.id.«userrefproc»
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
                .Tvoid)))
          (sk
            (.Sassign
              (.Efield
                (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
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
                    .Tvoid)))
              (.Efield
                (.Ederef
                  (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                  (.Tstruct dense.id.«optionstruct» noattr))
                dense.id.«userrefproc»
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
                    .Tvoid)))))
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Efield
                  (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                  dense.id.«refine1»
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
                      .Tvoid)))
                (sk
                  (.Sset (idOf 703) (.Ecast (.Ebinop .Oeq (tv dense.id.«m_arg») (ci 1 tint) tint) tbool)))
                (.Sset (idOf 703) (ci 0 tint))))
            (.Sifthenelse
              (tv (idOf 703))
              (sk
                (.Sassign
                  (.Efield
                    (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
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
                        .Tvoid)))
                  (.Efield
                    (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                    dense.id.«refine1»
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
                        .Tvoid)))))
              .Sskip))))
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .Oeq
                    (.Efield
                      (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
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
                          .Tvoid)))
                    (.Ecast (ci 0 tint) (tptr .Tvoid))
                    tint)
                  (.Sset (idOf 704) (ci 1 tint))
                  (sk
                    (.Sset
                      (idOf 704)
                      (.Ecast
                        (.Ebinop .Oeq
                          (.Efield
                            (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                            dense.id.«updatecan»
                            (tptr
                              (tfun
                                [(tptr tulong), (tptr tulong), (tptr tint), tint, tint, tint]
                                .Tvoid)))
                          (.Ecast (ci 0 tint) (tptr .Tvoid))
                          tint)
                        tbool)))))
              (.Sifthenelse
                (tv (idOf 704))
                (.Sset (idOf 705) (ci 1 tint))
                (sk
                  (.Sset
                    (idOf 705)
                    (.Ecast
                      (.Ebinop .Oeq
                        (.Efield
                          (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
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
                              tint)))
                        (.Ecast (ci 0 tint) (tptr .Tvoid))
                        tint)
                      tbool)))))
            (.Sifthenelse
              (tv (idOf 705))
              (.Sset (idOf 706) (ci 1 tint))
              (sk
                (.Sset
                  (idOf 706)
                  (.Ecast
                    (.Ebinop .Oeq
                      (.Efield
                        (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                        dense.id.«cheapautom»
                        (tptr (tfun [(tptr tint), tint, tint, tint] tint)))
                      (.Ecast (ci 0 tint) (tptr .Tvoid))
                      tint)
                    tbool)))))
          (.Sifthenelse
            (tv (idOf 706))
            (.Ssequence
              (sk
                (.Scall none
                  (.Evar dense.id.«fprintf»
                    (.Tfunction
                      [(tptr (.Tstruct dense.id.«_IO_FILE» noattr)), (tptr tschar)]
                      tint
                      ⟨
                      (some (zOfInt 2))
                      ,
                      false
                      ,
                      false⟩))
                  [(.Evar dense.id.«stderr» (tptr (.Tstruct dense.id.«_IO_FILE» noattr))),
                   (.Evar dense.id.«nauty:__stringlit_3» (tarray tschar 24))]))
              (sk (.Scall none (.Evar dense.id.«exit» (tfun [tint] .Tvoid)) [(ci 1 tint)])))
            .Sskip))
        tSizes)))

kernel_rfl body_eq : dense.body.nauty = body

end Nauty

end NautyVerified.Proofs.Top

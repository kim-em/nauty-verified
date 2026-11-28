import NautyVerified.Proofs.Search.Node.Othernode
import NautyVerified.Proofs.Search.Node.NodePrologue

/-!
# `othernode0` after its prologue

`rest`: the statements of `othernode0` after the four of `nodePrologue`;
`body_rest`: the body is `nodePrologue rest`.
-/

namespace NautyVerified.Proofs.Search.Othernode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv)

/-- `othernode0` after `processnode` and the early return: the short prune, the
cheap test, the child loop and the final return. -/
abbrev tail : statement :=
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
                                            (some (.Ebinop .Osub (tv dense.id.«level») (ci 1 tint) tint)))))))

/-- `othernode0` after its prologue. -/
abbrev rest : statement :=
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
                                  tail))))))))))))

theorem body_rest : body = NautyVerified.Proofs.Search.nodePrologue rest := rfl

end NautyVerified.Proofs.Search.Othernode

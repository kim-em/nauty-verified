import NautyVerified.Proofs.Refine.Syntax

/-!
# `doref`, factored

The Clight of nauty's `doref` (nautil.c), cut by `scripts/factor_clight.py`
with `scripts/factor/doref.py`; `body_eq` pins it to `dense.body.doref`.
`refcall` is the call `(*refproc)(g, lab, ptn, level, numcells, invar, active,
code, M, n)`; `invBody` is the vertex-invariant branch, which is unreachable
when `invarproc` is `NULL`.
-/

namespace NautyVerified.Proofs.Doref

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv)
open NautyVerified.Proofs.Refine (tv pi)
open NautyVerified.Proofs.Alloc (dynalloc1)

abbrev refcall : statement :=
  (.Scall none
    (.Ederef
      (.Etempvar dense.id.«refproc»
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
        .Tvoid))
    [(pv dense.id.«g»),
     (pi dense.id.«lab»),
     (pi dense.id.«ptn»),
     (tv dense.id.«level»),
     (pi dense.id.«numcells»),
     (pi dense.id.«invar»),
     (pv dense.id.«active»),
     (pi dense.id.«code»),
     (tv dense.id.«m»),
     (tv dense.id.«n»)])

abbrev invBody : statement :=
  (.Ssequence
    (sk
      (.Scall none
        (.Ederef
          (.Etempvar dense.id.«invarproc»
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
            .Tvoid))
        [(pv dense.id.«g»),
         (pi dense.id.«lab»),
         (pi dense.id.«ptn»),
         (tv dense.id.«level»),
         (.Ederef (pi dense.id.«numcells») tint),
         (tv dense.id.«tvpos»),
         (pi dense.id.«invar»),
         (tv dense.id.«invararg»),
         (tv dense.id.«digraph»),
         (tv dense.id.«m»),
         (tv dense.id.«n»)]))
    (.Ssequence
      (.Ssequence
        (sk
          (.Sset dense.id.«es_»
            (.Ebinop .Oadd (.Ecast (pv dense.id.«active») (tptr tulong)) (tv dense.id.«m») (tptr tulong))))
        (.Sloop
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .Ogt (pv dense.id.«es_») (.Ecast (pv dense.id.«active») (tptr tulong)) tint)
                .Sskip
                .Sbreak))
            (.Ssequence
              (.Ssequence
                (sk
                  (.Sset
                    (idOf 709)
                    (.Ecast (.Ebinop .Osub (pv dense.id.«es_») (ci 1 tint) (tptr tulong)) (tptr tulong))))
                (.Sset dense.id.«es_» (pv (idOf 709))))
              (.Sassign (.Ederef (pv (idOf 709)) tulong) (ci 0 tint))))
          .Sskip))
      (.Ssequence
        (.Ssequence
          (sk (.Sset dense.id.«i» (tv dense.id.«n»)))
          (.Sloop
            (.Ssequence
              (.Ssequence
                (.Ssequence
                  (sk (.Sset (idOf 710) (.Ecast (.Ebinop .Osub (tv dense.id.«i») (ci 1 tint) tint) tint)))
                  (.Sset dense.id.«i» (tv (idOf 710))))
                (.Sifthenelse (.Ebinop .Oge (tv (idOf 710)) (ci 0 tint) tint) .Sskip .Sbreak))
              (sk
                (.Sassign
                  (.Ederef
                    (.Ebinop .Oadd (.Evar dense.id.«nautil:workperm» (tptr tint)) (tv dense.id.«i») (tptr tint))
                    tint)
                  (.Ederef
                    (.Ebinop .Oadd
                      (pi dense.id.«invar»)
                      (.Ederef (.Ebinop .Oadd (pi dense.id.«lab») (tv dense.id.«i») (tptr tint)) tint)
                      (tptr tint))
                    tint))))
            .Sskip))
        (.Ssequence
          (sk (.Sset dense.id.«nc» (.Ederef (pi dense.id.«numcells») tint)))
          (.Ssequence
            (.Ssequence
              (sk (.Sset dense.id.«cell1» (ci 0 tint)))
              (.Sloop
                (.Ssequence
                  (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«cell1») (tv dense.id.«n») tint) .Sskip .Sbreak))
                  (.Ssequence
                    (sk
                      (.Sset dense.id.«pw»
                        (.Ederef
                          (.Ebinop .Oadd
                            (.Evar dense.id.«nautil:workperm» (tptr tint))
                            (tv dense.id.«cell1»)
                            (tptr tint))
                          tint)))
                    (.Ssequence
                      (sk (.Sset dense.id.«same» (ci 1 tint)))
                      (.Ssequence
                        (.Ssequence
                          (sk (.Sset dense.id.«cell2» (tv dense.id.«cell1»)))
                          (.Sloop
                            (.Ssequence
                              (sk
                                (.Sifthenelse
                                  (.Ebinop .Ogt
                                    (.Ederef
                                      (.Ebinop .Oadd (pi dense.id.«ptn») (tv dense.id.«cell2») (tptr tint))
                                      tint)
                                    (tv dense.id.«level»)
                                    tint)
                                  .Sskip
                                  .Sbreak))
                              (sk
                                (.Sifthenelse
                                  (.Ebinop .One
                                    (.Ederef
                                      (.Ebinop .Oadd
                                        (.Evar dense.id.«nautil:workperm» (tptr tint))
                                        (.Ebinop .Oadd (tv dense.id.«cell2») (ci 1 tint) tint)
                                        (tptr tint))
                                      tint)
                                    (tv dense.id.«pw»)
                                    tint)
                                  (sk (.Sset dense.id.«same» (ci 0 tint)))
                                  .Sskip)))
                            (sk (.Sset dense.id.«cell2» (.Ebinop .Oadd (tv dense.id.«cell2») (ci 1 tint) tint)))))
                        (.Ssequence
                          (sk (.Sifthenelse (tv dense.id.«same») .Scontinue .Sskip))
                          (.Ssequence
                            (sk
                              (.Scall none
                                (.Evar dense.id.«nautil:sortparallel»
                                  (tfun [(tptr tint), (tptr tint), tint] .Tvoid))
                                [(.Ebinop .Oadd
                                   (.Evar dense.id.«nautil:workperm» (tptr tint))
                                   (tv dense.id.«cell1»)
                                   (tptr tint)),
                                 (.Ebinop .Oadd (pi dense.id.«lab») (tv dense.id.«cell1») (tptr tint)),
                                 (.Ebinop .Oadd
                                   (.Ebinop .Osub (tv dense.id.«cell2») (tv dense.id.«cell1») tint)
                                   (ci 1 tint)
                                   tint)]))
                            (.Ssequence
                              (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«cell1») (ci 1 tint) tint)))
                              (.Sloop
                                (.Ssequence
                                  (sk
                                    (.Sifthenelse
                                      (.Ebinop .Ole (tv dense.id.«i») (tv dense.id.«cell2») tint)
                                      .Sskip
                                      .Sbreak))
                                  (sk
                                    (.Sifthenelse
                                      (.Ebinop .One
                                        (.Ederef
                                          (.Ebinop .Oadd
                                            (.Evar dense.id.«nautil:workperm» (tptr tint))
                                            (tv dense.id.«i»)
                                            (tptr tint))
                                          tint)
                                        (.Ederef
                                          (.Ebinop .Oadd
                                            (.Evar dense.id.«nautil:workperm» (tptr tint))
                                            (.Ebinop .Osub (tv dense.id.«i») (ci 1 tint) tint)
                                            (tptr tint))
                                          tint)
                                        tint)
                                      (.Ssequence
                                        (sk
                                          (.Sassign
                                            (.Ederef
                                              (.Ebinop .Oadd
                                                (pi dense.id.«ptn»)
                                                (.Ebinop .Osub (tv dense.id.«i») (ci 1 tint) tint)
                                                (tptr tint))
                                              tint)
                                            (tv dense.id.«level»)))
                                        (.Ssequence
                                          (sk
                                            (.Sassign
                                              (.Ederef (pi dense.id.«numcells») tint)
                                              (.Ebinop .Oadd
                                                (.Ederef (pi dense.id.«numcells») tint)
                                                (ci 1 tint)
                                                tint)))
                                          (sk
                                            (.Sassign
                                              (.Ederef
                                                (.Ebinop .Oadd
                                                  (pv dense.id.«active»)
                                                  (.Ebinop .Oshr (tv dense.id.«i») (ci 6 tint) tint)
                                                  (tptr tulong))
                                                tulong)
                                              (.Ebinop .Oor
                                                (.Ederef
                                                  (.Ebinop .Oadd
                                                    (pv dense.id.«active»)
                                                    (.Ebinop .Oshr (tv dense.id.«i») (ci 6 tint) tint)
                                                    (tptr tulong))
                                                  tulong)
                                                (.Ederef
                                                  (.Ebinop .Oadd
                                                    (.Evar dense.id.«nautil:bit» (tarray tulong 64))
                                                    (.Ebinop .Oand (tv dense.id.«i») (ci 63 tint) tint)
                                                    (tptr tulong))
                                                  tulong)
                                                tulong)))))
                                      .Sskip)))
                                (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint)))))))))))
                (sk (.Sset dense.id.«cell1» (.Ebinop .Oadd (tv dense.id.«cell2») (ci 1 tint) tint)))))
            (sk
              (.Sifthenelse
                (.Ebinop .Ogt (.Ederef (pi dense.id.«numcells») tint) (tv dense.id.«nc») tint)
                (.Ssequence
                  (sk (.Sassign (.Ederef (pi dense.id.«qinvar») tint) (ci 2 tint)))
                  (.Ssequence
                    (sk (.Sset dense.id.«longcode» (.Ecast (.Ederef (pi dense.id.«code») tint) tlong)))
                    (.Ssequence
                      (sk
                        (.Scall none
                          (.Ederef
                            (.Etempvar dense.id.«refproc»
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
                              .Tvoid))
                          [(pv dense.id.«g»),
                           (pi dense.id.«lab»),
                           (pi dense.id.«ptn»),
                           (tv dense.id.«level»),
                           (pi dense.id.«numcells»),
                           (pi dense.id.«invar»),
                           (pv dense.id.«active»),
                           (pi dense.id.«code»),
                           (tv dense.id.«m»),
                           (tv dense.id.«n»)]))
                      (.Ssequence
                        (sk
                          (.Sset dense.id.«longcode»
                            (.Ebinop .Oand
                              (.Ebinop .Oadd
                                (.Ebinop .Oxor
                                  (.Etempvar dense.id.«longcode» tlong)
                                  (ci 27421 tint)
                                  tlong)
                                (.Ederef (pi dense.id.«code») tint)
                                tlong)
                              (ci 32767 tint)
                              tlong)))
                        (sk
                          (.Sassign
                            (.Ederef (pi dense.id.«code») tint)
                            (.Ecast
                              (.Ebinop .Omod (.Etempvar dense.id.«longcode» tlong) (ci 32767 tint) tlong)
                              tint)))))))
                (sk (.Sassign (.Ederef (pi dense.id.«qinvar») tint) (ci 1 tint))))))))))

abbrev body : statement :=
  (.Ssequence
    (dynalloc1 dense.id.«nautil:workperm_sz» dense.id.«nautil:workperm» tint
      (tv dense.id.«n»)
      (idOf 703)
      (idOf 704)
      dense.id.«nautil:__stringlit_4»
      6)
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk
              (.Scall
                (some (idOf 705))
                (.Evar dense.id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
                [(pv dense.id.«active»), (tv dense.id.«m»), (.Eunop .Oneg (ci 1 tint) tint)]))
            (.Sset (idOf 706) (.Ecast (tv (idOf 705)) tint)))
          (.Sset dense.id.«tvpos» (tv (idOf 706))))
        (.Sifthenelse
          (.Ebinop .Olt (tv (idOf 706)) (ci 0 tint) tint)
          (sk (.Sset dense.id.«tvpos» (ci 0 tint)))
          .Sskip))
      (.Ssequence
        (sk refcall)
        (.Ssequence
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .Olt (tv dense.id.«mininvarlev») (ci 0 tint) tint)
                (sk (.Sset (idOf 707) (.Ecast (.Eunop .Oneg (tv dense.id.«mininvarlev») tint) tint)))
                (sk (.Sset (idOf 707) (.Ecast (tv dense.id.«mininvarlev») tint)))))
            (.Sset dense.id.«minlev» (tv (idOf 707))))
          (.Ssequence
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .Olt (tv dense.id.«maxinvarlev») (ci 0 tint) tint)
                  (sk (.Sset (idOf 708) (.Ecast (.Eunop .Oneg (tv dense.id.«maxinvarlev») tint) tint)))
                  (sk (.Sset (idOf 708) (.Ecast (tv dense.id.«maxinvarlev») tint)))))
              (.Sset dense.id.«maxlev» (tv (idOf 708))))
            (.Ssequence
              (.Ssequence
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Ebinop .One
                        (.Etempvar dense.id.«invarproc»
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
                        (.Ecast (ci 0 tint) (tptr .Tvoid))
                        tint)
                      (sk
                        (.Sset
                          (idOf 711)
                          (.Ecast
                            (.Ebinop .Olt (.Ederef (pi dense.id.«numcells») tint) (tv dense.id.«n») tint)
                            tbool)))
                      (.Sset (idOf 711) (ci 0 tint))))
                  (.Sifthenelse
                    (tv (idOf 711))
                    (sk
                      (.Sset
                        (idOf 712)
                        (.Ecast (.Ebinop .Oge (tv dense.id.«level») (tv dense.id.«minlev») tint) tbool)))
                    (.Sset (idOf 712) (ci 0 tint))))
                (.Sifthenelse
                  (tv (idOf 712))
                  (sk
                    (.Sset
                      (idOf 713)
                      (.Ecast (.Ebinop .Ole (tv dense.id.«level») (tv dense.id.«maxlev») tint) tbool)))
                  (.Sset (idOf 713) (ci 0 tint))))
              (.Sifthenelse
                (tv (idOf 713))
                invBody
                (sk (.Sassign (.Ederef (pi dense.id.«qinvar») tint) (ci 0 tint))))))))))

kernel_rfl body_eq : dense.body.doref = body

end NautyVerified.Proofs.Doref

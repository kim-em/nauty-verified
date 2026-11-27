import NautyVerified.Proofs.Harness.IO
import NautyVerified.Proofs.Set.Syntax

/-!
# `dense_main`'s `main`, factored

The Clight of the harness's `main`, cut by `scripts/factor_clight.py` with
`scripts/factor/main.py`; `body_eq` pins it to `dense.body.main`. The tails
`tInput`, `tPart`, `tOpts`, `tCall`, `tOut`, `tStats` start the input loops,
the partition, the option settings, the `densenauty` call, the output and the
statistics; the loops are `colourLoop`, `emptyG` (EMPTYGRAPH), `edgeLoop`
(ADDONEEDGE), `cellLoop`, `endLoop`, `labOut`, `orbOut`, `cgOut`.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)

abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint
abbrev pi (x : Common.AST.ident) : expr := .Etempvar x (tptr tint)
abbrev pl (x : Common.AST.ident) : expr := .Etempvar x (tptr tulong)
abbrev ix (p : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (pi p) a (tptr tint)) tint
/-- `t = nv_read()`. -/
abbrev rd (t : Common.AST.ident) : statement :=
  .Scall (some t) (.Evar dense.id.nv_read (tfun [] tlong)) []
/-- `nv_write(e)`. -/
abbrev wr (e : expr) : statement :=
  .Scall none (.Evar dense.id.nv_write (tfun [tlong] .Tvoid)) [e]
/-- `t = nauty_zalloc(e)`. -/
abbrev za (t : Common.AST.ident) (e : expr) : statement :=
  .Scall (some t) (.Evar dense.id.nauty_zalloc (tfun [tulong] (tptr .Tvoid))) [e]

abbrev colourLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«i») (tv dense.id.«n») tint) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence
          (sk (rd (idOf 710)))
          (.Sassign (ix dense.id.«colour» (tv dense.id.«i»)) (.Ecast (.Etempvar (idOf 710) tlong) tint)))
        (sk
          (.Sifthenelse
            (.Ebinop .Ogt (ix dense.id.«colour» (tv dense.id.«i»)) (tv dense.id.«maxc») tint)
            (sk (.Sset dense.id.«maxc» (ix dense.id.«colour» (tv dense.id.«i»))))
            .Sskip))))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev emptyG : statement :=
  (.Ssequence
    (sk
      (.Sset dense.id.«es_»
        (.Ebinop .Oadd
          (.Ecast (pl dense.id.«g») (tptr tulong))
          (.Ebinop .Omul (tv dense.id.«m») (.Ecast (tv dense.id.«n») tulong) tulong)
          (tptr tulong))))
    (.Sloop
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Ogt (pl dense.id.«es_») (.Ecast (pl dense.id.«g») (tptr tulong)) tint)
            .Sskip
            .Sbreak))
        (.Ssequence
          (.Ssequence
            (sk
              (.Sset
                (idOf 712)
                (.Ecast (.Ebinop .Osub (pl dense.id.«es_») (ci 1 tint) (tptr tulong)) (tptr tulong))))
            (.Sset dense.id.«es_» (pl (idOf 712))))
          (.Sassign (.Ederef (pl (idOf 712)) tulong) (ci 0 tint))))
      .Sskip))

abbrev edgeLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«i») (tv dense.id.«ne») tint) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence (sk (rd (idOf 713))) (.Sset dense.id.«a» (.Ecast (.Etempvar (idOf 713) tlong) tint)))
        (.Ssequence
          (.Ssequence
            (sk (rd (idOf 714)))
            (.Sset dense.id.«b» (.Ecast (.Etempvar (idOf 714) tlong) tint)))
          (.Ssequence
            (sk
              (.Sassign
                (.Ederef
                  (.Ebinop .Oadd
                    (.Ebinop .Oadd
                      (.Ecast (pl dense.id.«g») (tptr tulong))
                      (.Ebinop .Omul (tv dense.id.«m») (.Ecast (tv dense.id.«a») tulong) tulong)
                      (tptr tulong))
                    (.Ebinop .Oshr (tv dense.id.«b») (ci 6 tint) tint)
                    (tptr tulong))
                  tulong)
                (.Ebinop .Oor
                  (.Ederef
                    (.Ebinop .Oadd
                      (.Ebinop .Oadd
                        (.Ecast (pl dense.id.«g») (tptr tulong))
                        (.Ebinop .Omul (tv dense.id.«m») (.Ecast (tv dense.id.«a») tulong) tulong)
                        (tptr tulong))
                      (.Ebinop .Oshr (tv dense.id.«b») (ci 6 tint) tint)
                      (tptr tulong))
                    tulong)
                  (.Ederef
                    (.Ebinop .Oadd
                      (.Evar dense.id.«dense_main:bit» (tarray tulong 64))
                      (.Ebinop .Oand (tv dense.id.«b») (ci 63 tint) tint)
                      (tptr tulong))
                    tulong)
                  tulong)))
            (sk
              (.Sassign
                (.Ederef
                  (.Ebinop .Oadd
                    (.Ebinop .Oadd
                      (.Ecast (pl dense.id.«g») (tptr tulong))
                      (.Ebinop .Omul (tv dense.id.«m») (.Ecast (tv dense.id.«b») tulong) tulong)
                      (tptr tulong))
                    (.Ebinop .Oshr (tv dense.id.«a») (ci 6 tint) tint)
                    (tptr tulong))
                  tulong)
                (.Ebinop .Oor
                  (.Ederef
                    (.Ebinop .Oadd
                      (.Ebinop .Oadd
                        (.Ecast (pl dense.id.«g») (tptr tulong))
                        (.Ebinop .Omul (tv dense.id.«m») (.Ecast (tv dense.id.«b») tulong) tulong)
                        (tptr tulong))
                      (.Ebinop .Oshr (tv dense.id.«a») (ci 6 tint) tint)
                      (tptr tulong))
                    tulong)
                  (.Ederef
                    (.Ebinop .Oadd
                      (.Evar dense.id.«dense_main:bit» (tarray tulong 64))
                      (.Ebinop .Oand (tv dense.id.«a») (ci 63 tint) tint)
                      (tptr tulong))
                    tulong)
                  tulong)))))))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev cellLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«c») (tv dense.id.«maxc») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sset dense.id.«j» (ci 0 tint)))
        (.Sloop
          (.Ssequence
            (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«j») (tv dense.id.«n») tint) .Sskip .Sbreak))
            (sk
              (.Sifthenelse
                (.Ebinop .Oeq (ix dense.id.«colour» (tv dense.id.«j»)) (tv dense.id.«c») tint)
                (.Ssequence
                  (sk (.Sassign (ix dense.id.«lab» (tv dense.id.«pos»)) (tv dense.id.«j»)))
                  (.Ssequence
                    (sk (.Sassign (ix dense.id.«ptn» (tv dense.id.«pos»)) (ci 1 tint)))
                    (sk (.Sset dense.id.«pos» (.Ebinop .Oadd (tv dense.id.«pos») (ci 1 tint) tint)))))
                .Sskip)))
          (sk (.Sset dense.id.«j» (.Ebinop .Oadd (tv dense.id.«j») (ci 1 tint) tint))))))
    (sk (.Sset dense.id.«c» (.Ebinop .Oadd (tv dense.id.«c») (ci 1 tint) tint))))

abbrev endLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«i») (tv dense.id.«n») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Oeq (tv dense.id.«i») (.Ebinop .Osub (tv dense.id.«n») (ci 1 tint) tint) tint)
            (.Sset (idOf 715) (ci 1 tint))
            (sk
              (.Sset
                (idOf 715)
                (.Ecast
                  (.Ebinop .One
                    (ix dense.id.«colour» (ix dense.id.«lab» (tv dense.id.«i»)))
                    (ix dense.id.«colour» (ix dense.id.«lab» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint)))
                    tint)
                  tbool)))))
        (.Sifthenelse (tv (idOf 715)) (sk (.Sassign (ix dense.id.«ptn» (tv dense.id.«i»)) (ci 0 tint))) .Sskip)))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev labOut : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«i») (tv dense.id.«n») tint) .Sskip .Sbreak))
      (sk (wr (ix dense.id.«lab» (tv dense.id.«i»)))))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev orbOut : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«i») (tv dense.id.«n») tint) .Sskip .Sbreak))
      (sk (wr (ix dense.id.«orbits» (tv dense.id.«i»)))))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev cgOut : statement :=
  (.Sloop
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Olt (tv dense.id.«i») (.Ebinop .Omul (tv dense.id.«m») (tv dense.id.«n») tint) tint)
          .Sskip
          .Sbreak))
      (sk
        (wr
          (.Ecast (.Ederef (.Ebinop .Oadd (pl dense.id.«canong») (tv dense.id.«i») (tptr tulong)) tulong) tlong))))
    (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

abbrev tStats : statement :=
  (.Ssequence
    (sk (wr (ci 5 tint)))
    (.Ssequence
      (sk (wr (.Efield (.Evar dense.id.«stats» (Tstruct dense.id.«_1024» noattr)) dense.id.«numorbits» tint)))
      (.Ssequence
        (sk (wr (.Efield (.Evar dense.id.«stats» (Tstruct dense.id.«_1024» noattr)) dense.id.«numgenerators» tint)))
        (.Ssequence
          (sk
            (wr
              (.Ecast
                (.Efield (.Evar dense.id.«stats» (Tstruct dense.id.«_1024» noattr)) dense.id.«numnodes» tulong)
                tlong)))
          (.Ssequence
            (sk
              (wr
                (.Ecast
                  (.Efield (.Evar dense.id.«stats» (Tstruct dense.id.«_1024» noattr)) dense.id.«numbadleaves» tulong)
                  tlong)))
            (.Ssequence
              (sk (wr (.Efield (.Evar dense.id.«stats» (Tstruct dense.id.«_1024» noattr)) dense.id.«maxlevel» tint)))
              (.Ssequence
                (sk
                  (wr
                    (.Ecast
                      (.Efield (.Evar dense.id.«stats» (Tstruct dense.id.«_1024» noattr)) dense.id.«tctotal» tulong)
                      tlong)))
                (.Ssequence
                  (sk
                    (wr
                      (.Ecast
                        (.Efield
                          (.Evar dense.id.«stats» (Tstruct dense.id.«_1024» noattr))
                          dense.id.«canupdates»
                          tulong)
                        tlong)))
                  (.Ssequence
                    (sk
                      (wr
                        (.Efield (.Evar dense.id.«stats» (Tstruct dense.id.«_1024» noattr)) dense.id.«errstatus» tint)))
                    (sk (.Sreturn (some (ci 0 tint)))))))))))))

abbrev tOut : statement :=
  (.Ssequence
    (sk (wr (ci 2 tint)))
    (.Ssequence
      (.Ssequence (sk (.Sset dense.id.«i» (ci 0 tint))) labOut)
      (.Ssequence
        (sk (wr (ci 3 tint)))
        (.Ssequence
          (.Ssequence (sk (.Sset dense.id.«i» (ci 0 tint))) orbOut)
          (.Ssequence
            (sk (wr (ci 4 tint)))
            (.Ssequence (.Ssequence (sk (.Sset dense.id.«i» (ci 0 tint))) cgOut) tStats))))))

abbrev tCall : statement :=
  (.Ssequence
    (sk
      (.Scall none
        (.Evar dense.id.«densenauty»
          (tfun
            [(tptr tulong),
             (tptr tint),
             (tptr tint),
             (tptr tint),
             (tptr (Tstruct dense.id.«optionstruct» noattr)),
             (tptr (Tstruct dense.id.«_1024» noattr)),
             tint,
             tint,
             (tptr tulong)]
            .Tvoid))
        [(pl dense.id.«g»),
         (pi dense.id.«lab»),
         (pi dense.id.«ptn»),
         (pi dense.id.«orbits»),
         (.Eaddrof
           (.Evar dense.id.«dense_main:options» (Tstruct dense.id.«optionstruct» noattr))
           (tptr (Tstruct dense.id.«optionstruct» noattr))),
         (.Eaddrof
           (.Evar dense.id.«stats» (Tstruct dense.id.«_1024» noattr))
           (tptr (Tstruct dense.id.«_1024» noattr))),
         (tv dense.id.«m»),
         (tv dense.id.«n»),
         (pl dense.id.«canong»)]))
    tOut)

abbrev tOpts : statement :=
  (.Ssequence
    (sk
      (.Sassign
        (.Efield
          (.Evar dense.id.«dense_main:options» (Tstruct dense.id.«optionstruct» noattr))
          dense.id.«getcanon»
          tint)
        (ci 1 tint)))
    (.Ssequence
      (sk
        (.Sassign
          (.Efield
            (.Evar dense.id.«dense_main:options» (Tstruct dense.id.«optionstruct» noattr))
            dense.id.«defaultptn»
            tint)
          (ci 0 tint)))
      (.Ssequence
        (sk
          (.Sassign
            (.Efield
              (.Evar dense.id.«dense_main:options» (Tstruct dense.id.«optionstruct» noattr))
              dense.id.«userautomproc»
              (tptr (tfun [tint, (tptr tint), (tptr tint), tint, tint, tint] .Tvoid)))
            (.Evar dense.id.«dense_main:emit_generator»
              (tfun [tint, (tptr tint), (tptr tint), tint, tint, tint] .Tvoid))))
        (.Ssequence
          (sk
            (.Sassign
              (.Efield
                (.Evar dense.id.«dense_main:options» (Tstruct dense.id.«optionstruct» noattr))
                dense.id.«outfile»
                (tptr (Tstruct dense.id.«_IO_FILE» noattr)))
              (.Ecast
                (.Eaddrof (.Evar dense.id.«dense_main:dummyfile» tschar) (tptr tschar))
                (tptr (Tstruct dense.id.«_IO_FILE» noattr)))))
          tCall))))

abbrev tPart : statement :=
  (.Ssequence
    (sk (.Sset dense.id.«pos» (ci 0 tint)))
    (.Ssequence
      (.Ssequence (sk (.Sset dense.id.«c» (ci 0 tint))) cellLoop)
      (.Ssequence (.Ssequence (sk (.Sset dense.id.«i» (ci 0 tint))) endLoop) tOpts)))

abbrev tInput : statement :=
  (.Ssequence
    (sk (.Sset dense.id.«maxc» (ci 0 tint)))
    (.Ssequence
      (.Ssequence (sk (.Sset dense.id.«i» (ci 0 tint))) colourLoop)
      (.Ssequence
        (.Ssequence (sk (rd (idOf 711))) (.Sset dense.id.«ne» (.Ecast (.Etempvar (idOf 711) tlong) tint)))
        (.Ssequence emptyG (.Ssequence (.Ssequence (sk (.Sset dense.id.«i» (ci 0 tint))) edgeLoop) tPart)))))

abbrev body : statement :=
  (.Ssequence
    (.Ssequence
      (.Ssequence (sk (rd (idOf 703))) (.Sset dense.id.«n» (.Ecast (.Etempvar (idOf 703) tlong) tint)))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Ole (tv dense.id.«n») (ci 0 tint) tint)
            (.Ssequence
              (sk (wr (.Eunop .Oneg (ci 1 tint) tint)))
              (sk (.Sreturn (some (ci 0 tint)))))
            .Sskip))
        (.Ssequence
          (sk
            (.Sset dense.id.«m»
              (.Ebinop .Oadd
                (.Ebinop .Oshr (.Ebinop .Osub (tv dense.id.«n») (ci 1 tint) tint) (ci 6 tint) tint)
                (ci 1 tint)
                tint)))
          (.Ssequence
            (.Ssequence
              (sk
                (za
                  (idOf 704)
                  (.Ebinop .Omul (.Ecast (tv dense.id.«n») tulong) (.Esizeof tint tulong) tulong)))
              (.Sset dense.id.«colour» (.Etempvar (idOf 704) (tptr .Tvoid))))
            (.Ssequence
              (.Ssequence
                (sk
                  (za
                    (idOf 705)
                    (.Ebinop .Omul (.Ecast (tv dense.id.«n») tulong) (.Esizeof tint tulong) tulong)))
                (.Sset dense.id.«lab» (.Etempvar (idOf 705) (tptr .Tvoid))))
              (.Ssequence
                (.Ssequence
                  (sk
                    (za
                      (idOf 706)
                      (.Ebinop .Omul (.Ecast (tv dense.id.«n») tulong) (.Esizeof tint tulong) tulong)))
                  (.Sset dense.id.«ptn» (.Etempvar (idOf 706) (tptr .Tvoid))))
                (.Ssequence
                  (.Ssequence
                    (sk
                      (za
                        (idOf 707)
                        (.Ebinop .Omul (.Ecast (tv dense.id.«n») tulong) (.Esizeof tint tulong) tulong)))
                    (.Sset dense.id.«orbits» (.Etempvar (idOf 707) (tptr .Tvoid))))
                  (.Ssequence
                    (.Ssequence
                      (sk
                        (za
                          (idOf 708)
                          (.Ebinop .Omul
                            (.Ebinop .Omul
                              (.Ecast (tv dense.id.«m») tulong)
                              (.Ecast (tv dense.id.«n») tulong)
                              tulong)
                            (.Esizeof tulong tulong)
                            tulong)))
                      (.Sset dense.id.«g» (.Etempvar (idOf 708) (tptr .Tvoid))))
                    (.Ssequence
                      (.Ssequence
                        (sk
                          (za
                            (idOf 709)
                            (.Ebinop .Omul
                              (.Ebinop .Omul
                                (.Ecast (tv dense.id.«m») tulong)
                                (.Ecast (tv dense.id.«n») tulong)
                                tulong)
                              (.Esizeof tulong tulong)
                              tulong)))
                        (.Sset dense.id.«canong» (.Etempvar (idOf 709) (tptr .Tvoid))))
                      tInput)))))))))
    (sk (.Sreturn (some (ci 0 tint)))))

kernel_rfl body_eq : dense.body.main = body

end NautyVerified.Proofs.Harness

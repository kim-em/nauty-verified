import NautyVerified.Proofs.Refine.Syntax

/-!
# `densenauty`, factored

The Clight of naugraph.c's `densenauty`, cut by `scripts/factor_clight.py`
with `scripts/factor/densenauty.py`; `body_eq` pins it to
`dense.body.densenauty`. `scanLoop` looks for a loop (`ISELEMENT(GRAPHROW(g,
i, m), i)`), which makes the graph a digraph; `nautyCall` is the call of
`nauty` with the workspace `dnwork` of `2 * 500 * m` setwords.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open CompCert4Lean.Foundation.Numbers.Rocq.Coq (zOfInt)
open NautyVerified.Proofs.Set (sk pv)
open NautyVerified.Proofs.Refine (tv pi)
open NautyVerified.Proofs.Alloc (dynalloc1)

namespace Densenauty

abbrev scanLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv dense.id.«i») (tv dense.id.«n») tint) .Sskip .Sbreak))
      (sk
        (.Sifthenelse
          (.Ebinop .One
            (.Ebinop .Oand
              (.Ederef
                (.Ebinop .Oadd
                  (pv dense.id.«gi»)
                  (.Ebinop .Oshr (tv dense.id.«i») (ci 6 tint) tint)
                  (tptr tulong))
                tulong)
              (.Ederef
                (.Ebinop .Oadd
                  (.Evar dense.id.«naugraph:bit» (tarray tulong 64))
                  (.Ebinop .Oand (tv dense.id.«i») (ci 63 tint) tint)
                  (tptr tulong))
                tulong)
              tulong)
            (ci 0 tint)
            tint)
          .Sbreak
          .Sskip)))
    (.Ssequence
      (sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint)))
      (.Sset dense.id.«gi» (.Ebinop .Oadd (pv dense.id.«gi») (tv dense.id.«m») (tptr tulong)))))

abbrev nautyCall : statement :=
  (.Scall none
    (.Evar dense.id.«nauty»
      (tfun
        [(tptr tulong),
         (tptr tint),
         (tptr tint),
         (tptr tulong),
         (tptr tint),
         (tptr (.Tstruct dense.id.«optionstruct» noattr)),
         (tptr (.Tstruct dense.id.«_1024» noattr)),
         (tptr tulong),
         tint,
         tint,
         tint,
         (tptr tulong)]
        .Tvoid))
    [(pv dense.id.«g»),
     (pi dense.id.«lab»),
     (pi dense.id.«ptn»),
     (.Ecast (ci 0 tint) (tptr .Tvoid)),
     (pi dense.id.«orbits»),
     (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr))),
     (.Etempvar dense.id.«stats» (tptr (.Tstruct dense.id.«_1024» noattr))),
     (.Evar dense.id.«naugraph:dnwork» (tptr tulong)),
     (.Ebinop .Omul (.Ebinop .Omul (ci 2 tint) (ci 500 tint) tint) (tv dense.id.«m») tint),
     (tv dense.id.«m»),
     (tv dense.id.«n»),
     (pv dense.id.«h»)])

abbrev body : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .One
          (.Efield
            (.Ederef
              (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
              (.Tstruct dense.id.«optionstruct» noattr))
            dense.id.«dispatch»
            (tptr (.Tstruct dense.id.«_1027» noattr)))
          (.Eaddrof
            (.Evar dense.id.«dispatch_graph» (.Tstruct dense.id.«_1027» noattr))
            (tptr (.Tstruct dense.id.«_1027» noattr)))
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
               (.Evar dense.id.«naugraph:__stringlit_6» (tarray tschar 50))]))
          (sk (.Scall none (.Evar dense.id.«exit» (tfun [tint] .Tvoid)) [(ci 1 tint)])))
        .Sskip))
    (.Ssequence
      (sk
        (.Sset dense.id.«digraph»
          (.Efield
            (.Ederef
              (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
              (.Tstruct dense.id.«optionstruct» noattr))
            dense.id.«digraph»
            tint)))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Eunop .Onotbool (tv dense.id.«digraph») tint)
            (.Ssequence
              (.Ssequence
                (.Ssequence (sk (.Sset dense.id.«i» (ci 0 tint))) (.Sset dense.id.«gi» (pv dense.id.«g»)))
                scanLoop)
              (sk
                (.Sifthenelse
                  (.Ebinop .Olt (tv dense.id.«i») (tv dense.id.«n») tint)
                  (sk
                    (.Sassign
                      (.Efield
                        (.Ederef
                          (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                          (.Tstruct dense.id.«optionstruct» noattr))
                        dense.id.«digraph»
                        tint)
                      (ci 1 tint)))
                  .Sskip)))
            .Sskip))
        (.Ssequence
          (dynalloc1 dense.id.«naugraph:dnwork_sz» dense.id.«naugraph:dnwork» tulong
            (.Ebinop .Omul (.Ebinop .Omul (ci 2 tint) (ci 500 tint) tint) (tv dense.id.«m») tint)
            (idOf 703)
            (idOf 704)
            dense.id.«naugraph:__stringlit_7»
            18)
          (.Ssequence
            (sk nautyCall)
            (sk
              (.Sassign
                (.Efield
                  (.Ederef
                    (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr)))
                    (.Tstruct dense.id.«optionstruct» noattr))
                  dense.id.«digraph»
                  tint)
                (tv dense.id.«digraph»))))))))

kernel_rfl body_eq : dense.body.densenauty = body

end Densenauty

end NautyVerified.Proofs.Top

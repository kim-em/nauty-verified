import NautyVerified.Proofs.Search.Ops

/-!
# `firstterminal`, factored

The Clight of nauty.c's `firstterminal`, cut by `scripts/factor_clight.py`
with `scripts/factor/firstterminal.py`; `body_eq` pins it.
-/

namespace NautyVerified.Proofs.Search.Firstterminal

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Logic
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv ix)
open NautyVerified.Proofs.Alloc (gat)
open NautyVerified.Proofs.Search (gats statsF)

abbrev body : statement :=
  (.Ssequence
    (sk (.Sassign (statsF dense.id.«maxlevel» tint) (tv dense.id.«level»)))
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (sk (.Sset (idOf 703) (.Ecast (tv dense.id.«level») tint)))
              (.Sassign (.Evar dense.id.«nauty:eqlev_first» tint) (tv (idOf 703))))
            (.Sset (idOf 704) (.Ecast (tv (idOf 703)) tint)))
          (.Sassign (.Evar dense.id.«nauty:allsamelevel» tint) (tv (idOf 704))))
        (.Sassign (.Evar dense.id.«nauty:gca_first» tint) (tv (idOf 704))))
      (.Ssequence
        (sk
          (.Sassign
            (gats dense.id.«nauty:firstcode» (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint))
            (ci 32767 tint)))
        (.Ssequence
          (sk
            (.Sassign
              (gat dense.id.«nauty:firsttc» (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint))
              (.Eunop .Oneg (ci 1 tint) tint)))
          (.Ssequence
            (forLoopC dense.id.«i»
              (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
              (sk (.Sassign (gat dense.id.«nauty:firstlab» (tv dense.id.«i»)) (ix dense.id.«lab» (tv dense.id.«i»)))))
            (sk
              (.Sifthenelse
                (.Evar dense.id.«nauty:getcanon» tint)
                (.Ssequence
                  (.Ssequence
                    (.Ssequence
                      (.Ssequence
                        (.Ssequence
                          (sk (.Sset (idOf 705) (.Ecast (tv dense.id.«level») tint)))
                          (.Sassign (.Evar dense.id.«nauty:gca_canon» tint) (tv (idOf 705))))
                        (.Sset (idOf 706) (.Ecast (tv (idOf 705)) tint)))
                      (.Sassign (.Evar dense.id.«nauty:eqlev_canon» tint) (tv (idOf 706))))
                    (.Sassign (.Evar dense.id.«nauty:canonlevel» tint) (tv (idOf 706))))
                  (.Ssequence
                    (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint)))
                    (.Ssequence
                      (sk (.Sassign (.Evar dense.id.«nauty:samerows» tint) (ci 0 tint)))
                      (.Ssequence
                        (forLoopC dense.id.«i»
                          (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
                          (sk
                            (.Sassign
                              (gat dense.id.«nauty:canonlab» (tv dense.id.«i»))
                              (ix dense.id.«lab» (tv dense.id.«i»)))))
                        (.Ssequence
                          (forLoopC dense.id.«i»
                            (.Ebinop .Ole (tv dense.id.«i») (tv dense.id.«level») tint)
                            (sk
                              (.Sassign
                                (gats dense.id.«nauty:canoncode» (tv dense.id.«i»))
                                (gats dense.id.«nauty:firstcode» (tv dense.id.«i»)))))
                          (.Ssequence
                            (sk
                              (.Sassign
                                (gats dense.id.«nauty:canoncode»
                                  (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint))
                                (ci 32767 tint)))
                            (sk (.Sassign (statsF dense.id.«canupdates» tulong) (ci 1 tint)))))))))
                .Sskip)))))))


kernel_rfl body_eq : dense.body.«nauty:firstterminal» = body

end NautyVerified.Proofs.Search.Firstterminal

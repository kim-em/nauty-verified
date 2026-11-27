import NautyVerified.Proofs.Search.Ops

/-!
# `recover`, factored

The Clight of nauty.c's `recover`; `body_eq` pins it.
-/

namespace NautyVerified.Proofs.Search.Recover

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Logic
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv ix)

abbrev body : statement :=
  (.Ssequence
    (forLoopC dense.id.«i»
      (.Ebinop .Olt (tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
      (sk
        (.Sifthenelse
          (.Ebinop .Ogt (ix dense.id.«ptn» (tv dense.id.«i»)) (tv dense.id.«level») tint)
          (sk (.Sassign (ix dense.id.«ptn» (tv dense.id.«i»)) (ci 2000000002 tint)))
          .Sskip)))
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Olt (tv dense.id.«level») (.Evar dense.id.«nauty:noncheaplevel» tint) tint)
          (sk
            (.Sassign
              (.Evar dense.id.«nauty:noncheaplevel» tint)
              (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint)))
          .Sskip))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Olt (tv dense.id.«level») (.Evar dense.id.«nauty:eqlev_first» tint) tint)
            (sk (.Sassign (.Evar dense.id.«nauty:eqlev_first» tint) (tv dense.id.«level»)))
            .Sskip))
        (sk
          (.Sifthenelse
            (.Evar dense.id.«nauty:getcanon» tint)
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .Olt (tv dense.id.«level») (.Evar dense.id.«nauty:gca_canon» tint) tint)
                  (sk (.Sassign (.Evar dense.id.«nauty:gca_canon» tint) (tv dense.id.«level»)))
                  .Sskip))
              (sk
                (.Sifthenelse
                  (.Ebinop .Ole (tv dense.id.«level») (.Evar dense.id.«nauty:eqlev_canon» tint) tint)
                  (.Ssequence
                    (sk (.Sassign (.Evar dense.id.«nauty:eqlev_canon» tint) (tv dense.id.«level»)))
                    (sk (.Sassign (.Evar dense.id.«nauty:comp_canon» tint) (ci 0 tint))))
                  .Sskip)))
            .Sskip)))))


kernel_rfl body_eq : dense.body.«nauty:recover» = body

end NautyVerified.Proofs.Search.Recover

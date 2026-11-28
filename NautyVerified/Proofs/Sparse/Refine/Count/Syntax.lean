import NautyVerified.Proofs.Sparse.Refine.Pieces

/-!
# The count split's Clight, for both passes

The distance pass's and the nontrivial pass's count splits are the same C up
to their temporaries and the hashes, which the distance pass takes on `w2`,
`k` and `bigpos` and the nontrivial pass on `w1`, `v3`, `bigsize` and `w3`.
`runG`, `minG`, `runLoopG`, `fragG` and `innerG` are the shared Clight,
parametrised by the temporaries and the flag `d` (true for the distance
pass); `runD = runG (idOf 716)` and so on by `rfl`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk pv setWord bitOf isElement addElementB delElementB)

/-- `s; rest` when `b`, else `rest`. -/
abbrev optSeq (b : Bool) (s rest : statement) : statement := if b then .Ssequence s rest else rest

/-- `a; s` when `b`, else `a`. -/
abbrev optEnd (b : Bool) (a s : statement) : statement := if b then .Ssequence a s else a

/-- `while (ptn[v2-1] > level && HITS[lab[v2]] == w1) ++v2;` -/
abbrev runG (t : Common.AST.ident) : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Ogt
              (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint))
              (tv id.«level»)
              tint)
            (sk
              (.Sset
                t
                (.Ecast
                  (.Ebinop .Oeq
                    (gix id.«nausparse:work3» (ix id.«lab» (tv id.«v2»)))
                    (tv id.«w1»)
                    tint)
                  tbool)))
            (.Sset t (ci 0 tint))))
        (.Sifthenelse (tv t) .Sskip .Sbreak))
      (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint))))
    .Sskip)

/-- The three-way insertion's do-while over `j`. -/
abbrev minG (t : Common.AST.ident) : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sset id.«lj» (ix id.«lab» (tv id.«j»))))
      (.Ssequence
        (sk (.Sset id.«w3» (gix id.«nausparse:work3» (tv id.«lj»))))
        (sk
          (.Sifthenelse
            (.Ebinop .Oeq (tv id.«w3») (tv id.«w1») tint)
            (.Ssequence
              (sk (.Sassign (ix id.«lab» (tv id.«j»)) (ix id.«lab» (tv id.«v3»))))
              (.Ssequence
                (sk (.Sassign (ix id.«lab» (tv id.«v3»)) (ix id.«lab» (tv id.«v2»))))
                (.Ssequence
                  (sk (.Sassign (ix id.«lab» (tv id.«v2»)) (tv id.«lj»)))
                  (.Ssequence
                    (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint)))
                    (sk (.Sset id.«v3» (.Ebinop .Oadd (tv id.«v3») (ci 1 tint) tint)))))))
            (sk
              (.Sifthenelse
                (.Ebinop .Oeq (tv id.«w3») (tv id.«w2») tint)
                (.Ssequence
                  (sk (.Sassign (ix id.«lab» (tv id.«j»)) (ix id.«lab» (tv id.«v3»))))
                  (.Ssequence
                    (sk (.Sassign (ix id.«lab» (tv id.«v3»)) (tv id.«lj»)))
                    (sk (.Sset id.«v3» (.Ebinop .Oadd (tv id.«v3») (ci 1 tint) tint)))))
                (sk
                  (.Sifthenelse
                    (.Ebinop .Olt (tv id.«w3») (tv id.«w1») tint)
                    (.Ssequence
                      (sk (.Sassign (ix id.«lab» (tv id.«j»)) (ix id.«lab» (tv id.«v2»))))
                      (.Ssequence
                        (sk (.Sassign (ix id.«lab» (tv id.«v2»)) (ix id.«lab» (tv id.«v1»))))
                        (.Ssequence
                          (sk (.Sassign (ix id.«lab» (tv id.«v1»)) (tv id.«lj»)))
                          (.Ssequence
                            (sk (.Sset id.«v3» (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint)))
                            (.Ssequence
                              (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint)))
                              (.Ssequence
                                (sk (.Sset id.«w2» (tv id.«w1»)))
                                (sk (.Sset id.«w1» (tv id.«w3»)))))))))
                    (sk
                      (.Sifthenelse
                        (.Ebinop .Olt (tv id.«w3») (tv id.«w2») tint)
                        (.Ssequence
                          (sk (.Sassign (ix id.«lab» (tv id.«j»)) (ix id.«lab» (tv id.«v2»))))
                          (.Ssequence
                            (sk (.Sassign (ix id.«lab» (tv id.«v2»)) (tv id.«lj»)))
                            (.Ssequence
                              (sk (.Sset id.«v3» (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint)))
                              (sk (.Sset id.«w2» (tv id.«w3»))))))
                        .Sskip))))))))))
    (.Ssequence
      (.Ssequence
        (sk (.Sset t (tv id.«j»)))
        (.Sset id.«j» (.Ebinop .Oadd (tv t) (ci 1 tint) tint)))
      (.Sifthenelse
        (.Ebinop .Ogt (ix id.«ptn» (tv t)) (tv id.«level») tint)
        .Sskip
        .Sbreak)))

/-- `for (k = l; k < j-1 && HITS[lab[k+1]] == w3; ++k) CELLSTART[lab[k+1]] = l;` -/
abbrev runLoopG (t : Common.AST.ident) : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Olt (tv id.«k») (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) tint)
            (sk
              (.Sset
                t
                (.Ecast
                  (.Ebinop .Oeq
                    (gix id.«nausparse:work3»
                      (ix id.«lab» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint)))
                    (tv id.«w3»)
                    tint)
                  tbool)))
            (.Sset t (ci 0 tint))))
        (.Sifthenelse (tv t) .Sskip .Sbreak))
      (sk
        (.Sassign
          (gix id.«nausparse:work1» (ix id.«lab» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint)))
          (tv id.«l»))))
    (sk (.Sset id.«k» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint))))

/-- The later fragments' loop. -/
abbrev fragG (d : Bool) (t : Common.AST.ident) (rl : statement) : statement :=
  (.Sloop
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Olt (tv id.«k») (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) tint)
          .Sskip
          .Sbreak))
      (.Ssequence
        (sk (.Sassign (ix id.«ptn» (tv id.«k»)) (tv id.«level»)))
        (optSeq d (sk (mash (tv id.«k»)))
          (.Ssequence
            (sk
              (.Sassign
                (.Ederef (pi id.«numcells») tint)
                (.Ebinop .Oadd (.Ederef (pi id.«numcells») tint) (ci 1 tint) tint)))
            (.Ssequence
              (sk (.Sset id.«l» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint)))
              (.Ssequence
                (addElementB id.«active» id.«nausparse:bit» (tv id.«l»))
                (.Ssequence
                  (.Ssequence
                    (.Ssequence
                      (sk (.Sset t (tv id.«nactive»)))
                      (.Sset id.«nactive» (.Ebinop .Oadd (tv t) (ci 1 tint) tint)))
                    (.Sassign (gix id.«nausparse:work2» (tv t)) (tv id.«l»)))
                  (.Ssequence
                    (sk (.Sset id.«w3» (gix id.«nausparse:work3» (ix id.«lab» (tv id.«l»)))))
                    (optSeq (!d)
                      (sk (mash (tv id.«w3»)))
                      (.Ssequence
                        (.Ssequence (sk (.Sset id.«k» (tv id.«l»))) rl)
                        (.Ssequence
                          (sk
                            (.Sset id.«size»
                              (.Ebinop .Oadd
                                (.Ebinop .Osub (tv id.«k») (tv id.«l») tint)
                                (ci 1 tint)
                                tint)))
                          (sk
                            (.Sifthenelse
                              (.Ebinop .Oeq (tv id.«size») (ci 1 tint) tint)
                              (sk
                                (.Sassign
                                  (gix id.«nausparse:work1» (ix id.«lab» (tv id.«l»)))
                                  (tv id.«n»)))
                              (.Ssequence
                                (sk
                                  (.Sassign
                                    (gix id.«nausparse:work1» (ix id.«lab» (tv id.«l»)))
                                    (tv id.«l»)))
                                (sk
                                  (.Sifthenelse
                                    (.Ebinop .Ogt (tv id.«size») (tv id.«bigsize») tint)
                                    (.Ssequence
                                      (sk (.Sset id.«bigsize» (tv id.«size»)))
                                      (sk
                                        (.Sset id.«bigpos»
                                          (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint))))
                                    .Sskip))))))))))))))))
    .Sskip)
/-- `if (j != v2) { ... }`, the installation after the first two hashes. -/
abbrev innerG (d : Bool) (t1 t2 t3 t4 t5 : Common.AST.ident) (frag : statement) : statement :=
  (.Sifthenelse
    (.Ebinop .One (tv id.«j») (tv id.«v2») tint)
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Oeq (tv id.«v2») (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint) tint)
          (sk (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«v1»))) (tv id.«n»)))
          .Sskip))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Oeq (tv id.«v3») (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint) tint)
            (sk (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«v2»))) (tv id.«n»)))
            (.Ssequence (sk (.Sset id.«k» (tv id.«v2»))) startsD)))
        (.Ssequence
          (sk
            (.Sassign
              (.Ederef (pi id.«numcells») tint)
              (.Ebinop .Oadd (.Ederef (pi id.«numcells») tint) (ci 1 tint) tint)))
          (.Ssequence
            (sk
              (.Sassign (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint)) (tv id.«level»)))
            (sk
              (.Sifthenelse
                (.Ebinop .Oeq (tv id.«j») (tv id.«v3») tint)
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Ebinop .Ole
                        (.Ebinop .Osub (tv id.«v2») (tv id.«v1») tint)
                        (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint)
                        tint)
                      (sk
                        (.Sset t1
                          (.Ecast
                            (.Eunop .Onotbool
                              (isElement id.«active» id.«nausparse:bit» (tv id.«v1»))
                              tint)
                            tbool)))
                      (.Sset t1 (ci 0 tint))))
                  (.Sifthenelse
                    (tv t1)
                    (.Ssequence
                      (addElementB id.«active» id.«nausparse:bit» (tv id.«v1»))
                      (.Ssequence
                        (.Ssequence
                          (sk (.Sset t2 (tv id.«nactive»)))
                          (.Sset id.«nactive» (.Ebinop .Oadd (tv t2) (ci 1 tint) tint)))
                        (.Sassign (gix id.«nausparse:work2» (tv t2)) (tv id.«v1»))))
                    (.Ssequence
                      (addElementB id.«active» id.«nausparse:bit» (tv id.«v2»))
                      (.Ssequence
                        (.Ssequence
                          (sk (.Sset t3 (tv id.«nactive»)))
                          (.Sset id.«nactive» (.Ebinop .Oadd (tv t3) (ci 1 tint) tint)))
                        (.Sassign (gix id.«nausparse:work2» (tv t3)) (tv id.«v2»))))))
                (optSeq (!d)
                  (sk (mash (tv id.«v3»)))
                  (.Ssequence
                    (sk
                      (.Scall none
                        (.Evar id.«nausparse:sortindirect»
                          (tfun [(tptr tint), (tptr tint), tint] Tvoid))
                        [(.Ebinop .Oadd (pi id.«lab») (tv id.«v3») (tptr tint)),
                         (.Evar id.«nausparse:work3» (tptr tint)),
                         (.Ebinop .Osub (tv id.«j») (tv id.«v3») tint)]))
                    (.Ssequence
                      (.Ssequence
                        (.Ssequence
                          (sk (.Sset t4 (tv id.«nactive»)))
                          (.Sset id.«nactive» (.Ebinop .Oadd (tv t4) (ci 1 tint) tint)))
                        (.Sassign (gix id.«nausparse:work2» (tv t4)) (tv id.«v2»)))
                      (.Ssequence
                        (addElementB id.«active» id.«nausparse:bit» (tv id.«v2»))
                        (.Ssequence
                          (sk
                            (.Sifthenelse
                              (.Ebinop .Oge
                                (.Ebinop .Osub (tv id.«v2») (tv id.«v1») tint)
                                (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint)
                                tint)
                              (.Ssequence
                                (sk (.Sset id.«bigpos» (.Eunop .Oneg (ci 1 tint) tint)))
                                (sk
                                  (.Sset id.«bigsize»
                                    (.Ebinop .Osub (tv id.«v2») (tv id.«v1») tint))))
                              (.Ssequence
                                (sk
                                  (.Sset id.«bigpos»
                                    (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint)))
                                (optEnd (!d)
                                  (sk
                                    (.Sset id.«bigsize»
                                      (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint)))
                                  (sk (mash (tv id.«bigsize»)))))))
                          (.Ssequence
                            (.Ssequence
                              (sk (.Sset id.«k» (.Ebinop .Osub (tv id.«v3») (ci 1 tint) tint)))
                              frag)
                            (.Ssequence
                              (sk
                                (.Sifthenelse
                                  (.Ebinop .Oge (tv id.«bigpos») (ci 0 tint) tint)
                                  (sk
                                    (.Sset t5
                                      (.Ecast
                                        (.Eunop .Onotbool
                                          (isElement id.«active» id.«nausparse:bit» (tv id.«v1»))
                                          tint)
                                        tbool)))
                                  (.Sset t5 (ci 0 tint))))
                              (.Sifthenelse
                                (tv t5)
                                (optSeq d (sk (mash (tv id.«bigpos»)))
                                  (.Ssequence
                                    (delElementB id.«active» id.«nausparse:bit»
                                      (gix id.«nausparse:work2» (tv id.«bigpos»)))
                                    (.Ssequence
                                      (addElementB id.«active» id.«nausparse:bit» (tv id.«v1»))
                                      (sk
                                        (.Sassign
                                          (gix id.«nausparse:work2» (tv id.«bigpos»))
                                          (tv id.«v1»))))))
                                .Sskip))))))))))))))
    .Sskip)

theorem runD_eq : runD = runG (idOf 716) := rfl
theorem runN_eq : runN = runG (idOf 753) := rfl
theorem minD_eq : minD = minG (idOf 718) := rfl
theorem minN_eq : minN = minG (idOf 755) := rfl
theorem startsN_eq : startsN = startsD := rfl
theorem runLoopD_eq : runLoopD = runLoopG (idOf 724) := rfl
theorem runLoopN_eq : runLoopN = runLoopG (idOf 761) := rfl
theorem fragLoopD_eq : fragLoopD = fragG true (idOf 723) (runLoopG (idOf 724)) := rfl
theorem fragLoopN_eq : fragLoopN = fragG false (idOf 760) (runLoopG (idOf 761)) := rfl
theorem installD_eq : installD =
    .Ssequence (sk (mash (tv id.«w2»))) (.Ssequence (sk (mash (tv id.«v2»)))
      (.Ssequence (sk (innerG true (idOf 721) (idOf 719) (idOf 720) (idOf 722) (idOf 725)
        (fragG true (idOf 723) (runLoopG (idOf 724))))) (sk (.Sset id.«v1» (tv id.«j»))))) := rfl
theorem installN_eq : installN =
    .Ssequence (sk (mash (tv id.«w1»))) (.Ssequence (sk (mash (tv id.«v2»)))
      (sk (innerG false (idOf 758) (idOf 756) (idOf 757) (idOf 759) (idOf 762)
        (fragG false (idOf 760) (runLoopG (idOf 761)))))) := rfl

end NautyVerified.Proofs.Sparse.Refine.Count

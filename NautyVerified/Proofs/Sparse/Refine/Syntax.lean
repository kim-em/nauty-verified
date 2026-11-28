import NautyVerified.Proofs.Set.Bit
import NautyVerified.Proofs.Alloc.Dyn
import NautyVerified.Source.Sparse

/-!
# `refine_sg`, factored

The Clight of nausparse.c's `refine_sg`, in named pieces; `body_eq` pins it
to `sparse.body.refine_sg`. The pieces were cut out of the printed body by
`scripts/factor_clight.py` with `scripts/factor/refine_sg.py`.

- `queueLoop`: `ACTIVE[0..nactive-1]`, the active cell starts in ascending
  order (`nextelement`);
- `startLoop`: `CELLSTART`, each vertex's cell start (`n` for singletons);
- `dist`: the distance split at `level <= 2` (`distvals` into `HITS`, then
  `distLoop` over the cells: the first run `runD`, the three-way insertion
  `minD` and the installation of the fragments `installD`, with `startsD`,
  `fragLoopD` and `runLoopD`);
- `mainLoop`: the splitter choice (`selectLoop`, the first singleton among the
  first ten queue entries), then `trivial` (the singleton splitter: the
  neighbour scan `edgeLoopT`, then `cellLoopT` over the touched cells with
  `partLoopT`, `revLoopT` and `fixT`) or `nontrivial` (the hit counts
  `countLoop` with `edgeLoopN` and `clearLoop`, then `cellLoopN` with `runN`,
  `minN` and `installN`, with `startsN`, `fragLoopN` and `runLoopN`);
- `finish`: the final code.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv setWord bitOf isElement addElementB delElementB)
open NautyVerified.Proofs.Alloc (dynalloc1)

namespace id
abbrev «_1406» : Common.AST.ident := sparse.id.«_1406»
abbrev «active» : Common.AST.ident := sparse.id.«active»
abbrev «bigpos» : Common.AST.ident := sparse.id.«bigpos»
abbrev «bigsize» : Common.AST.ident := sparse.id.«bigsize»
abbrev «code» : Common.AST.ident := sparse.id.«code»
abbrev «d» : Common.AST.ident := sparse.id.«d»
abbrev «di» : Common.AST.ident := sparse.id.«di»
abbrev «distvals» : Common.AST.ident := sparse.id.«distvals»
abbrev «e» : Common.AST.ident := sparse.id.«e»
abbrev «g» : Common.AST.ident := sparse.id.«g»
abbrev «hitcells» : Common.AST.ident := sparse.id.«hitcells»
abbrev «i» : Common.AST.ident := sparse.id.«i»
abbrev «ii» : Common.AST.ident := sparse.id.«ii»
abbrev «ij» : Common.AST.ident := sparse.id.«ij»
abbrev «ij__1» : Common.AST.ident := sparse.id.«ij__1»
abbrev «ij__2» : Common.AST.ident := sparse.id.«ij__2»
abbrev «isplit» : Common.AST.ident := sparse.id.«isplit»
abbrev «j» : Common.AST.ident := sparse.id.«j»
abbrev «k» : Common.AST.ident := sparse.id.«k»
abbrev «l» : Common.AST.ident := sparse.id.«l»
abbrev «lab» : Common.AST.ident := sparse.id.«lab»
abbrev «level» : Common.AST.ident := sparse.id.«level»
abbrev «lj» : Common.AST.ident := sparse.id.«lj»
abbrev «longcode» : Common.AST.ident := sparse.id.«longcode»
abbrev «m» : Common.AST.ident := sparse.id.«m»
abbrev «n» : Common.AST.ident := sparse.id.«n»
abbrev «nactive» : Common.AST.ident := sparse.id.«nactive»
abbrev «nausparse:__stringlit_6» : Common.AST.ident := sparse.id.«nausparse:__stringlit_6»
abbrev «nausparse:bit» : Common.AST.ident := sparse.id.«nausparse:bit»
abbrev «nausparse:preparemarks1» : Common.AST.ident := sparse.id.«nausparse:preparemarks1»
abbrev «nausparse:preparemarks2» : Common.AST.ident := sparse.id.«nausparse:preparemarks2»
abbrev «nausparse:sortindirect» : Common.AST.ident := sparse.id.«nausparse:sortindirect»
abbrev «nausparse:sortints» : Common.AST.ident := sparse.id.«nausparse:sortints»
abbrev «nausparse:vmark1» : Common.AST.ident := sparse.id.«nausparse:vmark1»
abbrev «nausparse:vmark1_sz» : Common.AST.ident := sparse.id.«nausparse:vmark1_sz»
abbrev «nausparse:vmark1_val» : Common.AST.ident := sparse.id.«nausparse:vmark1_val»
abbrev «nausparse:vmark2» : Common.AST.ident := sparse.id.«nausparse:vmark2»
abbrev «nausparse:vmark2_sz» : Common.AST.ident := sparse.id.«nausparse:vmark2_sz»
abbrev «nausparse:vmark2_val» : Common.AST.ident := sparse.id.«nausparse:vmark2_val»
abbrev «nausparse:work1» : Common.AST.ident := sparse.id.«nausparse:work1»
abbrev «nausparse:work1_sz» : Common.AST.ident := sparse.id.«nausparse:work1_sz»
abbrev «nausparse:work2» : Common.AST.ident := sparse.id.«nausparse:work2»
abbrev «nausparse:work2_sz» : Common.AST.ident := sparse.id.«nausparse:work2_sz»
abbrev «nausparse:work3» : Common.AST.ident := sparse.id.«nausparse:work3»
abbrev «nausparse:work3_sz» : Common.AST.ident := sparse.id.«nausparse:work3_sz»
abbrev «nausparse:work4» : Common.AST.ident := sparse.id.«nausparse:work4»
abbrev «nausparse:work4_sz» : Common.AST.ident := sparse.id.«nausparse:work4_sz»
abbrev «nextelement» : Common.AST.ident := sparse.id.«nextelement»
abbrev «numcells» : Common.AST.ident := sparse.id.«numcells»
abbrev «ptn» : Common.AST.ident := sparse.id.«ptn»
abbrev «size» : Common.AST.ident := sparse.id.«size»
abbrev «splitv» : Common.AST.ident := sparse.id.«splitv»
abbrev «trivsplit» : Common.AST.ident := sparse.id.«trivsplit»
abbrev «v» : Common.AST.ident := sparse.id.«v»
abbrev «v1» : Common.AST.ident := sparse.id.«v1»
abbrev «v2» : Common.AST.ident := sparse.id.«v2»
abbrev «v3» : Common.AST.ident := sparse.id.«v3»
abbrev «vi» : Common.AST.ident := sparse.id.«vi»
abbrev «w1» : Common.AST.ident := sparse.id.«w1»
abbrev «w2» : Common.AST.ident := sparse.id.«w2»
abbrev «w3» : Common.AST.ident := sparse.id.«w3»
end id

abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint
abbrev pi (x : Common.AST.ident) : expr := .Etempvar x (tptr tint)

/-- `p[a]` for an `int *` temporary `p`. -/
abbrev ix (p : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (pi p) a (tptr tint)) tint

/-- `p[a]` for an `int *` global `p`. -/
abbrev gix (p : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar p (tptr tint)) a (tptr tint)) tint

/-- `arr[a]` for a `short *` global `arr`. -/
abbrev mk (arr : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar arr (tptr tshort)) a (tptr tshort)) tshort

/-- `longcode = MASH(longcode, e)`. -/
abbrev mash (e : expr) : statement :=
  .Sset id.«longcode» (.Ebinop .Oand (.Ebinop .Oadd (.Ebinop .Oxor
    (.Etempvar id.«longcode» tlong) (ci 27421 tint) tlong) e tlong) (ci 32767 tint) tlong)

/-- `RESETMARKS` on the stamp `val`, capacity `sz` and array `arr`, with
temporaries `t` (the old stamp) and `ij` (the index). -/
abbrev resetmarks (val sz arr t ij : Common.AST.ident) : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence .Sskip (.Sset t (.Evar val tshort)))
      (.Sassign (.Evar val tshort) (.Ebinop .Oadd (.Etempvar t tshort) (ci 1 tint) tint)))
    (.Sifthenelse (.Ebinop .Oge (.Etempvar t tshort) (ci 32000 tint) tint)
      (.Ssequence
        (.Ssequence
          (.Ssequence .Sskip (.Sset ij (.Ecast (ci 0 tint) tulong)))
          (.Sloop
            (.Ssequence
              (.Ssequence .Sskip
                (.Sifthenelse (.Ebinop .Olt (.Etempvar ij tulong) (.Evar sz tulong) tint)
                  .Sskip .Sbreak))
              (.Ssequence .Sskip (.Sassign (mk arr (.Etempvar ij tulong)) (ci 0 tint))))
            (.Ssequence .Sskip (.Sset ij (.Ebinop .Oadd (.Etempvar ij tulong) (ci 1 tint) tulong)))))
        (.Ssequence .Sskip (.Sassign (.Evar val tshort) (ci 1 tint))))
      .Sskip)

abbrev queueLoop : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk
              (.Scall
                (some (idOf 711))
                (.Evar id.«nextelement» (tfun [(tptr tulong), tint, tint] tint))
                [(pv id.«active»), (tv id.«m»), (tv id.«i»)]))
            (.Sset (idOf 712) (.Ecast (tv (idOf 711)) tint)))
          (.Sset id.«i» (tv (idOf 712))))
        (.Sifthenelse (.Ebinop .Oge (tv (idOf 712)) (ci 0 tint) tint) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence
          (sk (.Sset (idOf 713) (tv id.«nactive»)))
          (.Sset id.«nactive» (.Ebinop .Oadd (tv (idOf 713)) (ci 1 tint) tint)))
        (.Sassign (gix id.«nausparse:work2» (tv (idOf 713))) (tv id.«i»))))
    .Sskip)

abbrev startLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.«i») (tv id.«n») tint) .Sskip .Sbreak))
      (sk
        (.Sifthenelse
          (.Ebinop .Ole (ix id.«ptn» (tv id.«i»)) (tv id.«level») tint)
          (.Ssequence
            (sk (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«i»))) (tv id.«n»)))
            (sk (.Sset id.«i» (.Ebinop .Oadd (tv id.«i») (ci 1 tint) tint))))
          (.Ssequence
            (sk (.Sset id.«j» (tv id.«i»)))
            (.Sloop
              (sk (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«i»))) (tv id.«j»)))
              (.Ssequence
                (.Ssequence
                  (sk (.Sset (idOf 714) (tv id.«i»)))
                  (.Sset id.«i» (.Ebinop .Oadd (tv (idOf 714)) (ci 1 tint) tint)))
                (.Sifthenelse
                  (.Ebinop .Ogt (ix id.«ptn» (tv (idOf 714))) (tv id.«level») tint)
                  .Sskip
                  .Sbreak)))))))
    .Sskip)

abbrev runD : statement :=
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
                (idOf 716)
                (.Ecast
                  (.Ebinop .Oeq
                    (gix id.«nausparse:work3» (ix id.«lab» (tv id.«v2»)))
                    (tv id.«w1»)
                    tint)
                  tbool)))
            (.Sset (idOf 716) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 716)) .Sskip .Sbreak))
      (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint))))
    .Sskip)

abbrev minD : statement :=
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
        (sk (.Sset (idOf 718) (tv id.«j»)))
        (.Sset id.«j» (.Ebinop .Oadd (tv (idOf 718)) (ci 1 tint) tint)))
      (.Sifthenelse
        (.Ebinop .Ogt (ix id.«ptn» (tv (idOf 718))) (tv id.«level») tint)
        .Sskip
        .Sbreak)))

abbrev startsD : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.«k») (tv id.«v3») tint) .Sskip .Sbreak))
      (sk (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«k»))) (tv id.«v2»))))
    (sk (.Sset id.«k» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint))))

abbrev runLoopD : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Olt (tv id.«k») (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) tint)
            (sk
              (.Sset
                (idOf 724)
                (.Ecast
                  (.Ebinop .Oeq
                    (gix id.«nausparse:work3»
                      (ix id.«lab» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint)))
                    (tv id.«w3»)
                    tint)
                  tbool)))
            (.Sset (idOf 724) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 724)) .Sskip .Sbreak))
      (sk
        (.Sassign
          (gix id.«nausparse:work1» (ix id.«lab» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint)))
          (tv id.«l»))))
    (sk (.Sset id.«k» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint))))

abbrev fragLoopD : statement :=
  (.Sloop
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Olt (tv id.«k») (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) tint)
          .Sskip
          .Sbreak))
      (.Ssequence
        (sk (.Sassign (ix id.«ptn» (tv id.«k»)) (tv id.«level»)))
        (.Ssequence
          (sk (mash (tv id.«k»)))
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
                      (sk (.Sset (idOf 723) (tv id.«nactive»)))
                      (.Sset id.«nactive» (.Ebinop .Oadd (tv (idOf 723)) (ci 1 tint) tint)))
                    (.Sassign (gix id.«nausparse:work2» (tv (idOf 723))) (tv id.«l»)))
                  (.Ssequence
                    (sk (.Sset id.«w3» (gix id.«nausparse:work3» (ix id.«lab» (tv id.«l»)))))
                    (.Ssequence
                      (.Ssequence (sk (.Sset id.«k» (tv id.«l»))) runLoopD)
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
                                  .Sskip)))))))))))))))
    .Sskip)

abbrev installD : statement :=
  (.Ssequence
    (sk (mash (tv id.«w2»)))
    (.Ssequence
      (sk (mash (tv id.«v2»)))
      (.Ssequence
        (sk
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
                    (sk
                      (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«v2»))) (tv id.«n»)))
                    (.Ssequence (sk (.Sset id.«k» (tv id.«v2»))) startsD)))
                (.Ssequence
                  (sk
                    (.Sassign
                      (.Ederef (pi id.«numcells») tint)
                      (.Ebinop .Oadd (.Ederef (pi id.«numcells») tint) (ci 1 tint) tint)))
                  (.Ssequence
                    (sk
                      (.Sassign
                        (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint))
                        (tv id.«level»)))
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
                                (.Sset
                                  (idOf 721)
                                  (.Ecast
                                    (.Eunop .Onotbool
                                      (isElement id.«active» id.«nausparse:bit» (tv id.«v1»))
                                      tint)
                                    tbool)))
                              (.Sset (idOf 721) (ci 0 tint))))
                          (.Sifthenelse
                            (tv (idOf 721))
                            (.Ssequence
                              (addElementB id.«active» id.«nausparse:bit» (tv id.«v1»))
                              (.Ssequence
                                (.Ssequence
                                  (sk (.Sset (idOf 719) (tv id.«nactive»)))
                                  (.Sset id.«nactive»
                                    (.Ebinop .Oadd (tv (idOf 719)) (ci 1 tint) tint)))
                                (.Sassign (gix id.«nausparse:work2» (tv (idOf 719))) (tv id.«v1»))))
                            (.Ssequence
                              (addElementB id.«active» id.«nausparse:bit» (tv id.«v2»))
                              (.Ssequence
                                (.Ssequence
                                  (sk (.Sset (idOf 720) (tv id.«nactive»)))
                                  (.Sset id.«nactive»
                                    (.Ebinop .Oadd (tv (idOf 720)) (ci 1 tint) tint)))
                                (.Sassign (gix id.«nausparse:work2» (tv (idOf 720))) (tv id.«v2»))))))
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
                                (sk (.Sset (idOf 722) (tv id.«nactive»)))
                                (.Sset id.«nactive»
                                  (.Ebinop .Oadd (tv (idOf 722)) (ci 1 tint) tint)))
                              (.Sassign (gix id.«nausparse:work2» (tv (idOf 722))) (tv id.«v2»)))
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
                                      (sk
                                        (.Sset id.«bigsize»
                                          (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint))))))
                                (.Ssequence
                                  (.Ssequence
                                    (sk
                                      (.Sset id.«k» (.Ebinop .Osub (tv id.«v3») (ci 1 tint) tint)))
                                    fragLoopD)
                                  (.Ssequence
                                    (sk
                                      (.Sifthenelse
                                        (.Ebinop .Oge (tv id.«bigpos») (ci 0 tint) tint)
                                        (sk
                                          (.Sset
                                            (idOf 725)
                                            (.Ecast
                                              (.Eunop .Onotbool
                                                (isElement id.«active» id.«nausparse:bit»
                                                  (tv id.«v1»))
                                                tint)
                                              tbool)))
                                        (.Sset (idOf 725) (ci 0 tint))))
                                    (.Sifthenelse
                                      (tv (idOf 725))
                                      (.Ssequence
                                        (sk (mash (tv id.«bigpos»)))
                                        (.Ssequence
                                          (delElementB id.«active» id.«nausparse:bit»
                                            (gix id.«nausparse:work2» (tv id.«bigpos»)))
                                          (.Ssequence
                                            (addElementB id.«active» id.«nausparse:bit»
                                              (tv id.«v1»))
                                            (sk
                                              (.Sassign
                                                (gix id.«nausparse:work2» (tv id.«bigpos»))
                                                (tv id.«v1»))))))
                                      .Sskip)))))))))))))
            .Sskip))
        (sk (.Sset id.«v1» (tv id.«j»))))))

abbrev distLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.«v1») (tv id.«n») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Ole (ix id.«ptn» (tv id.«v1»)) (tv id.«level») tint)
            (.Ssequence
              (sk (.Sset id.«v1» (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint)))
              .Scontinue)
            .Sskip))
        (.Ssequence
          (sk (mash (tv id.«v1»)))
          (.Ssequence
            (sk (.Sset id.«w1» (gix id.«nausparse:work3» (ix id.«lab» (tv id.«v1»)))))
            (.Ssequence
              (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint)))
              (.Ssequence runD
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Ebinop .Ole
                        (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint))
                        (tv id.«level»)
                        tint)
                      (.Ssequence (sk (.Sset id.«v1» (tv id.«v2»))) .Scontinue)
                      .Sskip))
                  (.Ssequence
                    (sk (.Sset id.«w2» (ci 2000000002 tint)))
                    (.Ssequence
                      (.Ssequence
                        (.Ssequence
                          (sk (.Sset (idOf 717) (.Ecast (tv id.«v2») tint)))
                          (.Sset id.«j» (tv (idOf 717))))
                        (.Sset id.«v3» (tv (idOf 717))))
                      (.Ssequence minD installD))))))))))
    .Sskip)

abbrev dist : statement :=
  (.Ssequence
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Ole (tv id.«level») (ci 2 tint) tint)
            (sk (.Sset (idOf 726) (.Ecast (.Ebinop .Oeq (tv id.«nactive») (ci 1 tint) tint) tbool)))
            (.Sset (idOf 726) (ci 0 tint))))
        (.Sifthenelse
          (tv (idOf 726))
          (sk
            (.Sset
              (idOf 727)
              (.Ecast
                (.Ebinop .Ole
                  (ix id.«ptn» (gix id.«nausparse:work2» (ci 0 tint)))
                  (tv id.«level»)
                  tint)
                tbool)))
          (.Sset (idOf 727) (ci 0 tint))))
      (.Sifthenelse
        (tv (idOf 727))
        (sk
          (.Sset
            (idOf 728)
            (.Ecast
              (.Ebinop .Ole
                (.Ederef (pi id.«numcells») tint)
                (.Ebinop .Odiv (tv id.«n») (ci 8 tint) tint)
                tint)
              tbool)))
        (.Sset (idOf 728) (ci 0 tint))))
    (.Sifthenelse
      (tv (idOf 728))
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk (.Sset (idOf 715) (.Ecast (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint) tint)))
            (.Sset id.«nactive» (tv (idOf 715))))
          (.Sset id.«isplit» (gix id.«nausparse:work2» (tv (idOf 715)))))
        (.Ssequence
          (delElementB id.«active» id.«nausparse:bit» (tv id.«isplit»))
          (.Ssequence
            (sk
              (.Scall none
                (.Evar id.«distvals»
                  (tfun [(tptr (Tstruct id.«_1406» noattr)), tint, (tptr tint), tint] Tvoid))
                [(.Ecast (pv id.«g») (tptr (Tstruct id.«_1406» noattr))),
                 (ix id.«lab» (tv id.«isplit»)),
                 (.Evar id.«nausparse:work3» (tptr tint)),
                 (tv id.«n»)]))
            (.Ssequence (sk (.Sset id.«v1» (ci 0 tint))) distLoop))))
      .Sskip))

abbrev selectLoop : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Olt (tv id.«i») (tv id.«nactive») tint)
            (sk (.Sset (idOf 730) (.Ecast (.Ebinop .Olt (tv id.«i») (ci 10 tint) tint) tbool)))
            (.Sset (idOf 730) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 730)) .Sskip .Sbreak))
      (sk
        (.Sifthenelse
          (.Ebinop .Ole (ix id.«ptn» (gix id.«nausparse:work2» (tv id.«i»))) (tv id.«level») tint)
          .Sbreak
          .Sskip)))
    (sk (.Sset id.«i» (.Ebinop .Oadd (tv id.«i») (ci 1 tint) tint))))

abbrev edgeLoopT : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (.Etempvar id.«ii» tulong) (tv id.«di») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk
          (.Sset id.«j»
            (ix id.«e» (.Ebinop .Oadd (.Etempvar id.«vi» tulong) (.Etempvar id.«ii» tulong) tulong))))
        (.Ssequence
          (sk
            (.Sassign
              (mk id.«nausparse:vmark2» (tv id.«j»))
              (.Evar id.«nausparse:vmark2_val» tshort)))
          (.Ssequence
            (sk (.Sset id.«k» (gix id.«nausparse:work1» (tv id.«j»))))
            (.Ssequence
              (sk
                (.Sifthenelse
                  (.Ebinop .One (tv id.«k») (tv id.«n») tint)
                  (sk
                    (.Sset
                      (idOf 737)
                      (.Ecast
                        (.Ebinop .One
                          (mk id.«nausparse:vmark1» (tv id.«k»))
                          (.Evar id.«nausparse:vmark1_val» tshort)
                          tint)
                        tbool)))
                  (.Sset (idOf 737) (ci 0 tint))))
              (.Sifthenelse
                (tv (idOf 737))
                (.Ssequence
                  (sk
                    (.Sassign
                      (mk id.«nausparse:vmark1» (tv id.«k»))
                      (.Evar id.«nausparse:vmark1_val» tshort)))
                  (.Ssequence
                    (.Ssequence
                      (sk (.Sset (idOf 736) (tv id.«hitcells»)))
                      (.Sset id.«hitcells» (.Ebinop .Oadd (tv (idOf 736)) (ci 1 tint) tint)))
                    (.Sassign (gix id.«nausparse:work4» (tv (idOf 736))) (tv id.«k»))))
                .Sskip))))))
    (sk (.Sset id.«ii» (.Ebinop .Oadd (.Etempvar id.«ii» tulong) (ci 1 tint) tulong))))

abbrev partLoopT : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sset id.«lj» (ix id.«lab» (tv id.«j»))))
      (sk
        (.Sifthenelse
          (.Ebinop .Oeq
            (mk id.«nausparse:vmark2» (tv id.«lj»))
            (.Evar id.«nausparse:vmark2_val» tshort)
            tint)
          (.Ssequence
            (.Ssequence
              (sk (.Sset (idOf 741) (tv id.«k»)))
              (.Sset id.«k» (.Ebinop .Oadd (tv (idOf 741)) (ci 1 tint) tint)))
            (.Sassign (gix id.«nausparse:work3» (tv (idOf 741))) (tv id.«lj»)))
          (.Ssequence
            (.Ssequence
              (sk (.Sset (idOf 742) (tv id.«v2»)))
              (.Sset id.«v2» (.Ebinop .Oadd (tv (idOf 742)) (ci 1 tint) tint)))
            (.Sassign (ix id.«lab» (tv (idOf 742))) (tv id.«lj»))))))
    (.Ssequence
      (.Ssequence
        (sk (.Sset (idOf 740) (tv id.«j»)))
        (.Sset id.«j» (.Ebinop .Oadd (tv (idOf 740)) (ci 1 tint) tint)))
      (.Sifthenelse
        (.Ebinop .Ogt (ix id.«ptn» (tv (idOf 740))) (tv id.«level») tint)
        .Sskip
        .Sbreak)))

abbrev revLoopT : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (sk (.Sset (idOf 743) (.Ecast (.Ebinop .Osub (tv id.«k») (ci 1 tint) tint) tint)))
          (.Sset id.«k» (tv (idOf 743))))
        (.Sifthenelse (.Ebinop .Oge (tv (idOf 743)) (ci 0 tint) tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sset id.«j» (gix id.«nausparse:work3» (tv id.«k»))))
        (.Ssequence
          (sk (.Sassign (gix id.«nausparse:work1» (tv id.«j»)) (tv id.«v2»)))
          (.Ssequence
            (.Ssequence
              (sk (.Sset (idOf 744) (tv id.«v3»)))
              (.Sset id.«v3» (.Ebinop .Oadd (tv (idOf 744)) (ci 1 tint) tint)))
            (.Sassign (ix id.«lab» (tv (idOf 744))) (tv id.«j»))))))
    .Sskip)

abbrev fixT : statement :=
  (.Sifthenelse
    (tv (idOf 748))
    (.Ssequence
      (sk
        (.Sassign
          (.Ederef (pi id.«numcells») tint)
          (.Ebinop .Oadd (.Ederef (pi id.«numcells») tint) (ci 1 tint) tint)))
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
              .Sskip))
          (.Ssequence
            (sk
              (.Sassign (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint)) (tv id.«level»)))
            (.Ssequence
              (sk (mash (tv id.«v2»)))
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Ebinop .Ole
                      (.Ebinop .Osub (tv id.«v2») (tv id.«v1») tint)
                      (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint)
                      tint)
                    (sk
                      (.Sset
                        (idOf 747)
                        (.Ecast
                          (.Eunop .Onotbool
                            (isElement id.«active» id.«nausparse:bit» (tv id.«v1»))
                            tint)
                          tbool)))
                    (.Sset (idOf 747) (ci 0 tint))))
                (.Sifthenelse
                  (tv (idOf 747))
                  (.Ssequence
                    (addElementB id.«active» id.«nausparse:bit» (tv id.«v1»))
                    (.Ssequence
                      (.Ssequence
                        (sk (.Sset (idOf 745) (tv id.«nactive»)))
                        (.Sset id.«nactive» (.Ebinop .Oadd (tv (idOf 745)) (ci 1 tint) tint)))
                      (.Sassign (gix id.«nausparse:work2» (tv (idOf 745))) (tv id.«v1»))))
                  (.Ssequence
                    (addElementB id.«active» id.«nausparse:bit» (tv id.«v2»))
                    (.Ssequence
                      (.Ssequence
                        (sk (.Sset (idOf 746) (tv id.«nactive»)))
                        (.Sset id.«nactive» (.Ebinop .Oadd (tv (idOf 746)) (ci 1 tint) tint)))
                      (.Sassign (gix id.«nausparse:work2» (tv (idOf 746))) (tv id.«v2»)))))))))))
    .Sskip)

abbrev cellLoopT : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.«i») (tv id.«hitcells») tint) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (.Ssequence
                (sk (.Sset (idOf 738) (.Ecast (gix id.«nausparse:work4» (tv id.«i»)) tint)))
                (.Sset id.«v2» (tv (idOf 738))))
              (.Sset (idOf 739) (.Ecast (tv (idOf 738)) tint)))
            (.Sset id.«v1» (tv (idOf 739))))
          (.Sset id.«j» (tv (idOf 739))))
        (.Ssequence
          (sk (mash (tv id.«v2»)))
          (.Ssequence
            (sk (.Sset id.«k» (ci 0 tint)))
            (.Ssequence partLoopT
              (.Ssequence
                (sk (mash (tv id.«k»)))
                (.Ssequence
                  (sk (.Sset id.«v3» (tv id.«v2»)))
                  (.Ssequence revLoopT
                    (.Ssequence
                      (sk
                        (.Sifthenelse
                          (.Ebinop .One (tv id.«v2») (tv id.«v3») tint)
                          (sk
                            (.Sset
                              (idOf 748)
                              (.Ecast (.Ebinop .One (tv id.«v2») (tv id.«v1») tint) tbool)))
                          (.Sset (idOf 748) (ci 0 tint))))
                      fixT)))))))))
    (sk (.Sset id.«i» (.Ebinop .Oadd (tv id.«i») (ci 1 tint) tint))))

abbrev trivial : statement :=
  (.Ssequence
    (resetmarks id.«nausparse:vmark1_val» id.«nausparse:vmark1_sz» id.«nausparse:vmark1»
      (idOf 734)
      id.«ij»)
    (.Ssequence
      (resetmarks id.«nausparse:vmark2_val» id.«nausparse:vmark2_sz» id.«nausparse:vmark2»
        (idOf 735)
        id.«ij__1»)
      (.Ssequence
        (sk (.Sset id.«hitcells» (ci 0 tint)))
        (.Ssequence
          (sk (.Sset id.«splitv» (ix id.«lab» (tv id.«isplit»))))
          (.Ssequence
            (sk
              (.Sset id.«vi»
                (.Ederef (.Ebinop .Oadd (pv id.«v») (tv id.«splitv») (tptr tulong)) tulong)))
            (.Ssequence
              (sk (.Sset id.«di» (ix id.«d» (tv id.«splitv»))))
              (.Ssequence
                (.Ssequence (sk (.Sset id.«ii» (.Ecast (ci 0 tint) tulong))) edgeLoopT)
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Ebinop .Ogt (tv id.«hitcells») (ci 1 tint) tint)
                      (sk
                        (.Scall none
                          (.Evar id.«nausparse:sortints» (tfun [(tptr tint), tint] Tvoid))
                          [(.Evar id.«nausparse:work4» (tptr tint)), (tv id.«hitcells»)]))
                      .Sskip))
                  (.Ssequence
                    (sk (mash (tv id.«hitcells»)))
                    (.Ssequence (sk (.Sset id.«i» (ci 0 tint))) cellLoopT))))))))))

abbrev clearLoop : statement :=
  (.Sloop
    (sk (.Sassign (gix id.«nausparse:work3» (ix id.«lab» (tv id.«k»))) (ci 0 tint)))
    (.Ssequence
      (.Ssequence
        (sk (.Sset (idOf 752) (tv id.«k»)))
        (.Sset id.«k» (.Ebinop .Oadd (tv (idOf 752)) (ci 1 tint) tint)))
      (.Sifthenelse
        (.Ebinop .Ogt (ix id.«ptn» (tv (idOf 752))) (tv id.«level») tint)
        .Sskip
        .Sbreak)))

abbrev edgeLoopN : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (.Etempvar id.«ii» tulong) (tv id.«di») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk
          (.Sset id.«j»
            (ix id.«e» (.Ebinop .Oadd (.Etempvar id.«vi» tulong) (.Etempvar id.«ii» tulong) tulong))))
        (.Ssequence
          (sk (.Sset id.«k» (gix id.«nausparse:work1» (tv id.«j»))))
          (sk
            (.Sifthenelse
              (.Ebinop .One (tv id.«k») (tv id.«n») tint)
              (.Ssequence
                (sk
                  (.Sifthenelse
                    (.Ebinop .One
                      (mk id.«nausparse:vmark1» (tv id.«k»))
                      (.Evar id.«nausparse:vmark1_val» tshort)
                      tint)
                    (.Ssequence
                      (sk
                        (.Sassign
                          (mk id.«nausparse:vmark1» (tv id.«k»))
                          (.Evar id.«nausparse:vmark1_val» tshort)))
                      (.Ssequence
                        (.Ssequence
                          (.Ssequence
                            (sk (.Sset (idOf 751) (tv id.«hitcells»)))
                            (.Sset id.«hitcells» (.Ebinop .Oadd (tv (idOf 751)) (ci 1 tint) tint)))
                          (.Sassign (gix id.«nausparse:work4» (tv (idOf 751))) (tv id.«k»)))
                        clearLoop))
                    .Sskip))
                (sk
                  (.Sassign
                    (gix id.«nausparse:work3» (tv id.«j»))
                    (.Ebinop .Oadd (gix id.«nausparse:work3» (tv id.«j»)) (ci 1 tint) tint))))
              .Sskip)))))
    (sk (.Sset id.«ii» (.Ebinop .Oadd (.Etempvar id.«ii» tulong) (ci 1 tint) tulong))))

abbrev countLoop : statement :=
  (.Sloop
    (.Ssequence
      (sk
        (.Sset id.«vi»
          (.Ederef (.Ebinop .Oadd (pv id.«v») (ix id.«lab» (tv id.«isplit»)) (tptr tulong)) tulong)))
      (.Ssequence
        (sk (.Sset id.«di» (ix id.«d» (ix id.«lab» (tv id.«isplit»)))))
        (.Ssequence (sk (.Sset id.«ii» (.Ecast (ci 0 tint) tulong))) edgeLoopN)))
    (.Ssequence
      (.Ssequence
        (sk (.Sset (idOf 750) (tv id.«isplit»)))
        (.Sset id.«isplit» (.Ebinop .Oadd (tv (idOf 750)) (ci 1 tint) tint)))
      (.Sifthenelse
        (.Ebinop .Ogt (ix id.«ptn» (tv (idOf 750))) (tv id.«level») tint)
        .Sskip
        .Sbreak)))

abbrev runN : statement :=
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
                (idOf 753)
                (.Ecast
                  (.Ebinop .Oeq
                    (gix id.«nausparse:work3» (ix id.«lab» (tv id.«v2»)))
                    (tv id.«w1»)
                    tint)
                  tbool)))
            (.Sset (idOf 753) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 753)) .Sskip .Sbreak))
      (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint))))
    .Sskip)

abbrev minN : statement :=
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
        (sk (.Sset (idOf 755) (tv id.«j»)))
        (.Sset id.«j» (.Ebinop .Oadd (tv (idOf 755)) (ci 1 tint) tint)))
      (.Sifthenelse
        (.Ebinop .Ogt (ix id.«ptn» (tv (idOf 755))) (tv id.«level») tint)
        .Sskip
        .Sbreak)))

abbrev startsN : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.«k») (tv id.«v3») tint) .Sskip .Sbreak))
      (sk (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«k»))) (tv id.«v2»))))
    (sk (.Sset id.«k» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint))))

abbrev runLoopN : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Olt (tv id.«k») (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) tint)
            (sk
              (.Sset
                (idOf 761)
                (.Ecast
                  (.Ebinop .Oeq
                    (gix id.«nausparse:work3»
                      (ix id.«lab» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint)))
                    (tv id.«w3»)
                    tint)
                  tbool)))
            (.Sset (idOf 761) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 761)) .Sskip .Sbreak))
      (sk
        (.Sassign
          (gix id.«nausparse:work1» (ix id.«lab» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint)))
          (tv id.«l»))))
    (sk (.Sset id.«k» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint))))

abbrev fragLoopN : statement :=
  (.Sloop
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Olt (tv id.«k») (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) tint)
          .Sskip
          .Sbreak))
      (.Ssequence
        (sk (.Sassign (ix id.«ptn» (tv id.«k»)) (tv id.«level»)))
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
                    (sk (.Sset (idOf 760) (tv id.«nactive»)))
                    (.Sset id.«nactive» (.Ebinop .Oadd (tv (idOf 760)) (ci 1 tint) tint)))
                  (.Sassign (gix id.«nausparse:work2» (tv (idOf 760))) (tv id.«l»)))
                (.Ssequence
                  (sk (.Sset id.«w3» (gix id.«nausparse:work3» (ix id.«lab» (tv id.«l»)))))
                  (.Ssequence
                    (sk (mash (tv id.«w3»)))
                    (.Ssequence
                      (.Ssequence (sk (.Sset id.«k» (tv id.«l»))) runLoopN)
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
                                  .Sskip)))))))))))))))
    .Sskip)

abbrev installN : statement :=
  (.Ssequence
    (sk (mash (tv id.«w1»)))
    (.Ssequence
      (sk (mash (tv id.«v2»)))
      (sk
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
                  (.Ssequence (sk (.Sset id.«k» (tv id.«v2»))) startsN)))
              (.Ssequence
                (sk
                  (.Sassign
                    (.Ederef (pi id.«numcells») tint)
                    (.Ebinop .Oadd (.Ederef (pi id.«numcells») tint) (ci 1 tint) tint)))
                (.Ssequence
                  (sk
                    (.Sassign
                      (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint))
                      (tv id.«level»)))
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
                              (.Sset
                                (idOf 758)
                                (.Ecast
                                  (.Eunop .Onotbool
                                    (isElement id.«active» id.«nausparse:bit» (tv id.«v1»))
                                    tint)
                                  tbool)))
                            (.Sset (idOf 758) (ci 0 tint))))
                        (.Sifthenelse
                          (tv (idOf 758))
                          (.Ssequence
                            (addElementB id.«active» id.«nausparse:bit» (tv id.«v1»))
                            (.Ssequence
                              (.Ssequence
                                (sk (.Sset (idOf 756) (tv id.«nactive»)))
                                (.Sset id.«nactive»
                                  (.Ebinop .Oadd (tv (idOf 756)) (ci 1 tint) tint)))
                              (.Sassign (gix id.«nausparse:work2» (tv (idOf 756))) (tv id.«v1»))))
                          (.Ssequence
                            (addElementB id.«active» id.«nausparse:bit» (tv id.«v2»))
                            (.Ssequence
                              (.Ssequence
                                (sk (.Sset (idOf 757) (tv id.«nactive»)))
                                (.Sset id.«nactive»
                                  (.Ebinop .Oadd (tv (idOf 757)) (ci 1 tint) tint)))
                              (.Sassign (gix id.«nausparse:work2» (tv (idOf 757))) (tv id.«v2»))))))
                      (.Ssequence
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
                                (sk (.Sset (idOf 759) (tv id.«nactive»)))
                                (.Sset id.«nactive»
                                  (.Ebinop .Oadd (tv (idOf 759)) (ci 1 tint) tint)))
                              (.Sassign (gix id.«nausparse:work2» (tv (idOf 759))) (tv id.«v2»)))
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
                                      (.Ssequence
                                        (sk
                                          (.Sset id.«bigsize»
                                            (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint)))
                                        (sk (mash (tv id.«bigsize»)))))))
                                (.Ssequence
                                  (.Ssequence
                                    (sk
                                      (.Sset id.«k» (.Ebinop .Osub (tv id.«v3») (ci 1 tint) tint)))
                                    fragLoopN)
                                  (.Ssequence
                                    (sk
                                      (.Sifthenelse
                                        (.Ebinop .Oge (tv id.«bigpos») (ci 0 tint) tint)
                                        (sk
                                          (.Sset
                                            (idOf 762)
                                            (.Ecast
                                              (.Eunop .Onotbool
                                                (isElement id.«active» id.«nausparse:bit»
                                                  (tv id.«v1»))
                                                tint)
                                              tbool)))
                                        (.Sset (idOf 762) (ci 0 tint))))
                                    (.Sifthenelse
                                      (tv (idOf 762))
                                      (.Ssequence
                                        (delElementB id.«active» id.«nausparse:bit»
                                          (gix id.«nausparse:work2» (tv id.«bigpos»)))
                                        (.Ssequence
                                          (addElementB id.«active» id.«nausparse:bit» (tv id.«v1»))
                                          (sk
                                            (.Sassign
                                              (gix id.«nausparse:work2» (tv id.«bigpos»))
                                              (tv id.«v1»)))))
                                      .Sskip))))))))))))))
          .Sskip))))

abbrev cellLoopN : statement :=
  (.Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Olt (tv id.«i») (tv id.«hitcells») tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sset id.«v1» (gix id.«nausparse:work4» (tv id.«i»))))
        (.Ssequence
          (sk (.Sset id.«w1» (gix id.«nausparse:work3» (ix id.«lab» (tv id.«v1»)))))
          (.Ssequence
            (sk (mash (tv id.«v1»)))
            (.Ssequence
              (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint)))
              (.Ssequence runN
                (.Ssequence
                  (sk
                    (.Sifthenelse
                      (.Ebinop .Ole
                        (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint))
                        (tv id.«level»)
                        tint)
                      .Scontinue
                      .Sskip))
                  (.Ssequence
                    (sk (.Sset id.«w2» (ci 2000000002 tint)))
                    (.Ssequence
                      (.Ssequence
                        (.Ssequence
                          (sk (.Sset (idOf 754) (.Ecast (tv id.«v2») tint)))
                          (.Sset id.«j» (tv (idOf 754))))
                        (.Sset id.«v3» (tv (idOf 754))))
                      (.Ssequence minN installN))))))))))
    (sk (.Sset id.«i» (.Ebinop .Oadd (tv id.«i») (ci 1 tint) tint))))

abbrev nontrivial : statement :=
  (.Ssequence
    (resetmarks id.«nausparse:vmark1_val» id.«nausparse:vmark1_sz» id.«nausparse:vmark1»
      (idOf 749)
      id.«ij__2»)
    (.Ssequence
      (sk (.Sset id.«hitcells» (ci 0 tint)))
      (.Ssequence countLoop
        (.Ssequence
          (sk
            (.Sifthenelse
              (.Ebinop .Ogt (tv id.«hitcells») (ci 1 tint) tint)
              (sk
                (.Scall none
                  (.Evar id.«nausparse:sortints» (tfun [(tptr tint), tint] Tvoid))
                  [(.Evar id.«nausparse:work4» (tptr tint)), (tv id.«hitcells»)]))
              .Sskip))
          (.Ssequence
            (sk (mash (tv id.«hitcells»)))
            (.Ssequence (sk (.Sset id.«i» (ci 0 tint))) cellLoopN))))))

abbrev mainLoop : statement :=
  (.Sloop
    (.Ssequence
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Ogt (tv id.«nactive») (ci 0 tint) tint)
            (sk
              (.Sset
                (idOf 729)
                (.Ecast (.Ebinop .Olt (.Ederef (pi id.«numcells») tint) (tv id.«n») tint) tbool)))
            (.Sset (idOf 729) (ci 0 tint))))
        (.Sifthenelse (tv (idOf 729)) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence (sk (.Sset id.«i» (ci 0 tint))) selectLoop)
        (.Ssequence
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .Olt (tv id.«i») (tv id.«nactive») tint)
                (sk (.Sset (idOf 733) (.Ecast (.Ebinop .Olt (tv id.«i») (ci 10 tint) tint) tbool)))
                (.Sset (idOf 733) (ci 0 tint))))
            (.Sifthenelse
              (tv (idOf 733))
              (.Ssequence
                (sk (.Sset id.«trivsplit» (ci 1 tint)))
                (.Ssequence
                  (sk (.Sset id.«isplit» (gix id.«nausparse:work2» (tv id.«i»))))
                  (.Ssequence
                    (.Ssequence
                      (sk
                        (.Sset
                          (idOf 731)
                          (.Ecast (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint) tint)))
                      (.Sset id.«nactive» (tv (idOf 731))))
                    (.Sassign
                      (gix id.«nausparse:work2» (tv id.«i»))
                      (gix id.«nausparse:work2» (tv (idOf 731)))))))
              (.Ssequence
                (.Ssequence
                  (.Ssequence
                    (sk
                      (.Sset
                        (idOf 732)
                        (.Ecast (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint) tint)))
                    (.Sset id.«nactive» (tv (idOf 732))))
                  (.Sset id.«isplit» (gix id.«nausparse:work2» (tv (idOf 732)))))
                (sk
                  (.Sset id.«trivsplit»
                    (.Ebinop .Ole (ix id.«ptn» (tv id.«isplit»)) (tv id.«level») tint))))))
          (.Ssequence
            (delElementB id.«active» id.«nausparse:bit» (tv id.«isplit»))
            (.Ssequence
              (sk (mash (tv id.«isplit»)))
              (sk (.Sifthenelse (tv id.«trivsplit») trivial nontrivial)))))))
    .Sskip)

abbrev finish : statement :=
  (.Ssequence
    (sk (mash (.Ederef (pi id.«numcells») tint)))
    (sk
      (.Sassign
        (.Ederef (pi id.«code») tint)
        (.Ecast (.Ebinop .Omod (.Etempvar id.«longcode» tlong) (ci 32767 tint) tlong) tint))))

abbrev body : statement :=
  (.Ssequence
    (.Sloop
      (.Ssequence
        (sk
          (.Sset id.«v»
            (.Efield
              (.Ederef
                (.Ecast (pv id.«g») (tptr (Tstruct id.«_1406» noattr)))
                (Tstruct id.«_1406» noattr))
              id.«v»
              (tptr tulong))))
        (.Ssequence
          (sk
            (.Sset id.«d»
              (.Efield
                (.Ederef
                  (.Ecast (pv id.«g») (tptr (Tstruct id.«_1406» noattr)))
                  (Tstruct id.«_1406» noattr))
                id.«d»
                (tptr tint))))
          (sk
            (.Sset id.«e»
              (.Efield
                (.Ederef
                  (.Ecast (pv id.«g») (tptr (Tstruct id.«_1406» noattr)))
                  (Tstruct id.«_1406» noattr))
                id.«e»
                (tptr tint))))))
      (sk .Sbreak))
    (.Ssequence
      (dynalloc1 id.«nausparse:work1_sz» id.«nausparse:work1» tint
        (tv id.«n»)
        (idOf 703)
        (idOf 704)
        id.«nausparse:__stringlit_6»
        10)
      (.Ssequence
        (dynalloc1 id.«nausparse:work2_sz» id.«nausparse:work2» tint
          (tv id.«n»)
          (idOf 705)
          (idOf 706)
          id.«nausparse:__stringlit_6»
          10)
        (.Ssequence
          (dynalloc1 id.«nausparse:work3_sz» id.«nausparse:work3» tint
            (tv id.«n»)
            (idOf 707)
            (idOf 708)
            id.«nausparse:__stringlit_6»
            10)
          (.Ssequence
            (dynalloc1 id.«nausparse:work4_sz» id.«nausparse:work4» tint
              (tv id.«n»)
              (idOf 709)
              (idOf 710)
              id.«nausparse:__stringlit_6»
              10)
            (.Ssequence
              (sk
                (.Scall none
                  (.Evar id.«nausparse:preparemarks1» (tfun [tulong] Tvoid))
                  [(tv id.«n»)]))
              (.Ssequence
                (sk
                  (.Scall none
                    (.Evar id.«nausparse:preparemarks2» (tfun [tulong] Tvoid))
                    [(tv id.«n»)]))
                (.Ssequence
                  (sk (.Sset id.«longcode» (.Ecast (.Ederef (pi id.«numcells») tint) tlong)))
                  (.Ssequence
                    (sk (.Sset id.«nactive» (ci 0 tint)))
                    (.Ssequence
                      (.Ssequence (sk (.Sset id.«i» (.Eunop .Oneg (ci 1 tint) tint))) queueLoop)
                      (.Ssequence
                        (sk
                          (.Sifthenelse
                            (.Ebinop .Oeq (tv id.«nactive») (ci 0 tint) tint)
                            (.Ssequence
                              (sk
                                (.Sassign
                                  (.Ederef (pi id.«code») tint)
                                  (.Ecast
                                    (.Ebinop .Omod
                                      (.Etempvar id.«longcode» tlong)
                                      (ci 32767 tint)
                                      tlong)
                                    tint)))
                              (.Sreturn none))
                            .Sskip))
                        (.Ssequence
                          (.Ssequence (sk (.Sset id.«i» (ci 0 tint))) startLoop)
                          (.Ssequence dist (.Ssequence mainLoop finish))))))))))))))

kernel_rfl body_eq : sparse.body.refine_sg = body

end NautyVerified.Proofs.Sparse.Refine

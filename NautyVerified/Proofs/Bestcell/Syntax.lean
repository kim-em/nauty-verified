import NautyVerified.Proofs.Updatecan.Syntax
import NautyVerified.Proofs.Set.Global
import NautyVerified.Logic.ForFrom

/-!
# `bestcell`, factored

The Clight of naugraph.c's static `bestcell`, in named pieces; `body_eq` pins
it to `dense.body.«naugraph:bestcell»`.
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk pv)
open NautyVerified.Proofs.Updatecan (tv labAt row)
open NautyVerified.Proofs.Alloc (gat)

namespace id
abbrev g : Common.AST.ident := dense.id.g
abbrev lab : Common.AST.ident := dense.id.lab
abbrev ptn : Common.AST.ident := dense.id.ptn
abbrev level : Common.AST.ident := dense.id.level
abbrev tc_level : Common.AST.ident := dense.id.tc_level
abbrev m : Common.AST.ident := dense.id.m
abbrev n : Common.AST.ident := dense.id.n
abbrev i : Common.AST.ident := dense.id.i
abbrev gp : Common.AST.ident := dense.id.gp
abbrev sw1 : Common.AST.ident := dense.id.setword1
abbrev sw2 : Common.AST.ident := dense.id.setword2
abbrev v1 : Common.AST.ident := dense.id.v1
abbrev v2 : Common.AST.ident := dense.id.v2
abbrev nnt : Common.AST.ident := dense.id.nnt
abbrev es : Common.AST.ident := dense.id.es_
abbrev wp : Common.AST.ident := dense.id.«naugraph:workperm»
abbrev wsz : Common.AST.ident := dense.id.«naugraph:workperm_sz»
abbrev ws : Common.AST.ident := dense.id.«naugraph:workset»
abbrev wssz : Common.AST.ident := dense.id.«naugraph:workset_sz»
abbrev bk : Common.AST.ident := dense.id.«naugraph:bucket»
abbrev bksz : Common.AST.ident := dense.id.«naugraph:bucket_sz»
abbrev bit : Common.AST.ident := dense.id.«naugraph:bit»
abbrev msg : Common.AST.ident := dense.id.«naugraph:__stringlit_5»
abbrev t3 : Common.AST.ident := idOf 703
abbrev t4 : Common.AST.ident := idOf 704
abbrev t5 : Common.AST.ident := idOf 705
abbrev t6 : Common.AST.ident := idOf 706
abbrev t7 : Common.AST.ident := idOf 707
abbrev t8 : Common.AST.ident := idOf 708
abbrev t9 : Common.AST.ident := idOf 709
abbrev t10 : Common.AST.ident := idOf 710
abbrev t11 : Common.AST.ident := idOf 711
abbrev t12 : Common.AST.ident := idOf 712
abbrev t13 : Common.AST.ident := idOf 713
abbrev t14 : Common.AST.ident := idOf 714
abbrev t15 : Common.AST.ident := idOf 715
end id

abbrev lv (x : Common.AST.ident) : expr := .Etempvar x tulong

/-- `ptn[e]`. -/
abbrev ptnAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.ptn (tptr tint)) e (tptr tint)) tint

/-- `ptn[i] > level`. -/
abbrev ptnGt : expr := .Ebinop .Ogt (ptnAt (tv id.i)) (tv id.level) tint

/-- The `workset` pointer, `(set *) workset`. -/
abbrev wsP : expr := .Ecast (.Evar id.ws (tptr tulong)) (tptr tulong)

/-- `workset[e]`. -/
abbrev wsAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar id.ws (tptr tulong)) e (tptr tulong)) tulong

/-- `++i` until `i` holds the cell end: `while (ptn[i] > level) ++i;` -/
abbrev skipCell : statement :=
  .Sloop
    (.Ssequence (sk (.Sifthenelse ptnGt .Sskip .Sbreak))
      (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))))
    .Sskip

/-- `if (ptn[i] > level) { workperm[nnt++] = i; skipCell }` -/
abbrev startBody : statement :=
  sk (.Sifthenelse ptnGt
    (.Ssequence
      (.Ssequence
        (.Ssequence (sk (.Sset id.t10 (tv id.nnt)))
          (.Sset id.nnt (.Ebinop .Oadd (tv id.t10) (ci 1 tint) tint)))
        (.Sassign (gat id.wp (tv id.t10)) (tv id.i)))
      skipCell)
    .Sskip)

/-- `while (i < n) { startBody; ++i; }` -/
abbrev starts : statement :=
  .Sloop
    (.Ssequence (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak))
      (.Ssequence startBody (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint)))))
    .Sskip

/-- `i = nnt = 0;` -/
abbrev init : statement :=
  .Ssequence
    (.Ssequence (sk (.Sset id.t9 (.Ecast (ci 0 tint) tint))) (.Sset id.nnt (tv id.t9)))
    (.Sset id.i (tv id.t9))

/-- `if (nnt == 0) return n;` -/
abbrev ret0 : statement :=
  sk (.Sifthenelse (.Ebinop .Oeq (tv id.nnt) (ci 0 tint) tint) (sk (.Sreturn (some (tv id.n))))
    .Sskip)

/-- `for (i = nnt; --i >= 0;) bucket[i] = 0;` -/
abbrev clear : statement :=
  .Ssequence (sk (.Sset id.i (tv id.nnt)))
    (.Sloop
      (.Ssequence
        (.Ssequence
          (.Ssequence (sk (.Sset id.t11 (.Ecast (.Ebinop .Osub (tv id.i) (ci 1 tint) tint) tint)))
            (.Sset id.i (tv id.t11)))
          (.Sifthenelse (.Ebinop .Oge (tv id.t11) (ci 0 tint) tint) .Sskip .Sbreak))
        (sk (.Sassign (gat id.bk (tv id.i)) (ci 0 tint))))
      .Sskip)

/-- `EMPTYSET(workset, m)` -/
abbrev clearWS : statement := Set.emptySetG id.ws id.m id.es id.t12

/-- `ADDELEMENT(workset, lab[i])` -/
abbrev addLab : statement := Set.addElementG id.ws id.bit (labAt (tv id.i))

/-- `do { ++i; ADDELEMENT(workset, lab[i]); } while (ptn[i] > level);` -/
abbrev addCell : statement :=
  .Sloop
    (.Ssequence (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))) addLab)
    (sk (.Sifthenelse ptnGt .Sskip .Sbreak))

/-- `gp[e]`. -/
abbrev gpAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (pv id.gp) e (tptr tulong)) tulong

/-- `for (i = m; --i >= 0;) { setword1 |= …; setword2 |= …; }` -/
abbrev orLoop : statement :=
  .Ssequence (sk (.Sset id.i (tv id.m)))
    (.Sloop
      (.Ssequence
        (.Ssequence
          (.Ssequence (sk (.Sset id.t14 (.Ecast (.Ebinop .Osub (tv id.i) (ci 1 tint) tint) tint)))
            (.Sset id.i (tv id.t14)))
          (.Sifthenelse (.Ebinop .Oge (tv id.t14) (ci 0 tint) tint) .Sskip .Sbreak))
        (.Ssequence
          (sk (.Sset id.sw1 (.Ebinop .Oor (lv id.sw1)
            (.Ebinop .Oand (wsAt (tv id.i)) (gpAt (tv id.i)) tulong) tulong)))
          (sk (.Sset id.sw2 (.Ebinop .Oor (lv id.sw2)
            (.Ebinop .Oand (wsAt (tv id.i)) (.Eunop .Onotint (gpAt (tv id.i)) tulong) tulong) tulong)))))
      .Sskip)

/-- `++bucket[e]`. -/
abbrev bump (e : expr) : statement :=
  sk (.Sassign (gat id.bk e) (.Ebinop .Oadd (gat id.bk e) (ci 1 tint) tint))

/-- `if (setword1 != 0 && setword2 != 0) { ++bucket[v1]; ++bucket[v2]; }` -/
abbrev test : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Ebinop .One (lv id.sw1) (ci 0 tint) tint)
      (sk (.Sset id.t15 (.Ecast (.Ebinop .One (lv id.sw2) (ci 0 tint) tint) tbool)))
      (.Sset id.t15 (ci 0 tint))))
    (.Sifthenelse (tv id.t15) (.Ssequence (bump (tv id.v1)) (bump (tv id.v2))) .Sskip)

/-- The body of the `v1` loop. -/
abbrev pair : statement :=
  .Ssequence (sk (.Sset id.gp (row id.g (labAt (gat id.wp (tv id.v1))))))
    (.Ssequence
      (.Ssequence
        (.Ssequence (sk (.Sset id.t13 (.Ecast (ci 0 tint) tulong))) (.Sset id.sw2 (lv id.t13)))
        (.Sset id.sw1 (lv id.t13)))
      (.Ssequence orLoop test))

/-- `for (v1 = 0; v1 < v2; ++v1) pair` -/
abbrev pairs : statement := NautyVerified.Logic.forLoop id.v1 id.v2 pair

/-- The body of the `v2` loop. -/
abbrev rowBody : statement :=
  .Ssequence clearWS
    (.Ssequence (sk (.Sset id.i (.Ebinop .Osub (gat id.wp (tv id.v2)) (ci 1 tint) tint)))
      (.Ssequence addCell pairs))

/-- `for (v2 = 1; v2 < nnt; ++v2) rowBody` -/
abbrev rows : statement := NautyVerified.Logic.forLoopFrom 1 id.v2 id.nnt rowBody

/-- `if (bucket[i] > v2) { v1 = i; v2 = bucket[i]; }` -/
abbrev amBody : statement :=
  sk (.Sifthenelse (.Ebinop .Ogt (gat id.bk (tv id.i)) (tv id.v2) tint)
    (.Ssequence (sk (.Sset id.v1 (tv id.i))) (sk (.Sset id.v2 (gat id.bk (tv id.i)))))
    .Sskip)

/-- `for (i = 1; i < nnt; ++i) amBody` -/
abbrev amLoop : statement := NautyVerified.Logic.forLoopFrom 1 id.i id.nnt amBody

/-- The argmax and `return workperm[v1];` -/
abbrev argmax : statement :=
  .Ssequence (sk (.Sset id.v1 (ci 0 tint)))
    (.Ssequence (sk (.Sset id.v2 (gat id.bk (ci 0 tint))))
      (.Ssequence amLoop (sk (.Sreturn (some (.Ecast (gat id.wp (tv id.v1)) tint))))))

abbrev body : statement :=
  .Ssequence (Alloc.dynalloc1 id.wsz id.wp tint (tv id.n) id.t3 id.t4 id.msg 9)
    (.Ssequence (Alloc.dynalloc1 id.wssz id.ws tulong (tv id.m) id.t5 id.t6 id.msg 9)
      (.Ssequence
        (Alloc.dynalloc1 id.bksz id.bk tint (.Ebinop .Oadd (tv id.n) (ci 2 tint) tint) id.t7 id.t8 id.msg 9)
        (.Ssequence init
          (.Ssequence starts
            (.Ssequence ret0
              (.Ssequence clear (.Ssequence rows argmax)))))))

kernel_rfl body_eq : dense.body.«naugraph:bestcell» = body

end NautyVerified.Proofs.Bestcell

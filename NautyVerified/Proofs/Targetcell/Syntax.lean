import NautyVerified.Proofs.Bestcell.Syntax

/-!
# `targetcell`, factored

The Clight of naugraph.c's `targetcell`, in named pieces; `body_eq` pins it to
`dense.body.targetcell`. `Block.bestcell` and `Block.targetcell` are the
functions' blocks.
-/

namespace NautyVerified.Program

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source

namespace Block
/-- naugraph.c's static `bestcell`. -/
def bestcell : Common.Values.block := PArith.BinPos.Pos.of_nat 249
/-- naugraph.c's `targetcell`. -/
def targetcell : Common.Values.block := PArith.BinPos.Pos.of_nat 127
end Block

kernel_rfl find_bestcell :
  Genv.find_symbol ge.genv_genv dense.id.«naugraph:bestcell» = some Block.bestcell
kernel_rfl funct_bestcell :
  Genv.find_funct_ptr ge.genv_genv Block.bestcell = some (.Internal dense.fn.«naugraph:bestcell»)
kernel_rfl find_targetcell : Genv.find_symbol ge.genv_genv dense.id.targetcell = some Block.targetcell
kernel_rfl funct_targetcell :
  Genv.find_funct_ptr ge.genv_genv Block.targetcell = some (.Internal dense.fn.targetcell)

end NautyVerified.Program

namespace NautyVerified.Proofs.Targetcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Updatecan (tv)
open NautyVerified.Proofs.Bestcell (ptnAt)

namespace id
abbrev g : Common.AST.ident := dense.id.g
abbrev lab : Common.AST.ident := dense.id.lab
abbrev ptn : Common.AST.ident := dense.id.ptn
abbrev level : Common.AST.ident := dense.id.level
abbrev tc_level : Common.AST.ident := dense.id.tc_level
abbrev digraph : Common.AST.ident := dense.id.digraph
abbrev hint : Common.AST.ident := dense.id.hint
abbrev m : Common.AST.ident := dense.id.m
abbrev n : Common.AST.ident := dense.id.n
abbrev i : Common.AST.ident := dense.id.i
abbrev t3 : Common.AST.ident := idOf 703
abbrev t4 : Common.AST.ident := idOf 704
abbrev t5 : Common.AST.ident := idOf 705
abbrev t6 : Common.AST.ident := idOf 706
abbrev t7 : Common.AST.ident := idOf 707
end id

/-- `hint >= 0 && ptn[hint] > level && (hint == 0 || ptn[hint-1] <= level)` into `t7`. -/
abbrev hintTest : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Ebinop .Oge (tv id.hint) (ci 0 tint) tint)
      (sk (.Sset id.t6 (.Ecast (.Ebinop .Ogt (ptnAt (tv id.hint)) (tv id.level) tint) tbool)))
      (.Sset id.t6 (ci 0 tint))))
    (.Sifthenelse (tv id.t6)
      (sk (.Sifthenelse (.Ebinop .Oeq (tv id.hint) (ci 0 tint) tint)
        (sk (.Sset id.t7 (.Ecast (ci 1 tint) tbool)))
        (.Ssequence
          (sk (.Sset id.t7 (.Ecast (.Ebinop .Ole
            (ptnAt (.Ebinop .Osub (tv id.hint) (ci 1 tint) tint)) (tv id.level) tint) tbool)))
          (.Sset id.t7 (.Ecast (tv id.t7) tbool)))))
      (.Sset id.t7 (ci 0 tint)))

/-- `return bestcell(g, lab, ptn, level, tc_level, m, n);` -/
abbrev callBest : statement :=
  .Ssequence
    (sk (.Scall (some id.t3)
      (.Evar dense.id.«naugraph:bestcell»
        (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tint] tint))
      [.Etempvar id.g (tptr tulong), .Etempvar id.lab (tptr tint), .Etempvar id.ptn (tptr tint),
        tv id.level, tv id.tc_level, tv id.m, tv id.n]))
    (.Sreturn (some (tv id.t3)))

/-- `for (i = 0; i < n && ptn[i] <= level; ++i) {}` -/
abbrev scan : statement :=
  .Ssequence (sk (.Sset id.i (ci 0 tint)))
    (.Sloop
      (.Ssequence
        (.Ssequence
          (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint)
            (sk (.Sset id.t4 (.Ecast (.Ebinop .Ole (ptnAt (tv id.i)) (tv id.level) tint) tbool)))
            (.Sset id.t4 (ci 0 tint))))
          (.Sifthenelse (tv id.t4) .Sskip .Sbreak))
        .Sskip)
      (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))))

/-- `scan; return (i == n ? 0 : i);` -/
abbrev fallback : statement :=
  .Ssequence scan
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Oeq (tv id.i) (tv id.n) tint)
        (sk (.Sset id.t5 (.Ecast (ci 0 tint) tint)))
        (sk (.Sset id.t5 (.Ecast (tv id.i) tint)))))
      (.Sreturn (some (tv id.t5))))

abbrev body : statement :=
  .Ssequence hintTest
    (.Sifthenelse (tv id.t7) (sk (.Sreturn (some (tv id.hint))))
      (sk (.Sifthenelse (.Ebinop .Ole (tv id.level) (tv id.tc_level) tint) callBest fallback)))

kernel_rfl body_eq : dense.body.targetcell = body

end NautyVerified.Proofs.Targetcell

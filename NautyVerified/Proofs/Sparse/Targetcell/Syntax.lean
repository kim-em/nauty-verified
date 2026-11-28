import NautyVerified.Proofs.Targetcell.Syntax
import NautyVerified.Proofs.Sparse.Blocks

/-!
# `targetcell_sg`, factored

The Clight of nausparse.c's `targetcell_sg` is naugraph.c's `targetcell`
with the call to `bestcell` replaced by one to `bestcell_sg` (the shared
identifiers keep their numbers); `body_eq` pins it to
`sparse.body.targetcell_sg`.
-/

namespace NautyVerified.Proofs.Sparse

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source

namespace Block
/-- nausparse.c's static `bestcell_sg`. -/
def bestcell : Common.Values.block := PArith.BinPos.Pos.of_nat 16
/-- nausparse.c's `targetcell_sg`. -/
def targetcell : Common.Values.block := PArith.BinPos.Pos.of_nat 140
end Block

kernel_rfl find_bestcell :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:bestcell_sg» = some Block.bestcell
kernel_rfl funct_bestcell :
  Genv.find_funct_ptr sge.genv_genv Block.bestcell = some (.Internal sparse.fn.«nausparse:bestcell_sg»)
kernel_rfl find_targetcell :
  Genv.find_symbol sge.genv_genv sparse.id.targetcell_sg = some Block.targetcell
kernel_rfl funct_targetcell :
  Genv.find_funct_ptr sge.genv_genv Block.targetcell = some (.Internal sparse.fn.targetcell_sg)

end NautyVerified.Proofs.Sparse

namespace NautyVerified.Proofs.Sparse.Targetcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Updatecan (tv)
open NautyVerified.Proofs.Targetcell (hintTest fallback)

namespace id
export NautyVerified.Proofs.Targetcell.id (g lab ptn level tc_level digraph hint m n i t3 t4 t5 t6 t7)
end id

/-- `return bestcell_sg(g, lab, ptn, level, tc_level, m, n);` -/
abbrev callBest : statement :=
  .Ssequence
    (sk (.Scall (some id.t3)
      (.Evar sparse.id.«nausparse:bestcell_sg»
        (tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tint] tint))
      [.Etempvar id.g (tptr tulong), .Etempvar id.lab (tptr tint), .Etempvar id.ptn (tptr tint),
        tv id.level, tv id.tc_level, tv id.m, tv id.n]))
    (.Sreturn (some (tv id.t3)))

abbrev body : statement :=
  .Ssequence hintTest
    (.Sifthenelse (tv id.t7) (sk (.Sreturn (some (tv id.hint))))
      (sk (.Sifthenelse (.Ebinop .Ole (tv id.level) (tv id.tc_level) tint) callBest fallback)))

kernel_rfl body_eq : sparse.body.targetcell_sg = body

end NautyVerified.Proofs.Sparse.Targetcell

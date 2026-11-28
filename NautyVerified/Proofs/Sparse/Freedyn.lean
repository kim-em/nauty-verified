import NautyVerified.Proofs.Alloc.Dynfree
import NautyVerified.Program.Sparse
import NautyVerified.Proofs.Sparse.Isautom.Loops

/-!
# `nausparse_freedyn`

nausparse.c is compiled with `MAXN = 0`, so `nausparse_freedyn` runs
`DYNFREE` on its seven `DYNALLSTAT` pairs: `vmark1`, `vmark2` (`short`),
`work1` to `work4` (`int`) and `snwork` (`set`, the automorphism workspace
`sparsenauty` hands to `nauty`). `freedynSpec ds` (the dense `dynfreeSpec`,
for the sparse program): every pair ends at capacity 0 with a `NULL`
pointer, and only the pairs' globals and their allocated blocks change.
-/

namespace NautyVerified.Proofs.Sparse

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt FreeD dynfree seqR wp_dynfrees)

attribute [local instance] NautyEnv.sparse

namespace Block
def vmark2 : block := PArith.BinPos.Pos.of_nat 240
def vmark2Sz : block := PArith.BinPos.Pos.of_nat 322
def work2 : block := PArith.BinPos.Pos.of_nat 262
def work2Sz : block := PArith.BinPos.Pos.of_nat 339
def work3 : block := PArith.BinPos.Pos.of_nat 210
def work3Sz : block := PArith.BinPos.Pos.of_nat 289
def work4 : block := PArith.BinPos.Pos.of_nat 252
def work4Sz : block := PArith.BinPos.Pos.of_nat 333
def snwork : block := PArith.BinPos.Pos.of_nat 232
def snworkSz : block := PArith.BinPos.Pos.of_nat 312
end Block

kernel_rfl find_vmark2 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:vmark2» = some Block.vmark2
kernel_rfl find_vmark2Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:vmark2_sz» = some Block.vmark2Sz
kernel_rfl find_work2 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work2» = some Block.work2
kernel_rfl find_work2Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work2_sz» = some Block.work2Sz
kernel_rfl find_work3 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work3» = some Block.work3
kernel_rfl find_work3Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work3_sz» = some Block.work3Sz
kernel_rfl find_work4 :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work4» = some Block.work4
kernel_rfl find_work4Sz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:work4_sz» = some Block.work4Sz
kernel_rfl find_snwork :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:snwork» = some Block.snwork
kernel_rfl find_snworkSz :
  Genv.find_symbol sge.genv_genv sparse.id.«nausparse:snwork_sz» = some Block.snworkSz

/-- A function running `DYNFREE` on the pairs `ds` (`Top.dynfreeSpec`, for
the sparse program). -/
def freedynSpec (ds : List FreeD) : FunSpec where
  pre args m := args = [] ∧ FreeD.Ok m ds
  post _ m t _ m' := t = E0 ∧ (∀ d ∈ ds, ∀ c b', DynAt m' d.bp d.bs c 0 b') ∧
    Unch m m' (fun z => z ∈ FreeD.globals ds ∨ ∃ d ∈ ds, 0 < d.cap ∧ z = d.blk) ∧
    Mem.nextblock m' = Mem.nextblock m

/-- nausparse.c's pairs, with their capacities and blocks. -/
def sparseDs (c1 : Nat) (b1 : block) (c2 : Nat) (b2 : block) (w1 : Nat) (bw1 : block)
    (w2 : Nat) (bw2 : block) (w3 : Nat) (bw3 : block) (w4 : Nat) (bw4 : block) (s : Nat)
    (bsn : block) : List FreeD :=
  [⟨sparse.id.«nausparse:vmark1», sparse.id.«nausparse:vmark1_sz», Block.vmark1, Block.vmark1Sz,
     tshort, 2, c1, b1⟩,
   ⟨sparse.id.«nausparse:vmark2», sparse.id.«nausparse:vmark2_sz», Block.vmark2, Block.vmark2Sz,
     tshort, 2, c2, b2⟩,
   ⟨sparse.id.«nausparse:work1», sparse.id.«nausparse:work1_sz», Block.work1, Block.work1Sz,
     tint, 4, w1, bw1⟩,
   ⟨sparse.id.«nausparse:work2», sparse.id.«nausparse:work2_sz», Block.work2, Block.work2Sz,
     tint, 4, w2, bw2⟩,
   ⟨sparse.id.«nausparse:work3», sparse.id.«nausparse:work3_sz», Block.work3, Block.work3Sz,
     tint, 4, w3, bw3⟩,
   ⟨sparse.id.«nausparse:work4», sparse.id.«nausparse:work4_sz», Block.work4, Block.work4Sz,
     tint, 4, w4, bw4⟩,
   ⟨sparse.id.«nausparse:snwork», sparse.id.«nausparse:snwork_sz», Block.snwork, Block.snworkSz,
     tulong, 8, s, bsn⟩]

kernel_rfl body_freedyn : sparse.body.nausparse_freedyn =
  seqR [dynfree sparse.id.«nausparse:vmark1» sparse.id.«nausparse:vmark1_sz» tshort,
    dynfree sparse.id.«nausparse:vmark2» sparse.id.«nausparse:vmark2_sz» tshort,
    dynfree sparse.id.«nausparse:work1» sparse.id.«nausparse:work1_sz» tint,
    dynfree sparse.id.«nausparse:work2» sparse.id.«nausparse:work2_sz» tint,
    dynfree sparse.id.«nausparse:work3» sparse.id.«nausparse:work3_sz» tint,
    dynfree sparse.id.«nausparse:work4» sparse.id.«nausparse:work4_sz» tint,
    dynfree sparse.id.«nausparse:snwork» sparse.id.«nausparse:snwork_sz» tulong]

/-- The fourteen globals of `sparseDs` are distinct. -/
theorem sparseDs_glob (c1 : Nat) (b1 : block) (c2 : Nat) (b2 : block) (w1 : Nat) (bw1 : block)
    (w2 : Nat) (bw2 : block) (w3 : Nat) (bw3 : block) (w4 : Nat) (bw4 : block) (s : Nat)
    (bsn : block) :
    (FreeD.globals (sparseDs c1 b1 c2 b2 w1 bw1 w2 bw2 w3 bw3 w4 bw4 s bsn)).Pairwise (· ≠ ·) := by
  rw [show FreeD.globals (sparseDs c1 b1 c2 b2 w1 bw1 w2 bw2 w3 bw3 w4 bw4 s bsn) =
    [Block.vmark1Sz, Block.vmark1, Block.vmark2Sz, Block.vmark2, Block.work1Sz, Block.work1,
     Block.work2Sz, Block.work2, Block.work3Sz, Block.work3, Block.work4Sz, Block.work4,
     Block.snworkSz, Block.snwork] from rfl]
  decide

/-- The identifiers of `sparseDs` name its globals. -/
theorem sparseDs_sym (c1 : Nat) (b1 : block) (c2 : Nat) (b2 : block) (w1 : Nat) (bw1 : block)
    (w2 : Nat) (bw2 : block) (w3 : Nat) (bw3 : block) (w4 : Nat) (bw4 : block) (s : Nat)
    (bsn : block) : ∀ d ∈ sparseDs c1 b1 c2 b2 w1 bw1 w2 bw2 w3 bw3 w4 bw4 s bsn,
      Genv.find_symbol sge.genv_genv d.gs = some d.bs ∧
      Genv.find_symbol sge.genv_genv d.gp = some d.bp := by
  intro d hd
  simp only [sparseDs, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨find_vmark1Sz, find_vmark1⟩
  · exact ⟨find_vmark2Sz, find_vmark2⟩
  · exact ⟨find_work1Sz, find_work1⟩
  · exact ⟨find_work2Sz, find_work2⟩
  · exact ⟨find_work3Sz, find_work3⟩
  · exact ⟨find_work4Sz, find_work4⟩
  · exact ⟨find_snworkSz, find_snwork⟩

theorem freedyn_satisfies {xi : ExternalCalls} (c1 : Nat) (b1 : block) (c2 : Nat) (b2 : block)
    (w1 : Nat) (bw1 : block) (w2 : Nat) (bw2 : block) (w3 : Nat) (bw3 : block) (w4 : Nat)
    (bw4 : block) (s : Nat) (bsn : block) :
    Satisfies xi sge (.Internal sparse.fn.nausparse_freedyn)
      (freedynSpec (sparseDs c1 b1 c2 b2 w1 bw1 w2 bw2 w3 bw3 w4 bw4 s bsn)) := by
  let le0 := create_undef_temps sparse.fn.nausparse_freedyn.fn_temps
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧ le = le0 ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, le0, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hok⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [sparse.fn.nausparse_freedyn.fn_body_eq, body_freedyn]
    exact wp_dynfrees Alloc.noShadow_empty (sparseDs c1 b1 c2 b2 w1 bw1 w2 bw2 w3 bw3 w4 bw4 s bsn)
      _ hok (fun m' hD hu hnb => ⟨m', Isautom.free_empty m', rfl, hD, hu, hnb⟩)

end NautyVerified.Proofs.Sparse

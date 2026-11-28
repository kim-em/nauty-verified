import NautyVerified.Proofs.Top.NautyEnv
import NautyVerified.Proofs.Alloc.DynSeq
import NautyVerified.Proofs.Search.Ops

/-!
# `nauty()`'s nine `DYNALLOC1`s

`allocDs M n`: the nine `DYNALLSTAT` pairs `nauty()` allocates (`defltwork`
`2m` setwords, `fixedpts` and `active` `m`, `workperm`, `firstlab`,
`canonlab` `n` ints, `firstcode`, `canoncode` `n + 2` shorts, `firsttc`
`n + 2` ints), sized by the globals `nauty:m` and `nauty:n`. `tAlloc_eq`:
the stage `tAlloc` is their run followed by `tTc`. `wp_tAlloc`: from capacity
0, the run leaves each pair allocated with at least its size in a block not
valid before, zero-filled (`Alloc.wp_dynSeq`).
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt DynD dynSeq)
open NautyVerified.Proofs.Search (IntAt)

set_option linter.unusedSimpArgs false

/-- `nauty:m`, `nauty:n`, `2 * nauty:m` and `nauty:n + 2` as `int` expressions. -/
abbrev gM : expr := .Evar dense.id.«nauty:m» tint
abbrev gN : expr := .Evar dense.id.«nauty:n» tint

def allocDs (M n : Nat) : List DynD :=
  [⟨dense.id.«nauty:defltwork_sz», dense.id.«nauty:defltwork», Block.nautyDefltworkSz,
     Block.nautyDefltwork, tulong, 8, .Ebinop .Omul (ci 2 tint) gM tint, 2 * M, idOf 709, idOf 710⟩,
   ⟨dense.id.«nauty:fixedpts_sz», dense.id.«nauty:fixedpts», Block.nautyFixedptsSz,
     Block.nautyFixedpts, tulong, 8, gM, M, idOf 711, idOf 712⟩,
   ⟨dense.id.«nauty:active_sz», dense.id.«nauty:active», Block.nautyActiveSz, Block.nautyActive,
     tulong, 8, gM, M, idOf 713, idOf 714⟩,
   ⟨dense.id.«nauty:workperm_sz», dense.id.«nauty:workperm», Block.nautyWorkpermSz,
     Block.nautyWorkperm, tint, 4, gN, n, idOf 715, idOf 716⟩,
   ⟨dense.id.«nauty:firstlab_sz», dense.id.«nauty:firstlab», Block.nautyFirstlabSz,
     Block.nautyFirstlab, tint, 4, gN, n, idOf 717, idOf 718⟩,
   ⟨dense.id.«nauty:canonlab_sz», dense.id.«nauty:canonlab», Block.nautyCanonlabSz,
     Block.nautyCanonlab, tint, 4, gN, n, idOf 719, idOf 720⟩,
   ⟨dense.id.«nauty:firstcode_sz», dense.id.«nauty:firstcode», Block.nautyFirstcodeSz,
     Block.nautyFirstcode, tshort, 2, .Ebinop .Oadd gN (ci 2 tint) tint, n + 2, idOf 721, idOf 722⟩,
   ⟨dense.id.«nauty:canoncode_sz», dense.id.«nauty:canoncode», Block.nautyCanoncodeSz,
     Block.nautyCanoncode, tshort, 2, .Ebinop .Oadd gN (ci 2 tint) tint, n + 2, idOf 723, idOf 724⟩,
   ⟨dense.id.«nauty:firsttc_sz», dense.id.«nauty:firsttc», Block.nautyFirsttcSz,
     Block.nautyFirsttc, tint, 4, .Ebinop .Oadd gN (ci 2 tint) tint, n + 2, idOf 725, idOf 726⟩]

theorem tAlloc_eq (M n : Nat) :
    Nauty.tAlloc = dynSeq dense.id.«nauty:__stringlit_6» 6 (allocDs M n) Nauty.tTc := rfl

/-- An `int` global read in a memory that left it alone. -/
theorem eval_gint {le : temp_env} {m m' : mem} {S : block → Prop} {id : ident} {b : block}
    {v : Int} (he : PTree.get id (nEnv bI : env) = none)
    (hf : Genv.find_symbol ge.genv_genv id = some b) (h : IntAt m b v)
    (hu : Unch m m' S) (hb : ¬ S b) :
    Exec.evalExpr ge (nEnv bI) le m' (.Evar id tint) = some (.Vint (ir v)) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, he, hf,
    Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  rw [hu.load _ _ _ hb]
  exact h.load

variable {xi : ExternalCalls} in
/-- `nauty()`'s nine allocations from capacity 0. -/
theorem wp_tAlloc {Q : Post} {le : temp_env} {m : mem} {M n : Nat}
    (hM : IntAt m Search.Block.m M) (hn : IntAt m Search.Block.n n) (hM0 : 0 < M) (hn0 : 0 < n)
    (hnl : n < 1073741824) (hMl : M < 33554432)
    (hD : ∀ d ∈ allocDs M n, ∀ b, DynAt m d.bp d.bs d.c 0 b)
    (hQ : ∀ le' m' (cb : Nat → Nat × block),
      (∀ i (h : i < (allocDs M n).length), DynAt m' (allocDs M n)[i].bp (allocDs M n)[i].bs
        (allocDs M n)[i].c (cb i).1 (cb i).2 ∧ (allocDs M n)[i].n ≤ (cb i).1 ∧
        ¬ Mem.valid_block m (cb i).2 ∧ Alloc.Zeros m' (cb i).2 ((allocDs M n)[i].c * (cb i).1)) →
      (∀ i j, i < j → j < (allocDs M n).length → (cb i).2 ≠ (cb j).2) →
      Unch m m' (fun z => z ∈ DynD.globals (allocDs M n) ∨ ¬ Mem.valid_block m z) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ k, (∀ d ∈ allocDs M n, k ≠ d.t1 ∧ k ≠ d.t2) → PTree.get k le' = PTree.get k le) →
      Wp xi ge dense.fn.nauty Nauty.tTc Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.tAlloc Q (nEnv bI) le m := by
  rw [tAlloc_eq M n]
  let P : block → Prop := fun z => z = Search.Block.m ∨ z = Search.Block.n
  refine Alloc.wp_dynSeq Nauty.tTc P noShadow_nEnv (allocDs M n) le m ?_ hD
    (by show List.Pairwise _ (DynD.globals (allocDs 0 0)); decide) ?_ ?_ ?_ hQ
  · simp only [allocDs, List.forall_mem_cons, List.forall_mem_nil, and_true]
    refine ⟨DynD.Ok.mk (find_nautyDefltworkSz) find_nautyDefltwork rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega),
      DynD.Ok.mk (find_nautyFixedptsSz) find_nautyFixedpts rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega),
      DynD.Ok.mk (find_nautyActiveSz) find_nautyActive rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega),
      DynD.Ok.mk (find_nautyWorkpermSz) find_nautyWorkperm rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega),
      DynD.Ok.mk (find_nautyFirstlabSz) find_nautyFirstlab rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega),
      DynD.Ok.mk (find_nautyCanonlabSz) find_nautyCanonlab rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega),
      DynD.Ok.mk (find_nautyFirstcodeSz) find_nautyFirstcode rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega),
      DynD.Ok.mk (find_nautyCanoncodeSz) find_nautyCanoncode rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega),
      DynD.Ok.mk (find_nautyFirsttcSz) find_nautyFirsttc rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega), ?_⟩
    intro _ h; cases h
  · intro d hd
    simp only [allocDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  · rintro z (rfl | rfl)
    · exact Alloc.valid_of_access hM.writable
    · exact Alloc.valid_of_access hn.writable
  · intro d hd le' m' S hu hS
    have hm' := eval_gint (bI := bI) (le := le') rfl Search.find_m hM hu (fun h => hS _ h (.inl rfl))
    have hn' := eval_gint (bI := bI) (le := le') rfl Search.find_n hn hu (fun h => hS _ h (.inr rfl))
    simp only [allocDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Exec.evalExpr, gM] at hm' ⊢
      simp only [hm', typeof, cop]
      rw [show Lib.Integers.Int.repr (zOfInt 2) = ir 2 from rfl, ir_mul, Int.natCast_mul]; rfl
    · exact hm'
    · exact hm'
    · exact hn'
    · exact hn'
    · exact hn'
    · simp only [Exec.evalExpr, gN] at hn' ⊢
      simp only [hn', typeof, cop]
      rw [show Lib.Integers.Int.repr (zOfInt 2) = ir 2 from rfl, ir_add]; rfl
    · simp only [Exec.evalExpr, gN] at hn' ⊢
      simp only [hn', typeof, cop]
      rw [show Lib.Integers.Int.repr (zOfInt 2) = ir 2 from rfl, ir_add]; rfl
    · simp only [Exec.evalExpr, gN] at hn' ⊢
      simp only [hn', typeof, cop]
      rw [show Lib.Integers.Int.repr (zOfInt 2) = ir 2 from rfl, ir_add]; rfl

end NautyVerified.Proofs.Top

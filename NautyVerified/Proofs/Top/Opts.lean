import NautyVerified.Proofs.Top.NautyTc
import NautyVerified.Proofs.Top.Head

/-!
# `nauty()`'s option copies

`optF fld ty`: `options->fld`. `eval_optF` reads it, and `wp_gset` stores a
value into a scalar global of any by-value type. `wp_tOpts` runs the copies
of `options` into nauty.c's globals (`tOpts`), with the pinned options
(`OptionsAt`): afterwards the globals hold what `Fixed` needs (`OptsDone`).
`wp_tOptsG` is the same over any `NautyEnv` and `TopEnv`, the options at any
block (`OptionsAtG`); `wp_tOpts` is its dense instance.
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (FieldAt IntAt PtrAt)
open NautyVerified.Proofs.Harness (OptionsAt)

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- `g = rhs` for a scalar global `g` of by-value type `ty`. -/
theorem wp_gset {ge : genv} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {g : ident}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {b : block}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some b)
    (hacc : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hw : Mem.valid_access m chunk b (zOfInt 0) .Writable) {rhs : expr} {v : val}
    (hr : Exec.evalExpr ge e le m rhs = some v) (hrt : typeof rhs = ty)
    (hc : Cfrontend.Cop.sem_cast v ty ty m = some v) (hlr : Val.load_result chunk v = v)
    (hQ : ∀ m', FieldAt m' chunk b 0 v → Unch m m' (· = b) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ c z o p, Mem.valid_access m c z o p → Mem.valid_access m' c z o p) →
      (∀ z o k p, Mem.perm m z o k p → Mem.perm m' z o k p) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar g ty) rhs) Q e le m := by
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ v hw
  apply wp_assign_eval
  simp only [hr, hrt, hc]
  simp only [Exec.evalLvalue, Exec.lvalOfVar, hge, hg, typeof, Exec.assignLoc]
  simp only [hacc]
  simp only [Mem.storev, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  rw [hc]
  simp only [hst]
  exact hQ m' ⟨by rw [Mem.load_store_same _ _ _ _ _ _ hst, hlr],
    Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hw⟩ (Unch.store hst rfl)
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)
    (fun c z o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ h)
    (fun z o k p h => Mem.perm_store_1 _ _ _ _ _ _ hst _ _ _ _ h)

/-- A list of scalar facts `(chunk, block, value)` at offset 0. -/
def Facts (m : mem) (L : List (memory_chunk × block × val)) : Prop :=
  ∀ x ∈ L, FieldAt m x.1 x.2.1 0 x.2.2

theorem Facts.nil (m : mem) : Facts m [] := fun _ h => absurd h (by simp)

theorem Facts.step {m m' : mem} {L : List (memory_chunk × block × val)} {c : memory_chunk}
    {b : block} {v : val} (hF : Facts m L) (hu : Unch m m' (· = b))
    (hne : ∀ x ∈ L, x.2.1 ≠ b) (hb : FieldAt m' c b 0 v) : Facts m' ((c, b, v) :: L) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hb
  · exact (hF x hx).unch hu (hne x hx)

theorem Facts.get {m : mem} {L : List (memory_chunk × block × val)} (hF : Facts m L)
    {c : memory_chunk} {b : block} {v : val} (h : (c, b, v) ∈ L) : FieldAt m c b 0 v := hF _ h

/-- The globals `tOpts` writes, with their chunks. -/
def optTargets : List (memory_chunk × block) :=
  [(.Mint64, Search.Block.orbits), (.Mint64, Search.Block.stats), (.Mint32, Search.Block.getcanon),
   (.Mint32, Search.Block.digraph), (.Mint32, Search.Block.writeautoms),
   (.Mint32, Search.Block.domarkers), (.Mint32, Search.Block.cartesian),
   (.Mint32, Search.Block.doschreier), (.Mint32, Search.Block.linelength),
   (.Mint32, Search.Block.tcLevel), (.Mint64, Search.Block.outfile),
   (.Mint64, Search.Block.usernodeproc), (.Mint64, Search.Block.userautomproc),
   (.Mint64, Search.Block.userlevelproc), (.Mint64, Search.Block.usercanonproc),
   (.Mint64, Search.Block.invarproc), (.Mint32, Search.Block.mininvarlevel),
   (.Mint32, Search.Block.maxinvarlevel), (.Mint32, Search.Block.invararg)]

/-- What the option copies leave in nauty.c's globals. -/
def optFacts (bo bst : block) : List (memory_chunk × block × val) :=
  [(.Mint32, Search.Block.invararg, .Vint (ir 0)), (.Mint32, Search.Block.maxinvarlevel, .Vint (ir 1)),
   (.Mint32, Search.Block.mininvarlevel, .Vint (ir 0)), (.Mint64, Search.Block.invarproc, Vnullptr),
   (.Mint64, Search.Block.usercanonproc, Vnullptr), (.Mint64, Search.Block.userlevelproc, Vnullptr),
   (.Mint64, Search.Block.userautomproc, .Vptr Harness.Block.emitGenerator Ptrofs.zero),
   (.Mint64, Search.Block.usernodeproc, Vnullptr),
   (.Mint64, Search.Block.outfile, .Vptr Harness.Block.dummyfile Ptrofs.zero),
   (.Mint32, Search.Block.tcLevel, .Vint (ir 100)), (.Mint32, Search.Block.linelength, .Vint (ir 78)),
   (.Mint32, Search.Block.doschreier, .Vint (ir 0)), (.Mint32, Search.Block.cartesian, .Vint (ir 0)),
   (.Mint32, Search.Block.domarkers, .Vint (ir 0)), (.Mint32, Search.Block.writeautoms, .Vint (ir 0)),
   (.Mint32, Search.Block.digraph, .Vint (ir 0)), (.Mint32, Search.Block.getcanon, .Vint (ir 1)),
   (.Mint64, Search.Block.stats, .Vptr bst Ptrofs.zero), (.Mint64, Search.Block.orbits, .Vptr bo Ptrofs.zero)]

section Generic

variable {ge : genv} [E : NautyEnv ge] [T : TopEnv ge]

/-- `optTargets` in any program, with the blocks of `E`. -/
def optTargetsG : List (memory_chunk × block) :=
  [(.Mint64, E.orbits), (.Mint64, E.stats), (.Mint32, E.getcanon),
   (.Mint32, E.digraph), (.Mint32, E.writeautoms),
   (.Mint32, E.domarkers), (.Mint32, E.cartesian),
   (.Mint32, E.doschreier), (.Mint32, E.linelength),
   (.Mint32, E.tcLevel), (.Mint64, E.outfile),
   (.Mint64, E.usernodeproc), (.Mint64, E.userautomproc),
   (.Mint64, E.userlevelproc), (.Mint64, E.usercanonproc),
   (.Mint64, E.invarproc), (.Mint32, E.mininvarlevel),
   (.Mint32, E.maxinvarlevel), (.Mint32, E.invararg)]

/-- `optFacts` in any program: `outfile` and `userautomproc` are `bout` and `bua`. -/
def optFactsG (bout bua bo bst : block) : List (memory_chunk × block × val) :=
  [(.Mint32, E.invararg, .Vint (ir 0)), (.Mint32, E.maxinvarlevel, .Vint (ir 1)),
   (.Mint32, E.mininvarlevel, .Vint (ir 0)), (.Mint64, E.invarproc, Vnullptr),
   (.Mint64, E.usercanonproc, Vnullptr), (.Mint64, E.userlevelproc, Vnullptr),
   (.Mint64, E.userautomproc, .Vptr bua Ptrofs.zero),
   (.Mint64, E.usernodeproc, Vnullptr),
   (.Mint64, E.outfile, .Vptr bout Ptrofs.zero),
   (.Mint32, E.tcLevel, .Vint (ir 100)), (.Mint32, E.linelength, .Vint (ir 78)),
   (.Mint32, E.doschreier, .Vint (ir 0)), (.Mint32, E.cartesian, .Vint (ir 0)),
   (.Mint32, E.domarkers, .Vint (ir 0)), (.Mint32, E.writeautoms, .Vint (ir 0)),
   (.Mint32, E.digraph, .Vint (ir 0)), (.Mint32, E.getcanon, .Vint (ir 1)),
   (.Mint64, E.stats, .Vptr bst Ptrofs.zero), (.Mint64, E.orbits, .Vptr bo Ptrofs.zero)]

/-- `∀ x ∈ L, x.2.1 ≠ b` for a list literal of blocks of a `NautyEnv`. -/
macro "facts_ne" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, ne_eq]
  repeat' apply And.intro
  all_goals env_ne))

/-- `E.x ∈ optTargetsG.map Prod.snd`. -/
macro "tgt_mem" : tactic => `(tactic| simp only [optTargetsG, List.map_cons, List.map_nil, List.mem_cons,
  true_or, or_true])

set_option maxHeartbeats 2000000 in
/-- The option copies (`tOpts`), the options at `bo` (`OptionsAtG`), in any program. -/
theorem wp_tOptsG {Q : Post} {le : temp_env} {m : mem} {bo bst bc : block} {bopt bout bua bdg : block}
    (hopt : PTree.get dense.id.«options» le = some (.Vptr bopt Ptrofs.zero))
    (horb : PTree.get dense.id.«orbits_arg» le = some (.Vptr bo Ptrofs.zero))
    (hsta : PTree.get dense.id.«stats_arg» le = some (.Vptr bst Ptrofs.zero))
    (hcan : PTree.get dense.id.«canong_arg» le = some (.Vptr bc Ptrofs.zero))
    (hO : OptionsAtG m bopt bout bua bdg) (hbo : ∀ x ∈ optTargetsG, x.2 ≠ bopt)
    (hW : ∀ x ∈ optTargetsG, Mem.valid_access m x.1 x.2 (zOfInt 0) .Writable)
    (hdum : Mem.perm m bout (zOfInt 0) .Cur .Nonempty)
    (hbc : Mem.perm m bc (zOfInt 0) .Cur .Nonempty)
    (hQ : ∀ le' m', Facts m' (optFactsG bout bua bo bst) →
      Unch m m' (fun z => z ∈ optTargetsG.map Prod.snd) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 727 → x ≠ idOf 728 → x ≠ idOf 729 → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tPtn Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.tOpts Q (nEnv bI) le m := by
  have gw : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m c b (zOfInt 0) .Writable :=
    fun c b h => hW (c, b) h
  have hbo' : ∀ b, b ∈ optTargetsG.map Prod.snd → b ≠ bopt := fun b hb => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb; exact hbo x hx
  simp only [Nauty.tOpts]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint64) rfl E.find_orbits rfl (gw _ _ (by simp [optTargetsG]))
    (show Exec.evalExpr ge (nEnv bI) le m (Refine.pi dense.id.«orbits_arg») = _ from horb) rfl rfl rfl ?_
  intro m1 f1 u1 g1 a1 p1
  have F1 := (Facts.nil m).step u1 (by simp) f1
  have O1 := OptionsAtG.unch hO u1 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W1 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m1 c b (zOfInt 0) .Writable :=
    fun c b h => a1 _ _ _ _ (gw c b h)
  have P1 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m1 z o k' q := p1
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint64) rfl E.find_stats rfl (W1 _ _ (by simp [optTargetsG]))
    (show Exec.evalExpr ge (nEnv bI) le m1 (.Etempvar dense.id.«stats_arg» (tptr (.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr))) = _ from hsta) rfl rfl rfl ?_
  intro m2 f2 u2 g2 a2 p2
  have F2 := F1.step u2 (by facts_ne) f2
  have O2 := OptionsAtG.unch O1 u2 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W2 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m2 c b (zOfInt 0) .Writable :=
    fun c b h => a2 _ _ _ _ (W1 c b h)
  have P2 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m2 z o k' q :=
    fun z o k' q h => p2 _ _ _ _ (P1 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_getcanon rfl (W2 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oGetcanon rfl (by decide) (by decide) O2.getcanon) rfl rfl rfl ?_
  intro m3 f3 u3 g3 a3 p3
  have F3 := F2.step u3 (by facts_ne) f3
  have O3 := OptionsAtG.unch O2 u3 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W3 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m3 c b (zOfInt 0) .Writable :=
    fun c b h => a3 _ _ _ _ (W2 c b h)
  have P3 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m3 z o k' q :=
    fun z o k' q h => p3 _ _ _ _ (P2 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_digraph rfl (W3 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oDigraph rfl (by decide) (by decide) O3.digraph) rfl rfl rfl ?_
  intro m4 f4 u4 g4 a4 p4
  have F4 := F3.step u4 (by facts_ne) f4
  have O4 := OptionsAtG.unch O3 u4 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W4 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m4 c b (zOfInt 0) .Writable :=
    fun c b h => a4 _ _ _ _ (W3 c b h)
  have P4 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m4 z o k' q :=
    fun z o k' q h => p4 _ _ _ _ (P3 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_writeautoms rfl (W4 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oWriteautoms rfl (by decide) (by decide) O4.writeautoms) rfl rfl rfl ?_
  intro m5 f5 u5 g5 a5 p5
  have F5 := F4.step u5 (by facts_ne) f5
  have O5 := OptionsAtG.unch O4 u5 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W5 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m5 c b (zOfInt 0) .Writable :=
    fun c b h => a5 _ _ _ _ (W4 c b h)
  have P5 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m5 z o k' q :=
    fun z o k' q h => p5 _ _ _ _ (P4 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_domarkers rfl (W5 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oWritemarkers rfl (by decide) (by decide) O5.writemarkers) rfl rfl rfl ?_
  intro m6 f6 u6 g6 a6 p6
  have F6 := F5.step u6 (by facts_ne) f6
  have O6 := OptionsAtG.unch O5 u6 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W6 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m6 c b (zOfInt 0) .Writable :=
    fun c b h => a6 _ _ _ _ (W5 c b h)
  have P6 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m6 z o k' q :=
    fun z o k' q h => p6 _ _ _ _ (P5 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_cartesian rfl (W6 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oCartesian rfl (by decide) (by decide) O6.cartesian) rfl rfl rfl ?_
  intro m7 f7 u7 g7 a7 p7
  have F7 := F6.step u7 (by facts_ne) f7
  have O7 := OptionsAtG.unch O6 u7 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W7 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m7 c b (zOfInt 0) .Writable :=
    fun c b h => a7 _ _ _ _ (W6 c b h)
  have P7 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m7 z o k' q :=
    fun z o k' q h => p7 _ _ _ _ (P6 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_doschreier rfl (W7 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oSchreier rfl (by decide) (by decide) O7.schreier) rfl rfl rfl ?_
  intro m8 f8 u8 g8 a8 p8
  have F8 := F7.step u8 (by facts_ne) f8
  have O8 := OptionsAtG.unch O7 u8 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W8 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m8 c b (zOfInt 0) .Writable :=
    fun c b h => a8 _ _ _ _ (W7 c b h)
  have P8 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m8 z o k' q :=
    fun z o k' q h => p8 _ _ _ _ (P7 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Search.eval_gint (e := (nEnv bI)) (x := 0) rfl E.find_doschreier (F8.get (by simp))]
  simp only [typeof, cop]
  rw [ite_eq_right (by decide)]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_linelength rfl (W8 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oLinelength rfl (by decide) (by decide) O8.linelength) rfl rfl rfl ?_
  intro m9 f9 u9 g9 a9 p9
  have F9 := F8.step u9 (by facts_ne) f9
  have O9 := OptionsAtG.unch O8 u9 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W9 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m9 c b (zOfInt 0) .Writable :=
    fun c b h => a9 _ _ _ _ (W8 c b h)
  have P9 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m9 z o k' q :=
    fun z o k' q h => p9 _ _ _ _ (P8 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Search.eval_gint (e := (nEnv bI)) (x := 0) rfl E.find_digraph (F9.get (by simp))]
  simp only [typeof, cop]
  rw [ite_eq_right (by decide)]
  wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_tcLevel rfl (W9 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oTcLevel rfl (by decide) (by decide) O9.tcLevel) rfl rfl rfl ?_
  intro m10 f10 u10 g10 a10 p10
  have F10 := F9.step u10 (by facts_ne) f10
  have O10 := OptionsAtG.unch O9 u10 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W10 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m10 c b (zOfInt 0) .Writable :=
    fun c b h => a10 _ _ _ _ (W9 c b h)
  have P10 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m10 z o k' q :=
    fun z o k' q h => p10 _ _ _ _ (P9 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_optFG hopt T.field_oOutfile rfl (by decide) (by decide) O10.outfile]
  simp only [Exec.evalExpr, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, Search.cmp_null_ptr (P10 _ _ _ _ hdum)]
  simp only [Option.map, Val.of_bool, Bool.false_eq_true, ite_false, cop]
  rw [show Cfrontend.Cop.bool_val Vfalse tint m10 = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_optFG hopt T.field_oOutfile rfl (by decide) (by decide) O10.outfile]
  simp only [typeof, cop]
  have hopt : PTree.get dense.id.«options» (PTree.set (idOf 727)
      (.Vptr bout Ptrofs.zero) le) =
      some (.Vptr bopt Ptrofs.zero) := by
    rw [temps_gso _ _ (by decide)]; exact hopt
  have hcan : PTree.get dense.id.«canong_arg» (PTree.set (idOf 727)
      (.Vptr bout Ptrofs.zero) le) = some (.Vptr bc Ptrofs.zero) := by
    rw [temps_gso _ _ (by decide)]; exact hcan
  refine wp_gset (chunk := .Mint64) (v := .Vptr bout Ptrofs.zero) rfl E.find_outfile rfl (W10 _ _ (by simp [optTargetsG]))
    (by simp [Exec.evalExpr, temps_gss]) rfl rfl rfl ?_
  intro m11 f11 u11 g11 a11 p11
  have F11 := F10.step u11 (by facts_ne) f11
  have O11 := OptionsAtG.unch O10 u11 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W11 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m11 c b (zOfInt 0) .Writable :=
    fun c b h => a11 _ _ _ _ (W10 c b h)
  have P11 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m11 z o k' q :=
    fun z o k' q h => p11 _ _ _ _ (P10 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint64) rfl E.find_usernodeproc rfl (W11 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oUsernodeproc rfl (by decide) (by decide) O11.usernodeproc) rfl rfl rfl ?_
  intro m12 f12 u12 g12 a12 p12
  have F12 := F11.step u12 (by facts_ne) f12
  have O12 := OptionsAtG.unch O11 u12 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W12 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m12 c b (zOfInt 0) .Writable :=
    fun c b h => a12 _ _ _ _ (W11 c b h)
  have P12 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m12 z o k' q :=
    fun z o k' q h => p12 _ _ _ _ (P11 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint64) rfl E.find_userautomproc rfl (W12 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oUserautomproc rfl (by decide) (by decide) O12.userautomproc) rfl rfl rfl ?_
  intro m13 f13 u13 g13 a13 p13
  have F13 := F12.step u13 (by facts_ne) f13
  have O13 := OptionsAtG.unch O12 u13 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W13 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m13 c b (zOfInt 0) .Writable :=
    fun c b h => a13 _ _ _ _ (W12 c b h)
  have P13 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m13 z o k' q :=
    fun z o k' q h => p13 _ _ _ _ (P12 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint64) rfl E.find_userlevelproc rfl (W13 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oUserlevelproc rfl (by decide) (by decide) O13.userlevelproc) rfl rfl rfl ?_
  intro m14 f14 u14 g14 a14 p14
  have F14 := F13.step u14 (by facts_ne) f14
  have O14 := OptionsAtG.unch O13 u14 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W14 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m14 c b (zOfInt 0) .Writable :=
    fun c b h => a14 _ _ _ _ (W13 c b h)
  have P14 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m14 z o k' q :=
    fun z o k' q h => p14 _ _ _ _ (P13 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint64) rfl E.find_usercanonproc rfl (W14 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oUsercanonproc rfl (by decide) (by decide) O14.usercanonproc) rfl rfl rfl ?_
  intro m15 f15 u15 g15 a15 p15
  have F15 := F14.step u15 (by facts_ne) f15
  have O15 := OptionsAtG.unch O14 u15 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W15 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m15 c b (zOfInt 0) .Writable :=
    fun c b h => a15 _ _ _ _ (W14 c b h)
  have P15 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m15 z o k' q :=
    fun z o k' q h => p15 _ _ _ _ (P14 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint64) rfl E.find_invarproc rfl (W15 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oInvarproc rfl (by decide) (by decide) O15.invarproc) rfl rfl rfl ?_
  intro m16 f16 u16 g16 a16 p16
  have F16 := F15.step u16 (by facts_ne) f16
  have O16 := OptionsAtG.unch O15 u16 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W16 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m16 c b (zOfInt 0) .Writable :=
    fun c b h => a16 _ _ _ _ (W15 c b h)
  have P16 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m16 z o k' q :=
    fun z o k' q h => p16 _ _ _ _ (P15 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_optFG hopt T.field_oMininvarlevel rfl (by decide) (by decide) O16.mininvarlevel]
  simp only [Exec.evalExpr, typeof, cop]
  rw [ite_eq_right (by decide)]
  apply wp_set_eval
  simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, typeof, cop]
  rw [ite_eq_right (by decide)]
  have hopt : PTree.get dense.id.«options» (PTree.set (idOf 728) (Vint (Lib.Integers.Int.repr (zOfInt 0)))
      (PTree.set (idOf 727) (Vptr bout Ptrofs.zero) le)) = some (Vptr bopt Ptrofs.zero) := by
    rw [temps_gso _ _ (by decide)]; exact hopt
  have hcan : PTree.get dense.id.«canong_arg» (PTree.set (idOf 728)
      (Vint (Lib.Integers.Int.repr (zOfInt 0))) (PTree.set (idOf 727) (Vptr bout Ptrofs.zero) le)) = some (Vptr bc Ptrofs.zero) := by
    rw [temps_gso _ _ (by decide)]; exact hcan
  wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_mininvarlevel rfl (W16 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oMininvarlevel rfl (by decide) (by decide) O16.mininvarlevel) rfl rfl rfl ?_
  intro m17 f17 u17 g17 a17 p17
  have F17 := F16.step u17 (by facts_ne) f17
  have O17 := OptionsAtG.unch O16 u17 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W17 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m17 c b (zOfInt 0) .Writable :=
    fun c b h => a17 _ _ _ _ (W16 c b h)
  have P17 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m17 z o k' q :=
    fun z o k' q h => p17 _ _ _ _ (P16 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_optFG hopt T.field_oMaxinvarlevel rfl (by decide) (by decide) O17.maxinvarlevel]
  simp only [Exec.evalExpr, typeof, cop]
  rw [ite_eq_right (by decide)]
  apply wp_set_eval
  simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, typeof, cop]
  rw [ite_eq_right (by decide)]
  have hopt : PTree.get dense.id.«options» (PTree.set (idOf 729) (Vint (Lib.Integers.Int.repr (zOfInt 0)))
      (PTree.set (idOf 728) (Vint (Lib.Integers.Int.repr (zOfInt 0))) (PTree.set (idOf 727) (Vptr bout Ptrofs.zero) le))) = some (Vptr bopt Ptrofs.zero) := by
    rw [temps_gso _ _ (by decide)]; exact hopt
  have hcan : PTree.get dense.id.«canong_arg» (PTree.set (idOf 729)
      (Vint (Lib.Integers.Int.repr (zOfInt 0))) (PTree.set (idOf 728) (Vint (Lib.Integers.Int.repr (zOfInt 0))) (PTree.set (idOf 727) (Vptr bout Ptrofs.zero) le))) = some (Vptr bc Ptrofs.zero) := by
    rw [temps_gso _ _ (by decide)]; exact hcan
  wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_maxinvarlevel rfl (W17 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oMaxinvarlevel rfl (by decide) (by decide) O17.maxinvarlevel) rfl rfl rfl ?_
  intro m18 f18 u18 g18 a18 p18
  have F18 := F17.step u18 (by facts_ne) f18
  have O18 := OptionsAtG.unch O17 u18 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W18 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m18 c b (zOfInt 0) .Writable :=
    fun c b h => a18 _ _ _ _ (W17 c b h)
  have P18 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m18 z o k' q :=
    fun z o k' q h => p18 _ _ _ _ (P17 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (chunk := .Mint32) rfl E.find_invararg rfl (W18 _ _ (by simp [optTargetsG]))
    (eval_optFG hopt T.field_oInvararg rfl (by decide) (by decide) O18.invararg) rfl rfl rfl ?_
  intro m19 f19 u19 g19 a19 p19
  have F19 := F18.step u19 (by facts_ne) f19
  have O19 := OptionsAtG.unch O18 u19 (fun h => hbo' _ (by tgt_mem) h.symm)
  have W19 : ∀ c b, (c, b) ∈ optTargetsG → Mem.valid_access m19 c b (zOfInt 0) .Writable :=
    fun c b h => a19 _ _ _ _ (W18 c b h)
  have P19 : ∀ z o k' q, Mem.perm m z o k' q → Mem.perm m19 z o k' q :=
    fun z o k' q h => p19 _ _ _ _ (P18 z o k' q h)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Search.eval_gint (e := (nEnv bI)) (x := 1) rfl E.find_getcanon (F19.get (by simp))]
  simp only [typeof, cop]
  rw [ite_eq_left (by decide)]
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Set.pv, hcan, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, Search.cmp_null_ptr (P19 _ _ _ _ hbc)]
  simp only [Option.map, Val.of_bool, Bool.false_eq_true, ite_false, cop]
  rw [show Cfrontend.Cop.bool_val Vfalse tint m19 = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  refine hQ _ m19 F19 ?_ (fun z h => g19 _ (g18 _ (g17 _ (g16 _ (g15 _ (g14 _ (g13 _ (g12 _ (g11 _ (g10 _ (g9 _ (g8 _ (g7 _ (g6 _ (g5 _ (g4 _ (g3 _ (g2 _ (g1 _ (h)))))))))))))))))))) ?_
  · exact (((((((((((((((((((u1.mono (fun z hz => by subst hz; tgt_mem)).trans (u2.mono (fun z hz => by subst hz; tgt_mem))).trans (u3.mono (fun z hz => by subst hz; tgt_mem))).trans (u4.mono (fun z hz => by subst hz; tgt_mem))).trans (u5.mono (fun z hz => by subst hz; tgt_mem))).trans (u6.mono (fun z hz => by subst hz; tgt_mem))).trans (u7.mono (fun z hz => by subst hz; tgt_mem))).trans (u8.mono (fun z hz => by subst hz; tgt_mem))).trans (u9.mono (fun z hz => by subst hz; tgt_mem))).trans (u10.mono (fun z hz => by subst hz; tgt_mem))).trans (u11.mono (fun z hz => by subst hz; tgt_mem))).trans (u12.mono (fun z hz => by subst hz; tgt_mem))).trans (u13.mono (fun z hz => by subst hz; tgt_mem))).trans (u14.mono (fun z hz => by subst hz; tgt_mem))).trans (u15.mono (fun z hz => by subst hz; tgt_mem))).trans (u16.mono (fun z hz => by subst hz; tgt_mem))).trans (u17.mono (fun z hz => by subst hz; tgt_mem))).trans (u18.mono (fun z hz => by subst hz; tgt_mem))).trans (u19.mono (fun z hz => by subst hz; tgt_mem)))
  · intro x h1 h2 h3
    rw [temps_gso _ _ h3, temps_gso _ _ h2, temps_gso _ _ h1]

end Generic

/-- The option copies (`tOpts`), with the pinned options of the dense harness. -/
theorem wp_tOpts {Q : Post} {le : temp_env} {m : mem} {bo bst bc : block}
    (hopt : PTree.get dense.id.«options» le = some (.Vptr Harness.Block.options Ptrofs.zero))
    (horb : PTree.get dense.id.«orbits_arg» le = some (.Vptr bo Ptrofs.zero))
    (hsta : PTree.get dense.id.«stats_arg» le = some (.Vptr bst Ptrofs.zero))
    (hcan : PTree.get dense.id.«canong_arg» le = some (.Vptr bc Ptrofs.zero))
    (hO : OptionsAt m)
    (hW : ∀ x ∈ optTargets, Mem.valid_access m x.1 x.2 (zOfInt 0) .Writable)
    (hdum : Mem.perm m Harness.Block.dummyfile (zOfInt 0) .Cur .Nonempty)
    (hbc : Mem.perm m bc (zOfInt 0) .Cur .Nonempty)
    (hQ : ∀ le' m', Facts m' (optFacts bo bst) →
      Unch m m' (fun z => z ∈ optTargets.map Prod.snd) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 727 → x ≠ idOf 728 → x ≠ idOf 729 → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tPtn Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.tOpts Q (nEnv bI) le m :=
  wp_tOptsG hopt horb hsta hcan hO.toG (by decide) hW hdum hbc hQ

end NautyVerified.Proofs.Top

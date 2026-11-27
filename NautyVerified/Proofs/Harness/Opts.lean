import NautyVerified.Proofs.Harness.Tail

/-!
# The option settings

`wp_tOpts`: `options.getcanon = TRUE; options.defaultptn = FALSE;
options.userautomproc = emit_generator; options.outfile = &dummyfile;`
turns the initial `options` (`OptionsInit`) into `OptionsAt`, changing
only the block `options`.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)

/-- An assignment to a field of `options`. -/
theorem wp_storeOpt {Q : Post} {e : env} {le : temp_env} {m : mem} {a1 a2 : expr} {v2 v : val}
    {chunk : memory_chunk} {o : Int}
    (hl : Exec.evalLvalue ge e le m a1 =
      some (Block.options, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt o)), .Full))
    (ho : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt o))) = zOfInt o)
    (hv : Exec.evalExpr ge e le m a2 = some v2)
    (hc : Cfrontend.Cop.sem_cast v2 (typeof a2) (typeof a1) m = some v)
    (hmode : access_mode (typeof a1) = .By_value chunk)
    (hacc : Mem.valid_access m chunk Block.options (zOfInt o) .Writable)
    (hQ : ∀ m', Mem.store chunk m Block.options (zOfInt o) v = some m' → Q.normal E0 e le m') :
    Wp Statement.xi ge dense.fn.main (.Sassign a1 a2) Q e le m := by
  apply wp_assign_eval
  rw [hl, hv]
  simp only
  rw [hc]
  simp only
  obtain ⟨m', hm'⟩ := Mem.valid_access_store m chunk Block.options (zOfInt o) v hacc
  simp only [Exec.assignLoc, hmode, Mem.storev, ho, hm']
  exact hQ m' hm'

set_option maxRecDepth 100000 in
theorem lval_getcanon :
    Exec.lvalOfField ge (Tstruct dense.id.optionstruct noattr) dense.id.getcanon
      (.Vptr Block.options Ptrofs.zero) =
    some (Block.options, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 0)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_defaultptn :
    Exec.lvalOfField ge (Tstruct dense.id.optionstruct noattr) dense.id.defaultptn
      (.Vptr Block.options Ptrofs.zero) =
    some (Block.options, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 16)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_userautomproc :
    Exec.lvalOfField ge (Tstruct dense.id.optionstruct noattr) dense.id.userautomproc
      (.Vptr Block.options Ptrofs.zero) =
    some (Block.options, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 48)), .Full) := rfl
set_option maxRecDepth 100000 in
theorem lval_outfile :
    Exec.lvalOfField ge (Tstruct dense.id.optionstruct noattr) dense.id.outfile
      (.Vptr Block.options Ptrofs.zero) =
    some (Block.options, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 32)), .Full) := rfl
kernel_rfl ofs_0 : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 0))) = zOfInt 0
kernel_rfl ofs_16 : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 16))) = zOfInt 16
kernel_rfl ofs_32 : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 32))) = zOfInt 32
kernel_rfl ofs_48 : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 48))) = zOfInt 48

set_option maxRecDepth 100000 in
theorem wp_tOpts {Q : Post} {le : temp_env} {m₀ m : mem} {bst : block}
    (hinit : OptionsInit m₀) (hu : Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z))
    (hvo : Mem.valid_block m₀ Block.options)
    (hQ : ∀ m', OptionsAt m' → Unch m m' (· = Block.options) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Wp Statement.xi ge dense.fn.main tCall Q (envOf bst) le m') :
    Wp Statement.xi ge dense.fn.main tOpts Q (envOf bst) le m := by
  have hE : PTree.get dense.id.«dense_main:options» (envOf bst) = none := by
    rw [PTree.gso _ _ (by decide)]; rfl
  have hlv : Exec.evalExpr ge (envOf bst) le m
      (.Evar dense.id.«dense_main:options» (Tstruct dense.id.optionstruct noattr)) =
      some (.Vptr Block.options Ptrofs.zero) := by
    simp only [Exec.evalExpr, Exec.lvalOfVar, hE, find_options]; rfl
  have hlv' : ∀ mm, Exec.evalExpr ge (envOf bst) le mm
      (.Evar dense.id.«dense_main:options» (Tstruct dense.id.optionstruct noattr)) =
      some (.Vptr Block.options Ptrofs.zero) := by
    intro mm; simp only [Exec.evalExpr, Exec.lvalOfVar, hE, find_options]; rfl
  have hS : ¬ ¬ Mem.valid_block m₀ Block.options := fun h => h hvo
  have acc0 : ∀ c o, 0 ≤ o → o + csize c ≤ 128 →
      ZArith.BinInt.Z.divide (CompCert4Lean.Common.Memdata.align_chunk c) (zOfInt o) →
      Mem.valid_access m c Block.options (zOfInt o) .Writable := fun c o h0 h1 ha =>
    hu.access _ _ _ _ hS (hinit.access c o h0 h1 ha)
  wp_step; wp_step; wp_step
  refine wp_storeOpt (o := 0) (by simp only [Exec.evalLvalue, hlv' m, typeof, lval_getcanon]) ofs_0
    rfl rfl rfl (acc0 .Mint32 0 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 0, rfl⟩)
    fun m1 h1 => ?_
  wp_step; wp_step; wp_step
  refine wp_storeOpt (o := 16) (by simp only [Exec.evalLvalue, hlv' m1, typeof, lval_defaultptn]) ofs_16
    rfl rfl rfl (Mem.store_valid_access_1 _ _ _ _ _ _ h1 _ _ _ _
      (acc0 .Mint32 16 (by decide) (by simp only [csize_Mint32]; omega) ⟨zOfInt 4, rfl⟩))
    fun m2 h2 => ?_
  wp_step; wp_step; wp_step
  have hEg : PTree.get dense.id.«dense_main:emit_generator» (envOf bst) = none := by
    rw [PTree.gso _ _ (by decide)]; rfl
  have hEd : PTree.get dense.id.«dense_main:dummyfile» (envOf bst) = none := by
    rw [PTree.gso _ _ (by decide)]; rfl
  refine wp_storeOpt (o := 48) (v2 := .Vptr Block.emitGenerator Ptrofs.zero)
    (v := .Vptr Block.emitGenerator Ptrofs.zero) (by simp only [Exec.evalLvalue, hlv' m2, typeof, lval_userautomproc])
    ofs_48 (by simp only [Exec.evalExpr, Exec.lvalOfVar, hEg, find_emitGenerator]; rfl) rfl rfl
    (Mem.store_valid_access_1 _ _ _ _ _ _ h2 _ _ _ _ (Mem.store_valid_access_1 _ _ _ _ _ _ h1 _ _ _ _
      (acc0 .Mint64 48 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 6, rfl⟩)))
    fun m3 h3 => ?_
  wp_step; wp_step; wp_step
  refine wp_storeOpt (o := 32) (v2 := .Vptr Block.dummyfile Ptrofs.zero)
    (v := .Vptr Block.dummyfile Ptrofs.zero)
    (by simp only [Exec.evalLvalue, hlv' m3, typeof, lval_outfile]) ofs_32
    (by simp only [Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, hEd, find_dummyfile]; rfl) rfl rfl
    (Mem.store_valid_access_1 _ _ _ _ _ _ h3 _ _ _ _
      (Mem.store_valid_access_1 _ _ _ _ _ _ h2 _ _ _ _ (Mem.store_valid_access_1 _ _ _ _ _ _ h1 _ _ _ _
      (acc0 .Mint64 32 (by decide) (by simp only [csize_Mint64]; omega) ⟨zOfInt 4, rfl⟩))))
    fun m4 h4 => ?_
  refine hQ m4 (OptionsInit.toAt hinit hu hS h1 h2 h3 h4) ?_ ?_
  · exact ((Unch.store (S := (· = Block.options)) h1 rfl).trans (Unch.store h2 rfl)).trans
      ((Unch.store (S := (· = Block.options)) h3 rfl).trans (Unch.store h4 rfl))
  · intro z hz
    exact Mem.store_valid_block_1 _ _ _ _ _ _ h4 _ (Mem.store_valid_block_1 _ _ _ _ _ _ h3 _
      (Mem.store_valid_block_1 _ _ _ _ _ _ h2 _ (Mem.store_valid_block_1 _ _ _ _ _ _ h1 _ hz)))

end NautyVerified.Proofs.Harness

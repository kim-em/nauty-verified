import NautyVerified.Proofs.Search.Node.TcOps
import NautyVerified.Proofs.Search.Node.Firstpathnode
import NautyVerified.Proofs.Alloc.Zero
import NautyVerified.Proofs.Alloc.Zalloc

/-!
# A node's target cell

Both search nodes start by finding their entry of the target-cell list,
`tcnode_this = tcnode_parent->next`, and allocating it when it is missing
(`tcalloc`, the same statement in `firstpathnode0` and `othernode0`).
`wp_tcallocSkip`: when the entry exists, `tcalloc` does nothing.
`wp_tcallocNew`: when it is missing, `tcalloc` allocates a node and a
zero-filled target cell of `alloc_m = M` words and links the node from the
parent, which `TcChain.snoc` turns into the list with one more entry.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Source NautyVerified.Word

variable {xi : ExternalCalls}

/-- `p == NULL` is false for a pointer to offset 0 of a block with a
permission there. -/
theorem cmp_null_ptr {m : mem} {b : block} (hp : Mem.perm m b (zOfInt 0) .Cur .Nonempty) :
    Val.cmplu_bool (Mem.valid_pointer m) .Ceq (.Vptr b Ptrofs.zero)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 0)))) = some false := by
  have hvp : Mem.valid_pointer m b (Ptrofs.unsigned Ptrofs.zero) = true :=
    (Mem.valid_pointer_nonempty_perm m b _).2 hp
  unfold Val.cmplu_bool
  show (if _ && _ && (Mem.valid_pointer m b _ || Mem.valid_pointer m b _) then _ else _) = _
  rw [hvp, Bool.true_or]
  rfl

/-- A `long` at an 8-aligned offset with `Freeable` bytes is writable. -/
theorem va64 {m : mem} {b : block} {off : Nat}
    (h : ∀ o : Int, off ≤ o → o < off + 8 → Mem.perm m b (zOfInt o) .Cur .Freeable)
    (ha : off % 8 = 0) : Mem.valid_access m .Mint64 b (zOfInt off) .Writable := by
  refine ⟨fun o ho => ?_, ⟨zOfInt ((off / 8 : Nat) : Int), ?_⟩⟩
  · have h1 : (off : Int) ≤ intOfZ o := by
      have := ho.1; change intOfZ _ ≤ intOfZ _ at this; rwa [intOfZ_zOfInt] at this
    have h2 : intOfZ o < off + 8 := by
      have := ho.2; change intOfZ _ < intOfZ _ at this
      simpa [intOfZ_add, intOfZ_zOfInt, show intOfZ (Common.Memdata.size_chunk .Mint64) = 8 from rfl]
        using this
    have := h (intOfZ o) h1 h2
    rw [zOfInt_intOfZ] at this
    exact Mem.perm_implies _ _ _ _ _ _ this (.perm_F_any _)
  · apply intOfZ_injective
    simp only [intOfZ_mul, intOfZ_zOfInt, show intOfZ (Common.Memdata.align_chunk .Mint64) = 8 from rfl]
    omega

/-- `NULL == NULL`. -/
theorem eq_null [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (ce : composite_env) (m : mem) (t : type) :
    Cfrontend.Cop.sem_binary_operation ce .Oeq Vnullptr (tptr t)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
      (tptr .Tvoid) m = some (Val.of_bool true) := rfl

/-- `tcalloc` when this level's entry exists: nothing happens. -/
theorem wp_tcallocSkip {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {nd : block} (hthis : PTree.get dense.id.«tcnode_this» le = some (.Vptr nd Ptrofs.zero))
    (hp : Mem.perm m nd (zOfInt 0) .Cur .Nonempty) (hQ : Q.normal E0 e le m) :
    Wp xi ge f Firstpathnode.tcalloc Q e le m := by
  apply wp_if_eval
  simp only [Exec.evalExpr, hthis, typeof, cop]
  simp only [cmp_null_ptr hp, Option.map, cop, Val.of_bool]
  simp only [Vfalse, cop]
  rw [ite_eq_right (by decide)]
  exact wp_skip hQ

/-- `tcalloc` when this level's entry is missing: a new node `nd` and target
cell `tc` (zero-filled, `M` words) are allocated and linked from the parent. -/
theorem wp_tcallocNew {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {par : block} {M : Nat}
    (hthis : PTree.get dense.id.«tcnode_this» le = some Vnullptr)
    (hpar : PTree.get dense.id.«tcnode_parent» le = some (.Vptr par Ptrofs.zero))
    (hparW : Mem.valid_access m .Mint64 par (zOfInt 0) .Writable)
    (hge : PTree.get dense.id.«nauty:alloc_m» e = none) (hal : IntAt m Block.allocM M)
    (hM : 8 * M < 2 ^ 62) (hM31 : M < 2147483648) (hM0 : 0 < M) (hgz : PTree.get dense.id.nauty_zalloc e = none)
    (hQ : ∀ le' m' nd tc, ¬ Mem.valid_block m nd → ¬ Mem.valid_block m tc → nd ≠ tc →
      Unch m m' (fun z => z = par ∨ ¬ Mem.valid_block m z) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      FieldAt m' .Mint64 par 0 (.Vptr nd Ptrofs.zero) →
      (∀ v, FieldAt m .Mint64 par 8 v → FieldAt m' .Mint64 par 8 v) →
      FieldAt m' .Mint64 nd 0 Vnullptr → FieldAt m' .Mint64 nd 8 (.Vptr tc Ptrofs.zero) →
      ArrayAt m' .Mint64 tc 0 (fun _ => .Vlong (lr 0)) M →
      PTree.get dense.id.«tcnode_this» le' = some (.Vptr nd Ptrofs.zero) →
      (∀ x, x ≠ dense.id.«tcnode_this» → x ≠ idOf 703 → x ≠ idOf 704 → x ≠ idOf 705 →
        x ≠ idOf 706 → x ≠ idOf 707 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp xi ge f Firstpathnode.tcalloc Q e le m := by
  apply wp_if_eval
  simp only [Exec.evalExpr, hthis, typeof, cop, eq_null]
  simp only [cop, ite_true]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.zalloc Ptrofs.zero) (targs := [tulong]) (tres := tptr .Tvoid)
    (cc := Common.AST.cc_default) _ (Alloc.zallocSpec 16) (Alloc.zalloc_satisfies _) ?_ ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_zalloc]) rfl ⟨rfl, by decide⟩ ?_
  · rfl
  · simp [Exec.evalExpr, Exec.lvalOfVar, hgz, find_zalloc, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · rfl
  rintro t v m1 ⟨rfl, nd, rfl, hfr1, hz1⟩
  have hp0 : Mem.perm m1 nd (zOfInt 0) .Cur .Nonempty :=
    Mem.perm_implies _ _ _ _ _ _ (hfr1.perm 0 (by decide) (by decide)) (.perm_F_any _)
  simp only [set_opttemp, seqPost, Post.after, E0_append]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss, typeof, cop]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss]
  apply wp_if_eval
  simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, temps_gso, typeof, cop,
    cmp_null_ptr hp0, Option.map]
  simp only [ite_false]
  have hvA : Mem.valid_block m Block.allocM := Alloc.valid_of_access hal.writable
  have hal1 : IntAt m1 Block.allocM M :=
    ⟨by rw [hfr1.unch.load _ _ _ (fun h => hfr1.new (h ▸ hvA))]; exact hal.load,
      hfr1.unch.access _ _ _ _ (fun h => hfr1.new (h ▸ hvA)) hal.writable⟩
  have hsz8 : Vptrofs (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) = .Vlong (lr ((8 : Nat) : Int)) := by
    rw [show Cfrontend.Ctypes.sizeof ge.genv_cenv tulong = zOfInt (8 : Nat) from rfl, Alloc.vptrofs_lr]
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.zalloc Ptrofs.zero) (targs := [tulong]) (tres := tptr .Tvoid)
    (cc := Common.AST.cc_default) _ (Alloc.zallocSpec (M * 8)) (Alloc.zalloc_satisfies _) ?_ ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_zalloc]) rfl ⟨rfl, by omega⟩ ?_
  · rfl
  · simp [Exec.evalExpr, Exec.lvalOfVar, hgz, find_zalloc, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, hge, find_allocM, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode, Mem.loadv, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
      hal1.load, typeof, cop, hsz8]
    simp [cop, cast_int_long_ir (a := M) ⟨by omega, by omega⟩]
    exact_mod_cast Alloc.lr_mul M 8
  rintro t v m2 ⟨rfl, tc, rfl, hfr2, hz2⟩
  have hvnd1 : Mem.valid_block m1 nd := Mem.perm_valid_block _ _ _ _ _ (hfr1.perm 0 (by decide) (by decide))
  have hndtc : nd ≠ tc := fun h => hfr2.new (h ▸ hvnd1)
  have hW8 : Mem.valid_access m2 .Mint64 nd (zOfInt ((8 : Nat) : Int)) .Writable :=
    hfr2.unch.access _ _ _ _ hndtc (va64 (fun o h1 h2 => hfr1.perm o (by omega) (by omega)) rfl)
  simp only [set_opttemp, seqPost, Post.after, E0_append]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss, typeof, cop]
  simp only [seqPost, Post.after, E0_append]
  refine wp_tcFStore (off := 8) (by
      simp (config := {decide := true}) only [temps_gso, temps_gss]) (field_tcnodeTcell _ _)
    (by decide) (by simp only [Exec.evalExpr, temps_gss]; exact rfl) rfl rfl hW8 ?_
  intro m3 hst3
  have hptc3 : Mem.perm m3 tc (zOfInt 0) .Cur .Nonempty :=
    Mem.perm_store_1 _ _ _ _ _ _ hst3 _ _ _ _
      (Mem.perm_implies _ _ _ _ _ _ (hfr2.perm 0 (by decide) (by omega)) (.perm_F_any _))
  simp only [seqPost, Post.after, E0_append]
  apply wp_set_eval
  simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, temps_gso, typeof, cop,
    cmp_null_ptr hptc3, Option.map]
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, typeof, cop, Val.of_bool]
  rw [ite_eq_right (by decide)]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  have hvpar : Mem.valid_block m par := Alloc.valid_of_access hparW
  have hpnd : par ≠ nd := fun h => hfr1.new (h ▸ hvpar)
  have hptc : par ≠ tc := fun h => hfr2.new (h ▸ hfr1.grow _ hvpar)
  have hparW3 : Mem.valid_access m3 .Mint64 par (zOfInt ((0 : Nat) : Int)) .Writable :=
    Mem.store_valid_access_1 _ _ _ _ _ _ hst3 _ _ _ _
      (hfr2.unch.access _ _ _ _ hptc (hfr1.unch.access _ _ _ _ hpnd hparW))
  wp_step; wp_step; wp_step
  refine wp_tcFStore (off := 0) (v := .Vptr nd Ptrofs.zero) (ta := tptr tcStruct) ?_
    (field_tcnodeNext _ _) (by decide) ?_ ?_ ?_ hparW3 ?_
  · simp (config := {decide := true}) only [temps_gso, temps_gss]; exact hpar
  · simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss]
  · rfl
  · rfl
  intro m4 hst4
  have hW0 : Mem.valid_access m4 .Mint64 nd (zOfInt ((0 : Nat) : Int)) .Writable :=
    Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _ (Mem.store_valid_access_1 _ _ _ _ _ _ hst3 _ _ _ _
      (hfr2.unch.access _ _ _ _ hndtc (va64 (fun o h1 h2 => hfr1.perm o (by omega) (by omega)) rfl)))
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step
  refine wp_tcFStore (off := 0) (v := Vnullptr) (ta := tptr .Tvoid) ?_
    (field_tcnodeNext _ _) (by decide) ?_ ?_ ?_ hW0 ?_
  · simp (config := {decide := true}) only [temps_gso, temps_gss]
  · simp only [Exec.evalExpr, typeof, cop]; rfl
  · rfl
  · rfl
  intro m5 hst5
  have d08 : ∀ (m m' : mem) (b : block) (v : val), Mem.store .Mint64 m b (zOfInt ((0 : Nat) : Int)) v = some m' →
      Mem.load .Mint64 m' b (zOfInt 8) = Mem.load .Mint64 m b (zOfInt 8) := fun _ _ _ _ h =>
    Mem.load_store_other _ _ _ _ _ _ h _ _ _ (.inr (.inr (by decide)))
  have d80 : ∀ (m m' : mem) (b : block) (v : val), Mem.store .Mint64 m b (zOfInt ((8 : Nat) : Int)) v = some m' →
      Mem.load .Mint64 m' b (zOfInt 0) = Mem.load .Mint64 m b (zOfInt 0) := fun _ _ _ _ h =>
    Mem.load_store_other _ _ _ _ _ _ h _ _ _ (.inr (.inl (by decide)))
  have hu3 := Unch.store hst3 (S := (· = nd)) rfl
  have hu4 := Unch.store hst4 (S := (· = par)) rfl
  have hu5 := Unch.store hst5 (S := (· = nd)) rfl
  have hval : ∀ z, Mem.valid_block m z → Mem.valid_block m5 z := fun z h =>
    Mem.store_valid_block_1 _ _ _ _ _ _ hst5 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hst4 _
      (Mem.store_valid_block_1 _ _ _ _ _ _ hst3 _ (hfr2.grow _ (hfr1.grow _ h))))
  have htcm : ¬ Mem.valid_block m tc := fun h => hfr2.new (hfr1.grow _ h)
  have harr2 := Alloc.zero_longs hz2 (fun o h0 h1 => hfr2.perm o (by omega) h1) (by omega) M (by omega)
  have harr5 := ((harr2.unch hu3 (Ne.symm hndtc)).unch hu4 (Ne.symm hptc)).unch hu5 (Ne.symm hndtc)
  refine hQ _ m5 nd tc hfr1.new htcm hndtc ?_ hval ?_ ?_ ?_ ?_ harr5 ?_ ?_
  · refine ((((hfr1.unch.mono fun z hz => .inr (hz ▸ hfr1.new)).trans
      (hfr2.unch.mono fun z hz => .inr (hz ▸ htcm))).trans (hu3.mono fun z hz => .inr (hz ▸ hfr1.new))).trans
      (hu4.mono fun z hz => .inl hz)).trans (hu5.mono fun z hz => .inr (hz ▸ hfr1.new))
  · refine ⟨?_, Mem.store_valid_access_1 _ _ _ _ _ _ hst5 _ _ _ _
      (Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _ hparW3)⟩
    rw [hu5.load _ _ _ hpnd]
    exact Mem.load_store_same _ _ _ _ _ _ hst4
  · intro v hv
    refine ⟨?_, hu5.access _ _ _ _ hpnd (Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _
      (hu3.access _ _ _ _ hpnd (hfr2.unch.access _ _ _ _ hptc (hfr1.unch.access _ _ _ _ hpnd hv.writable))))⟩
    rw [hu5.load _ _ _ hpnd, d08 _ _ _ _ hst4, hu3.load _ _ _ hpnd, hfr2.unch.load _ _ _ hptc,
      hfr1.unch.load _ _ _ hpnd]
    exact hv.load
  · exact ⟨Mem.load_store_same _ _ _ _ _ _ hst5,
      Mem.store_valid_access_1 _ _ _ _ _ _ hst5 _ _ _ _ hW0⟩
  · refine ⟨?_, Mem.store_valid_access_1 _ _ _ _ _ _ hst5 _ _ _ _
      (Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _
        (Mem.store_valid_access_1 _ _ _ _ _ _ hst3 _ _ _ _ hW8))⟩
    rw [d08 _ _ _ _ hst5, hu4.load _ _ _ (Ne.symm hpnd)]
    exact Mem.load_store_same _ _ _ _ _ _ hst3
  · simp (config := {decide := true}) only [temps_gso, temps_gss]
  · intro x h1 h2 h3 h4 h5 h6
    simp only [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3, temps_gso _ _ h4, temps_gso _ _ h5,
      temps_gso _ _ h6]

end NautyVerified.Proofs.Search

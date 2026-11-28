import NautyVerified.Proofs.Alloc.DynG
import NautyVerified.Proofs.Top.Spec
import NautyVerified.Proofs.Search.Ops
import NautyVerified.Proofs.Search.Frame

/-!
# `densenauty` satisfies `densenautySpec`

`densenauty_satisfies`: given `nauty` against `nautySpec`, naugraph.c's
`densenauty` satisfies the harness's `densenautySpec`: `options->dispatch` is
`&dispatch_graph`; the graph has no loops (HexGraphIso's graphs are
loopless), so `options->digraph` stays 0; the workspace `dnwork` is
(re)allocated for `2 * 500 * m` setwords; `nauty` runs; `options->digraph` is
written back.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Alloc (DynAt)
open NautyVerified.Proofs.Search (FieldAt)
open NautyVerified.Proofs.Harness (OptionsAt wordsOf harnessPtn densenautySpec)
open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

section Cop
variable (m : mem) (t t' : Cfrontend.Ctypes.type) (a b : attr)

@[simp, cop] theorem cast_pp_ptr (bk : block) (o : Lib.Integers.ptrofs) :
    Cfrontend.Cop.sem_cast (.Vptr bk o) (.Tpointer t a) (.Tpointer t' b) m = some (.Vptr bk o) := rfl
@[simp, cop] theorem cast_pp_long (x : Lib.Integers.int64) :
    Cfrontend.Cop.sem_cast (.Vlong x) (.Tpointer t a) (.Tpointer t' b) m = some (.Vlong x) := rfl
end Cop

/-- A range permission of a block outside the changed ones survives. -/
theorem range_perm_unch {m m' : mem} {S : block → Prop} {b : block} {lo hi : Z} {p : Common.Memtype.permission}
    (h : Mem.range_perm m b lo hi .Cur p) (hu : Unch m m' S) (hb : ¬ S b) :
    Mem.range_perm m' b lo hi .Cur p := fun ofs ho => by
  have hva : Mem.valid_access m .Mint8unsigned b ofs p := by
    refine ⟨fun o ho' => ?_, ⟨ofs, by
      apply intOfZ_injective
      simp [show intOfZ (Common.Memdata.align_chunk .Mint8unsigned) = 1 from rfl]⟩⟩
    have h1 : intOfZ ofs ≤ intOfZ o := ho'.1
    have h2 : intOfZ o < intOfZ ofs + 1 := by
      have := ho'.2; change intOfZ _ < intOfZ _ at this
      simpa [intOfZ_add, show intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 from rfl] using this
    rw [show o = ofs by apply intOfZ_injective; omega]
    exact h ofs ho
  have := hu.access _ _ _ _ hb hva
  exact this.1 ofs ⟨by change intOfZ _ ≤ intOfZ _; exact Int.le_refl _, by
    change intOfZ _ < intOfZ _
    simp only [intOfZ_add, show intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 from rfl]; omega⟩

theorem OptionsAt.unch {m m' : mem} {S : block → Prop} (h : OptionsAt m) (hu : Unch m m' S)
    (hb : ¬ S Harness.Block.options) : OptionsAt m' where
  getcanon := h.getcanon.unch hu hb
  digraph := h.digraph.unch hu hb
  writeautoms := h.writeautoms.unch hu hb
  writemarkers := h.writemarkers.unch hu hb
  defaultptn := h.defaultptn.unch hu hb
  cartesian := h.cartesian.unch hu hb
  linelength := h.linelength.unch hu hb
  outfile := h.outfile.unch hu hb
  userrefproc := h.userrefproc.unch hu hb
  userautomproc := h.userautomproc.unch hu hb
  userlevelproc := h.userlevelproc.unch hu hb
  usernodeproc := h.usernodeproc.unch hu hb
  usercanonproc := h.usercanonproc.unch hu hb
  invarproc := h.invarproc.unch hu hb
  tcLevel := h.tcLevel.unch hu hb
  mininvarlevel := h.mininvarlevel.unch hu hb
  maxinvarlevel := h.maxinvarlevel.unch hu hb
  invararg := h.invararg.unch hu hb
  dispatch := h.dispatch.unch hu hb
  schreier := h.schreier.unch hu hb
  extraOptions := h.extraOptions.unch hu hb

/-- The temporaries on entry. -/
def dnTemps (bg bl bp bo bst bc : block) (M n : Nat) : temp_env :=
  PTree.set dense.id.h (.Vptr bc Ptrofs.zero) (PTree.set dense.id.n (.Vint (ir n))
    (PTree.set dense.id.m (.Vint (ir M)) (PTree.set dense.id.stats (.Vptr bst Ptrofs.zero)
      (PTree.set dense.id.options (.Vptr Harness.Block.options Ptrofs.zero)
        (PTree.set dense.id.orbits (.Vptr bo Ptrofs.zero) (PTree.set dense.id.ptn (.Vptr bp Ptrofs.zero)
          (PTree.set dense.id.lab (.Vptr bl Ptrofs.zero) (PTree.set dense.id.g (.Vptr bg Ptrofs.zero)
            (create_undef_temps dense.fn.densenauty.fn_temps)))))))))

/-- `options->fld` for the `options` temporary. -/
abbrev optF (fld : ident) (ty : Cfrontend.Ctypes.type) : expr :=
  .Efield (.Ederef (.Etempvar dense.id.options (tptr (.Tstruct dense.id.optionstruct noattr)))
    (.Tstruct dense.id.optionstruct noattr)) fld ty

kernel_rfl fld_digraph : ∀ (l : block) (o : Lib.Integers.ptrofs),
  Exec.lvalOfField ge (.Tstruct dense.id.optionstruct noattr) dense.id.digraph (.Vptr l o) =
    some (l, Ptrofs.add o (Ptrofs.repr (zOfInt 4)), .Full)
kernel_rfl fld_dispatch : ∀ (l : block) (o : Lib.Integers.ptrofs),
  Exec.lvalOfField ge (.Tstruct dense.id.optionstruct noattr) dense.id.dispatch (.Vptr l o) =
    some (l, Ptrofs.add o (Ptrofs.repr (zOfInt 104)), .Full)

/-- Reading `options->fld` at byte `off`. -/
theorem eval_optF {e : env} {le : temp_env} {m : mem} {fld : ident} {ty : Cfrontend.Ctypes.type}
    {chunk : memory_chunk} {off : Int} {v : val}
    (hle : PTree.get dense.id.options le = some (.Vptr Harness.Block.options Ptrofs.zero))
    (hfld : ∀ l o, Exec.lvalOfField ge (.Tstruct dense.id.optionstruct noattr) fld (.Vptr l o) =
      some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (hacc : Cfrontend.Ctypes.access_mode ty = .By_value chunk) (h0 : 0 ≤ off) (h1 : off < 2 ^ 64)
    (hf : FieldAt m chunk Harness.Block.options off v) :
    Exec.evalExpr ge e le m (optF fld ty) = some v := by
  simp only [optF, Exec.evalExpr, hle, typeof, Exec.derefLoc]
  simp only [hacc]
  simp only [Cfrontend.Ctypes.access_mode, Mem.loadv, hfld]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [Search.unsigned_add_off Ptrofs.zero h0 (by simpa using h1)]
  simpa using hf.load

kernel_rfl info_dispatchGraph :
  (Init.info Harness.Block.dispatchGraph).map (fun x => (init_data_list_size x.1, x.2)) =
    some (zOfInt 88, false, false)

/-- `&dispatch_graph` is a valid pointer in any memory that agrees with the
initial one on `dispatch_graph`. -/
theorem dispatchGraph_vp {m₀ m : mem} (hm : Genv.init_mem Init.prog = some m₀) {S : block → Prop}
    (hu : Unch m₀ m S) (hS : ¬ S Harness.Block.dispatchGraph) :
    Mem.valid_pointer m Harness.Block.dispatchGraph (zOfInt 0) = true := by
  have hi := info_dispatchGraph
  cases hf : Genv.find_var_info ge.genv_genv Harness.Block.dispatchGraph with
  | none => simp [Init.info, hf] at hi
  | some v =>
    simp only [Init.info, hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨hsz, hro, hvol⟩ := hi
    have h1 := (Init.var_init hm hf hvol).1
    have hp : Genv.perm_globvar v = .Writable := by
      unfold Genv.perm_globvar; rw [hro, hvol]; rfl
    rw [hp, hsz] at h1
    rw [Mem.valid_pointer_valid_access]
    apply hu.access _ _ _ _ hS
    refine ⟨fun o ho => Mem.perm_implies _ _ _ _ _ _ (h1 o ⟨ho.1, ?_⟩) (.perm_any_N _), ⟨zOfInt 0, rfl⟩⟩
    have := ho.2
    change intOfZ o < intOfZ _ at this ⊢
    simp only [intOfZ_zOfInt] at this ⊢
    change intOfZ o < intOfZ (ZArith.BinInt.Z.add (zOfInt 0) _) at this
    rw [intOfZ_add, intOfZ_zOfInt] at this
    have h1' : intOfZ (Common.Memdata.size_chunk Mint8unsigned) = 1 := rfl
    omega

/-- `p != p` for a valid pointer `p` at offset 0. -/
theorem ne_same_ptr (ce : composite_env) (m : mem) (t t' : Cfrontend.Ctypes.type) (b : block)
    (hv : Mem.valid_pointer m b (zOfInt 0) = true) :
    Cfrontend.Cop.sem_binary_operation ce .One (.Vptr b Ptrofs.zero) (tptr t) (.Vptr b Ptrofs.zero)
      (tptr t') m = some (Val.of_bool false) := by
  simp [Cfrontend.Cop.sem_binary_operation, Cfrontend.Cop.sem_cmp, Cfrontend.Cop.classify_cmp,
    Cfrontend.Cop.cmp_ptr, Val.cmplu_bool, CompCert4Lean.X86_64.Archi.ptr64, typeconv,
    remove_attributes, change_attributes, hv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  left
  split
  · rfl
  · rename_i h
    exfalso; apply h
    unfold eq_block
    cases hp : Lib.Coqlib.peq b b with
    | left _ => rfl
    | right h => exact absurd rfl h

theorem rowsOf_loopless {n k : Nat} (G : Colored n k) {i : Nat} (hi : i < n) :
    (rowsOf G)[i]!.mem i = false := by
  have hr : (rowsOf G)[i]! = rowOf G i := by
    simp [rowsOf, hi]
  rw [hr, mem_rowOf, dite_eq_left ⟨hi, hi⟩, Hex.Graph.adj_eq_getElem]
  exact G.graph.loopless ⟨i, hi⟩

variable {xi : ExternalCalls} in
/-- The loop search finds no loop: it ends with `i = n`. -/
theorem wp_scanLoop {Q : Post} {le : temp_env} {m : mem} {n k : Nat} (G : Colored n k) {bg : block}
    {gw : Nat → Lib.Integers.int64} {M : Nat}
    (hg : GraphAt m bg Ptrofs.zero gw (rowsOf G) M) (hM : M < 33554432) (hnM : n ≤ 64 * M)
    (hnl : n < 1073741824)
    (hn : PTree.get dense.id.n le = some (.Vint (ir n)))
    (hm : PTree.get dense.id.m le = some (.Vint (ir M)))
    (hi : PTree.get dense.id.i le = some (.Vint (ir 0)))
    (hgi : PTree.get dense.id.gi le = some (.Vptr bg Ptrofs.zero))
    (hbit : Set.BitTable m Block.naugraphBit)
    (hQ : ∀ le', PTree.get dense.id.i le' = some (.Vint (ir n)) →
      (∀ x, x ≠ dense.id.i → x ≠ dense.id.gi → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m) :
    Wp xi ge dense.fn.densenauty Densenauty.scanLoop Q empty_env le m := by
  let base := intOfZ (Ptrofs.unsigned (Ptrofs.zero : Lib.Integers.ptrofs))
  have hb0 : base = 0 := rfl
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ j, j ≤ n ∧ v = n - j ∧
      PTree.get dense.id.i le' = some (.Vint (ir j)) ∧
      PTree.get dense.id.gi le' = some (.Vptr bg (ptrTo base 8 (M * j))) ∧
      ∀ x, x ≠ dense.id.i → x ≠ dense.id.gi → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ j, j < n ∧ v = n - j ∧
      PTree.get dense.id.i le' = some (.Vint (ir j)) ∧
      PTree.get dense.id.gi le' = some (.Vptr bg (ptrTo base 8 (M * j))) ∧
      ∀ x, x ≠ dense.id.i → x ≠ dense.id.gi → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0)
    ⟨rfl, rfl, rfl, 0, Nat.zero_le _, rfl, hi, by rw [hgi, Nat.mul_zero, Graph.ptrTo_zero],
      fun _ _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, hj, rfl, hij, hgj, ho⟩
    have hn' : PTree.get dense.id.n le' = some (.Vint (ir n)) := by
      rw [ho _ (by decide) (by decide)]; exact hn
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hij, hn', Refine.tv, typeof, cop]
    rw [ir_lt (a := (j : Int)) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hjn : j < n
    · rw [ite_eq_left (by simpa using hjn)]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      have hrow := hg.row hjn
      have hel := Set.eval_isElement (e := empty_env) (le := le') (s := dense.id.gi)
        (bitId := dense.id.«naugraph:bit») (a := Refine.tv dense.id.i) hrow (by omega) hgj
        (by exact hij) rfl
        (c := j) (by omega) (by omega) hbit rfl find_naugraphBit
      rw [(hg.rep j hjn).2 j (by omega), rowsOf_loopless G hjn] at hel
      wp_step; wp_step
      apply wp_if_eval
      rw [hel]
      simp only [Val.of_bool, typeof, cop, Bool.false_eq_true, ite_false]
      apply wp_skip
      exact ⟨by simp, rfl, rfl, j, hjn, rfl, hij, hgj, ho⟩
    · rw [ite_eq_right (by simpa using hjn)]
      apply wp_break
      simp only [E0_append]
      exact hQ le' (by rw [hij, show j = n by omega]) ho
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, hj, rfl, hij, hgj, ho⟩
    have hm' : PTree.get dense.id.m le' = some (.Vint (ir M)) := by
      rw [ho _ (by decide) (by decide)]; exact hm
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hij, Refine.tv, typeof, cop, ir_add]
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss, hgj, hm', Set.pv,
      typeof, cop]
    have hadd : Ptrofs.add (ptrTo base 8 (M * j)) (Ptrofs.mul (Ptrofs.repr
        (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir M))) =
        ptrTo base 8 (M * (j + 1)) := by
      have h := add_ptrTo_ptrTo base (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong) (M * j) M
        (by omega)
      have h8 : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong) = 8 := rfl
      rw [h8, ← Nat.mul_succ] at h
      exact h
    rw [hadd]
    refine ⟨n - (j + 1), by omega, by simp, rfl, rfl, j + 1, by omega, rfl, ?_, ?_, ?_⟩
    · rw [temps_gso _ _ (by decide), temps_gss]; push_cast; rfl
    · rw [temps_gss]
    · intro x h1 h2
      rw [temps_gso _ _ h2, temps_gso _ _ h1, ho x h1 h2]

theorem densenauty_satisfies {xi : ExternalCalls} {n k : Nat} (G : Colored n k)
    (gens : List (Array Nat)) (bg bl bp bo bst bc : block)
    (hN : ∀ capD bD, Satisfies xi ge (.Internal dense.fn.nauty)
      (nautySpec G gens bg bl bp bo bst bc capD bD)) :
    Satisfies xi ge (.Internal dense.fn.densenauty) (densenautySpec G gens bg bl bp bo bst bc) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = dnTemps bg bl bp bo bst bc (wordsOf n) n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, dnTemps bg bl bp bo bst bc (wordsOf n) n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩,
      rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀' ⟨rfl, hinit, hopt, ⟨gw, hg⟩, hlab, hptn, hob, hcg, hst, hpw, hn0, hnmax⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, hmm⟩
    subst hmm
    rw [dense.fn.densenauty.fn_body_eq, Densenauty.body_eq]
    simp only [Densenauty.body]
    obtain ⟨m₀, hm0, hu0, hgrow, hfresh⟩ := hinit
    have hdgv : Mem.valid_block m₀ Harness.Block.dispatchGraph :=
      Alloc.valid_of_access ((Mem.valid_pointer_valid_access _ _ _).1
        (dispatchGraph_vp hm0 (Unch.refl m₀ (fun _ => False)) (fun h => h)))
    have hvp : Mem.valid_pointer m Harness.Block.dispatchGraph (zOfInt 0) = true :=
      dispatchGraph_vp hm0 hu0 (by rintro (h | h); exact absurd h (by decide); exact h hdgv)
    have hT : ∀ x v, PTree.get x (dnTemps bg bl bp bo bst bc (wordsOf n) n) = some v →
        PTree.get x (dnTemps bg bl bp bo bst bc (wordsOf n) n) = some v := fun _ _ h => h
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, eval_optF (by simp (config := {decide := true}) only [dnTemps, temps_gso,
      temps_gss]) fld_dispatch rfl (by decide) (by decide) hopt.dispatch]
    simp only [Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar,
      show PTree.get dense.id.dispatch_graph (empty_env : env) = none from rfl,
      Harness.find_dispatchGraph, typeof]
    rw [ne_same_ptr _ _ _ _ _ hvp]
    simp only [cop, Val.of_bool, Bool.false_eq_true, ite_false]
    apply wp_skip
    have hopts : PTree.get dense.id.options (dnTemps bg bl bp bo bst bc (wordsOf n) n) =
        some (.Vptr Harness.Block.options Ptrofs.zero) := by
      simp (config := {decide := true}) only [dnTemps, temps_gso, temps_gss]
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_optF hopts fld_digraph rfl (by decide) (by decide) hopt.digraph]
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
    rw [ite_eq_left (by decide)]
    have hgl := Init.globals hm0
    have nS : ∀ {z : block} {id : ident}, Genv.find_symbol ge.genv_genv id = some z →
        z ≠ Harness.Block.options → ¬ (z = Harness.Block.options ∨ ¬ Mem.valid_block m₀ z) :=
      fun hf hne h => h.elim hne (fun h => h (Init.valid_global hm0 hf))
    have hbit : Set.BitTable m Block.naugraphBit :=
      hgl.naugraphBit.unch hu0 (nS find_naugraphBit (by decide))
    have hM := Statement.setwordsNeeded
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss, dnTemps, Set.pv]
    simp only [seqPost, Post.after, E0_append]
    have hnl : n < 1073741824 := by omega
    have hwM : n ≤ 64 * wordsOf n := by
      simp only [wordsOf, Statement.setwordsNeeded]; omega
    have hwl : wordsOf n < 33554432 := by
      simp only [wordsOf, Statement.setwordsNeeded]; omega
    refine wp_scanLoop G hg hwl hwM hnl ?_ ?_ (by rw [temps_gso _ _ (by decide), temps_gss])
      (by rw [temps_gss]) hbit ?_
    · simp (config := {decide := true}) only [dnTemps, temps_gso, temps_gss]
    · simp (config := {decide := true}) only [dnTemps, temps_gso, temps_gss]
    intro le1 hi1 ho1
    have hT1 : ∀ x, x ≠ dense.id.i → x ≠ dense.id.gi → x ≠ dense.id.digraph →
        PTree.get x le1 = PTree.get x (dnTemps bg bl bp bo bst bc (wordsOf n) n) := fun x h1 h2 h3 => by
      rw [ho1 x h1 h2, temps_gso _ _ h2, temps_gso _ _ h1, temps_gso _ _ h3]; rfl
    have hn1 : PTree.get dense.id.n le1 = some (.Vint (ir n)) := by
      rw [hT1 _ (by decide) (by decide) (by decide)]
      simp (config := {decide := true}) only [dnTemps, temps_gso, temps_gss]
    have hm1 : PTree.get dense.id.m le1 = some (.Vint (ir (wordsOf n))) := by
      rw [hT1 _ (by decide) (by decide) (by decide)]
      simp (config := {decide := true}) only [dnTemps, temps_gso, temps_gss]
    wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hi1, hn1, Refine.tv, typeof, cop]
    rw [ir_lt (a := (n : Int)) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    rw [ite_eq_right (by simp)]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    -- the workspace
    have hD0 : DynAt m Block.naugraphDnwork Block.naugraphDnworkSz 8 0 bg :=
      (hgl.naugraphDnwork 8 bg).keep hu0 (nS find_naugraphDnwork (by decide))
        (nS find_naugraphDnworkSz (by decide)) (fun h => absurd h (Nat.lt_irrefl 0))
    have hws : wordsOf n ≤ 1024 := by simp only [wordsOf, Statement.setwordsNeeded]; omega
    wp_step
    refine Alloc.wp_dynalloc1Z (c := 8) (n := 2 * 500 * wordsOf n) find_naugraphDnworkSz
      find_naugraphDnwork rfl hD0 (fun _ _ => by
        simp only [Exec.evalExpr, hm1, Refine.tv, typeof, cop, ir_mul]
        rw [Int.natCast_mul, Int.natCast_mul]; rfl)
      rfl (by omega) (by omega) ?_
    intro le2 m2 capD bD hD hcapD hu2 hbD hg2 ho2
    have hT2 : ∀ x, x ≠ dense.id.i → x ≠ dense.id.gi → x ≠ dense.id.digraph → x ≠ idOf 703 →
        x ≠ idOf 704 →
        PTree.get x le2 = PTree.get x (dnTemps bg bl bp bo bst bc (wordsOf n) n) :=
      fun x h1 h2 h3 h4 h5 => by rw [ho2 x h4 h5, hT1 x h1 h2 h3]
    have e : ∀ x, x = dense.id.g ∨ x = dense.id.lab ∨ x = dense.id.ptn ∨ x = dense.id.orbits ∨
        x = dense.id.options ∨ x = dense.id.stats ∨ x = dense.id.m ∨ x = dense.id.n ∨
        x = dense.id.h →
        PTree.get x le2 = PTree.get x (dnTemps bg bl bp bo bst bc (wordsOf n) n) := by
      intro x hx
      apply hT2 <;> rintro rfl <;> revert hx <;> decide
    have hcD : 0 < capD := by have := hcapD; have : 0 < wordsOf n := by
                                simp only [wordsOf, Statement.setwordsNeeded]; omega
                              omega
    wp_step; wp_step; wp_step
    simp only [Densenauty.nautyCall]
    refine wp_call (vf := .Vptr Search.Block.nautyFn Ptrofs.zero)
      (targs := [tptr tulong, tptr tint, tptr tint, tptr tulong, tptr tint,
        tptr (.Tstruct dense.id.optionstruct noattr), tptr (.Tstruct dense.id._1024 noattr),
        tptr tulong, tint, tint, tint, tptr tulong]) (tres := .Tvoid) (cc := cc_default)
      (vargs := [.Vptr bg Ptrofs.zero, .Vptr bl Ptrofs.zero, .Vptr bp Ptrofs.zero, nullArg,
        .Vptr bo Ptrofs.zero, .Vptr Harness.Block.options Ptrofs.zero, .Vptr bst Ptrofs.zero,
        .Vptr bD Ptrofs.zero, .Vint (ir (2 * 500 * wordsOf n)), .Vint (ir (wordsOf n)), .Vint (ir n),
        .Vptr bc Ptrofs.zero]) _ _ (hN capD bD) ?_ ?_ ?_
      (by simp [Common.Globalenvs.Genv.find_funct, Search.funct_nautyFn]) rfl ?_ ?_
    · rfl
    · simp only [Exec.evalExpr, Exec.lvalOfVar,
        show PTree.get dense.id.nauty (empty_env : env) = none from rfl,
        Search.find_nautyFn, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
    · simp only [Exec.evalExprlist, Exec.evalExpr, Set.pv, Refine.pi, Refine.tv]
      rw [e dense.id.g (by simp), e dense.id.lab (by simp), e dense.id.ptn (by simp),
        e dense.id.orbits (by simp), e dense.id.options (by simp), e dense.id.stats (by simp),
        e dense.id.m (by simp), e dense.id.n (by simp), e dense.id.h (by simp)]
      simp (config := {decide := true}) only [dnTemps, temps_gso, temps_gss, typeof, cop,
        Exec.lvalOfVar, show PTree.get dense.id.«naugraph:dnwork» (empty_env : env) = none from rfl,
        find_naugraphDnwork, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
        show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, Alloc.Mptr_eq, hD.ptr hcD]
      have h2 : Lib.Integers.Int.mul (Lib.Integers.Int.mul (Lib.Integers.Int.repr (zOfInt 2))
          (Lib.Integers.Int.repr (zOfInt 500))) (ir (wordsOf n : Int)) =
          ir ((2 * 500 * wordsOf n : Nat) : Int) := by
        rw [show Lib.Integers.Int.repr (zOfInt 2) = ir 2 from rfl,
          show Lib.Integers.Int.repr (zOfInt 500) = ir 500 from rfl, ir_mul, ir_mul,
          Int.natCast_mul, Int.natCast_mul]; rfl
      rw [h2]; rfl
    · -- `nautySpec`'s precondition
      have hbDm : ¬ Mem.valid_block m bD := by
        rcases hbD with ⟨h, -⟩ | h
        · omega
        · exact h.1
      have hZ : Alloc.Zeros m2 bD (8 * capD) := by
        rcases hbD with ⟨h, -⟩ | h
        · omega
        · exact h.2
      have hvopt : Mem.valid_block m₀ Harness.Block.options := Init.valid_global hm0 Harness.find_options
      -- a harness block: valid now, fresh relative to the initial memory
      have nH : ∀ z, Mem.valid_block m z → ¬ Mem.valid_block m₀ z →
          ¬ (z = Block.naugraphDnworkSz ∨ z = Block.naugraphDnwork ∨ (0 < 0 ∧ z = bg) ∨
            (¬ Mem.valid_block m bD ∧ z = bD)) := by
        rintro z hv hf (h | h | ⟨h, -⟩ | ⟨-, rfl⟩)
        · exact hf (h ▸ Init.valid_global hm0 find_naugraphDnworkSz)
        · exact hf (h ▸ Init.valid_global hm0 find_naugraphDnwork)
        · exact absurd h (Nat.lt_irrefl 0)
        · exact hbDm hv
      have hH : ∀ z ∈ [bg, bl, bp, bo, bst, bc], ¬ (z = Block.naugraphDnworkSz ∨
          z = Block.naugraphDnwork ∨ (0 < 0 ∧ z = bg) ∨ (¬ Mem.valid_block m bD ∧ z = bD)) :=
        fun z hz => nH z (hfresh z hz).2 (hfresh z hz).1
      have nO : ¬ (Harness.Block.options = Block.naugraphDnworkSz ∨
          Harness.Block.options = Block.naugraphDnwork ∨ (0 < 0 ∧ Harness.Block.options = bg) ∨
          (¬ Mem.valid_block m bD ∧ Harness.Block.options = bD)) := by
        rintro (h | h | ⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (Nat.lt_irrefl 0)
        · exact hbDm (h ▸ hgrow _ hvopt)
      obtain ⟨cv, hcv⟩ := hcg
      obtain ⟨ov, hov⟩ := hob
      refine ⟨rfl, ⟨m₀, hm0, (hu0.mono fun z hz => ?_).trans (hu2.mono fun z hz => ?_),
          fun z hz => hg2 _ (hgrow _ hz), fun z hz => ⟨(hfresh z hz).1, hg2 _ (hfresh z hz).2⟩,
          fun h => hbDm (hgrow _ h), fun h => hbDm (hfresh _ h).2⟩,
        hD, hcapD, hZ, OptionsAt.unch hopt hu2 nO, ⟨gw, hg.arr.unch hu2 (hH _ (by simp)), hg.rep⟩,
        hlab.unch hu2 (hH _ (by simp)), hptn.unch hu2 (hH _ (by simp)),
        ⟨ov, hov.unch hu2 (hH _ (by simp))⟩, ⟨cv, hcv.unch hu2 (hH _ (by simp))⟩,
        range_perm_unch hst hu2 (hH _ (by simp)), hpw, hn0, hnmax⟩
      · rcases hz with h | h
        · exact .inl h
        · exact .inr (.inr (.inr h))
      · rcases hz with h | h | ⟨h, -⟩ | ⟨hv, rfl⟩
        · exact .inr (.inr (.inl h))
        · exact .inr (.inl h)
        · exact absurd h (Nat.lt_irrefl 0)
        · exact .inr (.inr (.inr fun h => hv (hgrow _ h)))
    · rintro t v m3 ⟨⟨hw, hlab3, hob3, hcg3, f12, f16, f20, f24, f32, f40, f48, f56, hst3, hg3⟩, hwr⟩
      simp only [set_opttemp, seqPost, Post.after]
      have hdg : PTree.get dense.id.digraph le2 = some (.Vint (ir 0)) := by
        rw [ho2 _ (by decide) (by decide), ho1 _ (by decide) (by decide)]
        simp (config := {decide := true}) only [temps_gso, temps_gss]
      have hopt2 : PTree.get dense.id.options le2 = some (.Vptr Harness.Block.options Ptrofs.zero) :=
        by rw [e _ (by simp)]; exact hopts
      obtain ⟨m4, hst4⟩ := Mem.valid_access_store _ _ _ _ (.Vint (ir 0)) hwr
      wp_step; wp_step
      apply wp_assign_eval
      simp only [Exec.evalLvalue, optF, Exec.evalExpr, hopt2, hdg, Refine.tv, typeof, cop,
        Exec.derefLoc, Cfrontend.Ctypes.access_mode, fld_digraph, Exec.assignLoc, Mem.storev]
      rw [Search.unsigned_add_off Ptrofs.zero (by decide) (by decide),
        show zOfInt (intOfZ (Ptrofs.unsigned (Ptrofs.zero : Lib.Integers.ptrofs)) + 4) = zOfInt 4
          from rfl, hst4]
      have hu4 : Unch m3 m4 (· = Harness.Block.options) := Unch.store hst4 rfl
      have hvopt : Mem.valid_block m₀ Harness.Block.options := Init.valid_global hm0 Harness.find_options
      have nO : ∀ z ∈ [bg, bl, bp, bo, bst, bc], z ≠ Harness.Block.options := fun z hz h =>
        (hfresh z hz).1 (h ▸ hvopt)
      refine ⟨m4, Nextelement.free_empty m4, by simpa using hw, hlab3.unch hu4 (nO _ (by simp)),
        hob3.unch hu4 (nO _ (by simp)), ?_, f12.unch hu4 (nO _ (by simp)),
        f16.unch hu4 (nO _ (by simp)), f20.unch hu4 (nO _ (by simp)), f24.unch hu4 (nO _ (by simp)),
        f32.unch hu4 (nO _ (by simp)), f40.unch hu4 (nO _ (by simp)), f48.unch hu4 (nO _ (by simp)),
        f56.unch hu4 (nO _ (by simp)), range_perm_unch hst3 hu4 (nO _ (by simp)),
        fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst4 _ (hg3 _ (hg2 _ hz))⟩
      obtain ⟨cw, hcw, hrep⟩ := hcg3
      exact ⟨cw, hcw.unch hu4 (nO _ (by simp)), hrep⟩

end NautyVerified.Proofs.Top

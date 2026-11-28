import NautyVerified.Proofs.Sparse.Marks
import NautyVerified.Proofs.Alloc.DynL
import NautyVerified.Program.Sparse

/-!
# `preparemarks1`

```
static void preparemarks1(size_t nn)
{
    size_t oldsize; short *oldpos;
    oldsize = vmark1_sz; oldpos = vmark1;
    DYNALLOC1(short,vmark1,vmark1_sz,nn,"preparemarks");
    if (vmark1_sz != oldsize || vmark1 != oldpos) vmark1_val = 32000;
}
```
`prepSpec`: afterwards the marks (`MarksAt`) hold at least `nn` entries. When
`DYNALLOC1` allocates, the new array is zero-filled (`nauty_zalloc`) and the
stamp is set to 32000, so the invariant holds with every entry 0; otherwise
nothing changes. The pointer comparison is only evaluated when the capacity is
unchanged, that is when nothing was allocated, so it compares a pointer with
itself (or `NULL` with `NULL`).
-/

namespace NautyVerified.Proofs.Sparse

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Program

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

/-- The blocks the marks may occupy after `preparemarks1`: the three globals,
the old array (if any) and a new one. -/
def MarksS (m : mem) (cap : Nat) (b b' : block) (z : block) : Prop :=
  z = Block.vmark1 ∨ z = Block.vmark1Sz ∨ z = Block.vmark1Val ∨ (0 < cap ∧ z = b) ∨
    (¬ Mem.valid_block m b' ∧ z = b')

/-- `preparemarks1(nn)`: afterwards the marks hold at least `nn` entries; a
reallocated array is a block new to `m`. -/
def prepSpec (nn cap : Nat) (b : block) (st : Nat) (marks : Nat → Int) : FunSpec where
  pre args m := args = [.Vlong (lr nn)] ∧ MarksAt m cap b st marks ∧ nn < 2147483648
  post _ m t _ m' := t = E0 ∧ ∃ cap' b' st' marks', MarksAt m' cap' b' st' marks' ∧ nn ≤ cap' ∧
    ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') ∧ Unch m m' (MarksS m cap b b') ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z)

namespace Prep

abbrev nn : ident := sparse.id.nn
abbrev oldsize : ident := sparse.id.oldsize
abbrev oldpos : ident := sparse.id.oldpos
abbrev t : ident := idOf 705

/-- The body of `preparemarks1`, factored. -/
abbrev body : statement :=
  .Ssequence (Alloc.sk (.Sset oldsize (.Evar id.vmark1Sz tulong)))
   (.Ssequence (Alloc.sk (.Sset oldpos (.Evar id.vmark1 (tptr tshort))))
    (.Ssequence (Alloc.dynalloc1 id.vmark1Sz id.vmark1 tshort (.Etempvar nn tulong) (idOf 703) (idOf 704)
        sparse.id.«nausparse:__stringlit_1» 13)
      (.Ssequence
        (Alloc.sk (.Sifthenelse
          (.Ebinop .One (.Evar id.vmark1Sz tulong) (.Etempvar oldsize tulong) tint)
          (.Sset t (ci 1 tint))
          (Alloc.sk (.Sset t (.Ecast (.Ebinop .One (.Evar id.vmark1 (tptr tshort))
            (.Etempvar oldpos (tptr tshort)) tint) tbool)))))
        (.Sifthenelse (.Etempvar t tint)
          (Alloc.sk (.Sassign (.Evar id.vmark1Val tshort) (ci 32000 tint))) .Sskip))))

kernel_rfl body_eq : sparse.body.«nausparse:preparemarks1» = body

def entryTemps (nv : Nat) : temp_env :=
  PTree.set nn (.Vlong (lr nv)) (create_undef_temps sparse.fn.«nausparse:preparemarks1».fn_temps)

theorem free_empty (m : mem) : Mem.free_list m (blocks_of_env sge empty_env) = some m := rfl

theorem eval_ptr {le : temp_env} {m : mem} {v : val}
    (h : Mem.load .Mint64 m Block.vmark1 (zOfInt 0) = some v) :
    Exec.evalExpr sge empty_env le m (.Evar id.vmark1 (tptr tshort)) = some v := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.vmark1 (empty_env : env) = none from rfl,
    find_vmark1, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq]
  exact h

theorem eq_lr {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Lib.Integers.Int64.eq (lr a) (lr b) = decide (a = b) := by
  rw [bv64_eq]
  apply decide_eq_decide.2
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [Alloc.toNat_lr ha, Alloc.toNat_lr hb] at this
  · intro h; subst h; rfl

end Prep

open Prep in
theorem prep_satisfies (nv cap : Nat) (b : block) (st : Nat) (marks : Nat → Int) :
    Satisfies xi sge (.Internal sparse.fn.«nausparse:preparemarks1») (prepSpec nv cap b st marks) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps nv ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps nv, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hM, hn31⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [sparse.fn.«nausparse:preparemarks1».fn_body_eq, body_eq]
    have hD := hM.dyn
    have hcap := hD.capLt
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_sz hD.capLd]
    let pv : val := if 0 < cap then .Vptr b Ptrofs.zero else Vnullptr
    have hpv : Mem.load .Mint64 m Block.vmark1 (zOfInt 0) = some pv := by
      by_cases h0 : 0 < cap
      · simp only [pv, h0, ite_true]; exact hD.ptr h0
      · simp only [pv, h0, ite_false]; exact hD.null (by omega)
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_ptr hpv]
    wp_step
    refine Alloc.wp_dynalloc1L (E := NautyEnv.sparse) find_vmark1Sz find_vmark1 rfl hD
      (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]) hn31 (show 2 * nv < 2 ^ 62 by omega) ?_
    intro le1 m1 cap1 b1 hD1 hnc hu1 hor hg1 ho1
    have hD1' : Alloc.DynAt m1 Block.vmark1 Block.vmark1Sz 2 cap1 b1 := hD1
    have hcap1 := hD1'.capLt
    have hos : PTree.get oldsize le1 = some (.Vlong (lr cap)) := by
      rw [ho1 _ (by decide) (by decide)]
      simp (config := {decide := true}) only [temps_gso, temps_gss]
    have hop : PTree.get oldpos le1 = some pv := by
      rw [ho1 _ (by decide) (by decide)]
      simp (config := {decide := true}) only [temps_gss]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, eval_sz hD1'.capLd,
      show Exec.evalExpr sge empty_env le1 m1 (.Etempvar oldsize tulong) = _ from hos]
    simp only [typeof, cop, eq_lr (a := cap1) (b := cap) (by omega) (by omega)]
    by_cases hcc : cap1 = cap
    · have hb1 : b1 = b ∧ m1 = m := by
        rcases hor with ⟨-, h1, h2⟩ | ⟨-, hlt, -⟩
        · exact ⟨h1, h2⟩
        · omega
      obtain ⟨rfl, rfl⟩ := hb1
      subst hcc
      simp only [cop, decide_true,
        Bool.not_true]
      simp (config := {decide := true}) only [cop, ite_false]
      wp_step; wp_step
      apply wp_set_eval
      have hcv : Exec.evalExpr sge empty_env le1 m1 (.Ecast (.Ebinop .One (.Evar id.vmark1 (tptr tshort))
          (.Etempvar oldpos (tptr tshort)) tint) tbool) = some (.Vint Lib.Integers.Int.zero) := by
        by_cases h0 : 0 < cap1
        · simp only [pv, h0, ite_true] at hpv hop
          have hw := hM.arr.weak_valid h0 (o := 0) (Int.le_refl _)
            (Int.le_add_of_nonneg_right (Int.mul_nonneg (Int.le_of_lt (csize_pos _)) (Int.natCast_nonneg _)))
          have hw' : (Mem.valid_pointer m1 b1 (Ptrofs.unsigned Ptrofs.zero) || Mem.valid_pointer m1 b1
              (ZArith.BinInt.Z.sub (Ptrofs.unsigned Ptrofs.zero) (.Zpos .xH))) = true := hw
          rw [Exec.evalExpr, Exec.evalExpr, eval_ptr hpv,
            show Exec.evalExpr sge empty_env le1 m1 (.Etempvar oldpos (tptr tshort)) = _ from hop]
          simp only [typeof, cop, cmplu_same _ _ _ _ _ hw' hw']
          rfl
        · simp only [pv, h0, ite_false] at hpv hop
          rw [Exec.evalExpr, Exec.evalExpr, eval_ptr hpv,
            show Exec.evalExpr sge empty_env le1 m1 (.Etempvar oldpos (tptr tshort)) = _ from hop]
          simp only [typeof, cop, Vnullptr]
          rfl
      rw [hcv]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp (config := {decide := true}) only [ite_false]
      apply wp_skip
      exact ⟨m1, free_empty _, rfl, cap1, b1, st, marks, hM, hnc, .inl ⟨rfl, rfl⟩, Unch.refl _ _,
        fun _ h => h⟩
    · obtain ⟨hnew, hlt, hz⟩ := hor.resolve_left (fun h => hcc h.1)
      have hz' : Alloc.Zeros m1 b1 (2 * cap1) := hz
      simp only [show (!decide (cap1 = cap)) = true by simp [hcc], ite_true]
      apply wp_set_eval
      simp only [Exec.evalExpr]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp (config := {decide := true}) only [ite_true]
      wp_step; wp_step
      have hvV : Mem.valid_block m Block.vmark1Val := Alloc.valid_of_access hM.valW
      have hVS : ¬ (Block.vmark1Val = Block.vmark1Sz ∨ Block.vmark1Val = Block.vmark1 ∨
          0 < cap ∧ Block.vmark1Val = b ∨ ¬Mem.valid_block m b1 ∧ Block.vmark1Val = b1) := by
        rintro (h | h | ⟨h0, h⟩ | ⟨h0, h⟩)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact hM.bval h0 h.symm
        · exact h0 (h ▸ hvV)
      have hW := hu1.access _ _ _ _ hVS hM.valW
      refine wp_storeVal (x := 32000) (rhs := ci 32000 tint) (by decide) rfl rfl hW ?_
      intro m2 hst2
      have hu2 : Unch m1 m2 (· = Block.vmark1Val) := Unch.store hst2 rfl
      have hb1V : b1 ≠ Block.vmark1Val := fun h => hnew (h ▸ hvV)
      have hc1 : 0 < cap1 := by omega
      have hmal := hD1'.mal hc1
      have hD2 : Alloc.DynAt m2 Block.vmark1 Block.vmark1Sz 2 cap1 b1 :=
        hD1'.keep hu2 (by decide) (by decide) (fun _ => Alloc.Keep.unch hu2 hb1V)
      have harr : ArrayAt m2 .Mint16signed b1 0 (markVals fun _ => 0) cap1 :=
        (hz'.unch hu2 hb1V).array (fun o h1 h2 => Mem.perm_store_1 _ _ _ _ _ _ hst2 _ _ _ _
          (hmal.perm o (by omega) h2)) hD1'.small .Mint16signed 2 rfl rfl _ rfl cap1 (Nat.le_refl _)
      refine ⟨m2, free_empty _, rfl, cap1, b1, 32000, fun _ => 0, ⟨hD2, ?_,
        Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _ hW, by decide, by decide, harr,
        fun _ _ => ⟨Int.le_refl _, by decide⟩, fun _ => hb1V⟩, hnc, .inr hnew, ?_, fun z h =>
          Mem.store_valid_block_1 _ _ _ _ _ _ hst2 _ (hg1 _ h)⟩
      · rw [Mem.load_store_same _ _ _ _ _ _ hst2]; rfl
      · refine (hu1.mono fun z hz => ?_).trans (hu2.mono fun z hz => .inr (.inr (.inl hz)))
        rcases hz with h | h | h | h
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr h)))

end NautyVerified.Proofs.Sparse

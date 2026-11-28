import NautyVerified.Proofs.Top.Densenauty
import NautyVerified.Proofs.Top.NautySizes
import NautyVerified.Proofs.Top.Copy
import NautyVerified.Proofs.Top.Fields
import NautyVerified.Proofs.Search.Node.Prologue

/-!
# The head of `nauty()`

`wp_head`: `dispatch = *options->dispatch` (a copy of `dispatch_graph`), the
`refine1` substitution when `m = 1`, and the four `NULL` checks of the
dispatch vector, which pass. Afterwards `nauty:dispatch` holds
`dispatchOf M` (`DispatchAt`).
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (FieldAt)
open NautyVerified.Proofs.Harness (OptionsAt)

set_option linter.unusedSimpArgs false

/-- The dispatch vector `nauty()` uses: `dispatch_graph`, with `refine1` as
`refine` when `m = 1`. -/
def dispatchOf (M : Nat) : List val :=
  dispatchVals.set 3 (if M = 1 then .Vptr Refine.Block.refine1 Ptrofs.zero
    else .Vptr Refine.Block.refine Ptrofs.zero)

theorem dispatchOf_length (M : Nat) : (dispatchOf M).length = 11 := by
  simp [dispatchOf, dispatchVals]

/-- `nauty:dispatch` holds `dispatchOf M`. -/
def DispatchAt (m : mem) (M : Nat) : Prop :=
  ∀ (i : Nat) (hi : i < 11), FieldAt m .Mint64 Search.Block.dispatch (8 * (i : Int))
    ((dispatchOf M)[i]'(by rw [dispatchOf_length]; exact hi))

theorem cast_dispatch (m : mem) (b : block) (o : Lib.Integers.ptrofs) :
    Cfrontend.Cop.sem_cast (.Vptr b o) (Cfrontend.Ctypes.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr)
      (Cfrontend.Ctypes.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr) m = some (.Vptr b o) := by
  unfold Cfrontend.Cop.sem_cast Cfrontend.Cop.classify_cast
  simp

theorem bool_null (m : mem) (t : Cfrontend.Ctypes.type) :
    Cfrontend.Cop.bool_val Vnullptr (tptr t) m = some false := rfl

/-- `dispatch.fld`, a pointer field at byte `off`. -/
abbrev dispF (fld : ident) (ty : Cfrontend.Ctypes.type) : expr :=
  .Efield (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr)) fld ty

theorem eval_dispF {le : temp_env} {m : mem} {fld : ident} {t : Cfrontend.Ctypes.type} {off : Int} {v : val}
    (hfld : ∀ l o, Exec.lvalOfField ge (.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr) fld (.Vptr l o) =
      some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (h0 : 0 ≤ off) (h1 : off < 2 ^ 64)
    (hl : Mem.load .Mint64 m Search.Block.dispatch (zOfInt off) = some v) :
    Exec.evalExpr ge (nEnv bI) le m (dispF fld (tptr t)) = some v := by
  simp only [dispF, Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar,
    show PTree.get Source.dense.id.«nauty:dispatch» (nEnv bI : env) = none from rfl,
    Search.find_dispatch, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, typeof]
  rw [hfld]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [Search.unsigned_add_off Ptrofs.zero h0 (by simpa using h1)]
  exact (show Mem.load .Mint64 m _ (zOfInt (intOfZ (Ptrofs.unsigned Ptrofs.zero) + off)) = _ by
    simpa using hl)

theorem cast_flag (m : mem) (M : Nat) :
    Cfrontend.Cop.sem_cast (Val.of_bool (decide ((M : Int) = 1))) tint tbool m =
      some (.Vint (if M = 1 then Lib.Integers.Int.one else Lib.Integers.Int.zero)) := by
  by_cases h : M = 1
  · subst h; rfl
  · rw [decide_eq_false (by omega), if_neg h]; rfl

/-- `dispatch.refine` as a store target. -/
theorem lval_dispF {le : temp_env} {m : mem} {fld : ident} {t : Cfrontend.Ctypes.type} {off : Int}
    (hfld : ∀ l o, Exec.lvalOfField ge (.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr) fld (.Vptr l o) =
      some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full)) :
    Exec.evalLvalue ge (nEnv bI) le m (dispF fld (tptr t)) =
      some (Search.Block.dispatch, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt off)), .Full) := by
  simp only [dispF, Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar,
    show PTree.get Source.dense.id.«nauty:dispatch» (nEnv bI : env) = none from rfl,
    Search.find_dispatch, Exec.derefLoc, Cfrontend.Ctypes.access_mode, typeof]
  exact hfld _ _

theorem dispatchOf_ne {M : Nat} (h : M ≠ 1) : dispatchOf M = dispatchVals := by
  simp [dispatchOf, dispatchVals, h]

/-- `dispatch.fld == NULL` for a function pointer field. -/
theorem eval_dispNull {le : temp_env} {m : mem} {fld : ident} {t : Cfrontend.Ctypes.type} {off : Int}
    {b : block}
    (hfld : ∀ l o, Exec.lvalOfField ge (.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr) fld (.Vptr l o) =
      some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (h0 : 0 ≤ off) (h1 : off < 2 ^ 64)
    (hl : Mem.load .Mint64 m Search.Block.dispatch (zOfInt off) = some (.Vptr b Ptrofs.zero))
    (hp : Mem.perm m b (zOfInt 0) .Cur .Nonempty) :
    Exec.evalExpr ge (nEnv bI) le m (.Ebinop .Oeq (dispF fld (tptr t)) (.Ecast (ci 0 tint) (tptr .Tvoid))
      tint) = some (Val.of_bool false) := by
  rw [Exec.evalExpr, eval_dispF hfld h0 h1 hl]
  simp only [Exec.evalExpr, typeof, cop]
  rw [Search.cmp_null_ptr hp]
  rfl

theorem dispatchOf3 (M : Nat) : ∃ b, (dispatchOf M)[3]'(by rw [dispatchOf_length]; decide) = .Vptr b Ptrofs.zero ∧
    (b = Refine.Block.refine ∨ b = Refine.Block.refine1) := by
  by_cases h : M = 1
  · exact ⟨_, by simp [dispatchOf, h], .inr rfl⟩
  · exact ⟨_, by simp [dispatchOf, h], .inl rfl⟩

set_option maxRecDepth 20000 in
variable {xi : ExternalCalls} in
/-- `if (m == 1 && dispatch.refine1) dispatch.refine = dispatch.refine1;` -/
theorem wp_subst {f : function} {Q : Post} {le : temp_env} {m1 : mem} {M : Nat}
    (h703 : PTree.get (idOf 703) le =
      some (.Vint (if M = 1 then Lib.Integers.Int.one else Lib.Integers.Int.zero)))
    (hld1 : ∀ (i : Nat) (hi : i < 11), Mem.load .Mint64 m1 Search.Block.dispatch (zOfInt (8 * (i : Int))) =
      some (dispatchVals[i]'(by simp [dispatchVals]; omega)))
    (hw24 : Mem.valid_access m1 .Mint64 Search.Block.dispatch (zOfInt 24) .Writable)
    (hQ : ∀ m2, (∀ (i : Nat) (hi : i < 11), Mem.load .Mint64 m2 Search.Block.dispatch (zOfInt (8 * (i : Int))) =
        some ((dispatchOf M)[i]'(by rw [dispatchOf_length]; exact hi))) →
      Unch m1 m2 (· = Search.Block.dispatch) →
      (∀ b z k p, Mem.perm m1 b z k p → Mem.perm m2 b z k p) →
      (∀ z, Mem.valid_block m1 z → Mem.valid_block m2 z) →
      Q.normal E0 (nEnv bI) le m2) :
    Wp xi ge f (.Sifthenelse (Refine.tv (idOf 703))
      (Set.sk (.Sassign (dispF dense.id.refine (tptr Refine.refprocType))
        (dispF dense.id.refine1 (tptr Refine.refprocType)))) .Sskip) Q (nEnv bI) le m1 := by
  apply wp_if_eval
  simp only [Exec.evalExpr, Refine.tv, h703, typeof, cop]
  by_cases hM1 : M = 1
  · simp only [hM1, ite_true]
    rw [ite_eq_left (by decide)]
    obtain ⟨m2, hst⟩ := Mem.valid_access_store m1 Mptr _ _ (.Vptr Refine.Block.refine1 Ptrofs.zero) hw24
    wp_step; wp_step
    apply wp_assign_eval
    rw [lval_dispF Search.field_dRefine, eval_dispF Search.field_dRefine1 (by decide) (by decide)
      (hld1 4 (by decide))]
    rw [show dispatchVals[4] = .Vptr Refine.Block.refine1 Ptrofs.zero from rfl]
    simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
    rw [Search.unsigned_add_off Ptrofs.zero (by decide) (by decide)]
    rw [show zOfInt (intOfZ (Ptrofs.unsigned Ptrofs.zero) + 24) = zOfInt 24 from rfl, hst]
    refine hQ m2 (fun i hi => ?_) (Unch.store hst rfl)
      (fun b z k p h => Mem.perm_store_1 _ _ _ _ _ _ hst _ _ _ _ h)
      (fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ h)
    by_cases h3 : i = 3
    · subst h3
      rw [show zOfInt (8 * ((3 : Nat) : Int)) = zOfInt 24 from rfl]
      have := Mem.load_store_same _ _ _ _ _ _ hst
      refine this.trans ?_
      simp [dispatchOf, hM1]; rfl
    · rw [Mem.load_store_other _ _ _ _ _ _ hst _ _ _ (.inr (by
        rcases Nat.lt_or_gt_of_ne h3 with h | h
        · left; change intOfZ _ ≤ intOfZ _; rw [intOfZ_add]; simp [intOfZ_zOfInt]
          change 8 * (i : Int) + 8 ≤ 24; omega
        · right; change intOfZ _ ≤ intOfZ _; rw [intOfZ_add]; simp [intOfZ_zOfInt]
          change 24 + 8 ≤ 8 * (i : Int); omega)), hld1 i hi]
      simp [dispatchOf, List.getElem_set, Ne.symm h3]
  · rw [if_neg hM1]
    rw [ite_eq_right (by decide)]
    apply wp_skip
    refine hQ m1 (fun i hi => ?_) (Unch.refl _ _) (fun _ _ _ _ h => h) (fun _ h => h)
    rw [hld1 i hi]
    simp [dispatchOf_ne hM1]

set_option maxRecDepth 20000 in
variable {xi : ExternalCalls} in
theorem wp_head {Q : Post} {le : temp_env} {m : mem} {M : Nat}
    (hopt : PTree.get dense.id.options le = some (.Vptr Harness.Block.options Ptrofs.zero))
    (hO : OptionsAt m)
    (hdg : ∀ (i : Nat) (hi : i < 11), Mem.load .Mint64 m Harness.Block.dispatchGraph (zOfInt (8 * (i : Int))) =
      some (dispatchVals[i]'(by simp [dispatchVals]; omega)))
    (hdgr : Mem.range_perm m Harness.Block.dispatchGraph (zOfInt 0) (zOfInt 88) .Cur .Readable)
    (hdvp : Mem.valid_pointer m Harness.Block.dispatchGraph (zOfInt 0) = true)
    (hdw : Mem.range_perm m Search.Block.dispatch (zOfInt 0) (zOfInt 88) .Cur .Writable)
    (hfp : ∀ b, b = Refine.Block.refine ∨ b = Refine.Block.refine1 ∨ b = Search.Block.updatecanFn ∨
      b = Search.Block.targetcellFn ∨ b = Search.Block.cheapautomFn → Mem.perm m b (zOfInt 0) .Cur .Nonempty)
    (hmarg : PTree.get dense.id.m_arg le = some (.Vint (ir M))) (hM : M < 2147483648)
    (hQ : ∀ le' m', DispatchAt m' M → Unch m m' (· = Search.Block.dispatch) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 703 → x ≠ idOf 704 → x ≠ idOf 705 → x ≠ idOf 706 →
        PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tSizes Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.body Q (nEnv bI) le m := by
  simp only [Nauty.body]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  have hdsp := eval_optF (e := (nEnv bI)) (ty := tptr (.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr))
    hopt fld_dispatch rfl (by decide) (by decide) hO.dispatch
  rw [Exec.evalExpr, hdsp]
  simp only [Exec.evalExpr, typeof, cop]
  have hdgp : Mem.perm m Harness.Block.dispatchGraph (zOfInt 0) .Cur .Nonempty :=
    (Mem.valid_pointer_nonempty_perm m _ _).1 hdvp
  rw [Search.cmp_null_ptr hdgp]
  simp only [Option.map, Val.of_bool, cop]
  rw [ite_eq_right (by decide)]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar,
    show PTree.get Source.dense.id.«nauty:dispatch» (nEnv bI : env) = none from rfl,
    Search.find_dispatch, hdsp, typeof, Exec.derefLoc, Cfrontend.Ctypes.access_mode, hopt, fld_dispatch,
    Mem.loadv]
  have hl104 : Mem.load Mptr m Harness.Block.options (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero
      (Ptrofs.repr (zOfInt 104)))) = some (.Vptr Harness.Block.dispatchGraph Ptrofs.zero) := by
    rw [Search.unsigned_add_off Ptrofs.zero (by decide) (by decide)]
    exact (show Mem.load .Mint64 m _ (zOfInt (intOfZ (Ptrofs.unsigned Ptrofs.zero) + 104)) = _ by
      simpa using hO.dispatch.load)
  rw [hl104]
  simp only [cast_dispatch, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  have hcopy : Exec.copyOk ge.genv_cenv (Cfrontend.Ctypes.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr)
      Search.Block.dispatch Ptrofs.zero Harness.Block.dispatchGraph Ptrofs.zero := by
    refine ⟨?_, ?_, .inl (by decide)⟩ <;> rw [align_dispatch] <;> decide
  have hex : ∀ i : Nat, i < 11 → ∃ v, Mem.load .Mint64 m Harness.Block.dispatchGraph (zOfInt (8 * (i : Int))) =
      some v := fun i hi => ⟨_, hdg i hi⟩
  obtain ⟨bytes, hlb⟩ := lb_of_loads 11 hex
  rw [ite_eq_left hcopy, sizeof_dispatch, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
    show zOfInt 88 = zOfInt (8 * ((11 : Nat) : Int)) from rfl, hlb]
  have hlen : bytes.length = 88 :=
    (Mem.loadbytes_length _ _ _ _ _ hlb).trans (zToNat_zOfInt 88)
  obtain ⟨m1, hst⟩ := Mem.range_perm_storebytes m Search.Block.dispatch (zOfInt 0) bytes (by
    have e : ZArith.BinInt.Z.add (zOfInt 0) (ZArith.BinInt.Z.of_nat bytes.length) = zOfInt 88 :=
      intOfZ_injective (by rw [intOfZ_add, intOfZ_of_nat, hlen]; simp [intOfZ_zOfInt])
    have := hdw; rw [← e] at this; exact this)
  simp only [hst]
  -- the copied fields
  have hld1 : ∀ (i : Nat) (hi : i < 11), Mem.load .Mint64 m1 Search.Block.dispatch (zOfInt (8 * (i : Int))) =
      some (dispatchVals[i]'(by simp [dispatchVals]; omega)) := by
    intro i hi
    have e : (8 * (i : Int)) = ((8 * i : Nat) : Int) := by push_cast; rfl
    have h0 := hdg i hi
    rw [e] at h0 ⊢
    exact copy_load (N := 88) (chunk := .Mint64) (k := 8 * i) (s := 8) hlb hst rfl h0 (by omega)
      ⟨zOfInt i, by apply intOfZ_injective; rw [intOfZ_mul]; simp [intOfZ_zOfInt]; rfl⟩
  have hp1 : ∀ b z, Mem.perm m b z .Cur .Nonempty → Mem.perm m1 b z .Cur .Nonempty :=
    fun b z h => Mem.perm_storebytes_1 _ _ _ _ _ hst _ _ _ _ h
  have hu1 : Unch m m1 (· = Search.Block.dispatch) := Unch.storebytes hst
  have hO1 : OptionsAt m1 := OptionsAt.unch hO hu1 (by decide)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [eval_optF hopt field_oUserrefproc rfl (by decide) (by decide) hO1.userrefproc]
  simp only [typeof]
  rw [bool_null]
  simp only [Bool.false_eq_true, ite_false]
  have hwv : ∀ b, b = Refine.Block.refine ∨ b = Refine.Block.refine1 ∨ b = Search.Block.updatecanFn ∨
      b = Search.Block.targetcellFn ∨ b = Search.Block.cheapautomFn →
      Mem.weak_valid_pointer m1 b (Ptrofs.unsigned Ptrofs.zero) = true := fun b hb => by
    have := (Mem.valid_pointer_nonempty_perm m1 b _).2 (hp1 _ _ (hfp b hb))
    unfold Mem.weak_valid_pointer
    show (Mem.valid_pointer m1 b (zOfInt 0) || _) = true
    rw [this, Bool.true_or]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [eval_dispF Search.field_dRefine1 (by decide) (by decide) (hld1 4 (by decide))]
  rw [show dispatchVals[4] = .Vptr Refine.Block.refine1 Ptrofs.zero from rfl]
  simp only [typeof, cop, hwv _ (.inr (.inl rfl)), ite_true]
  wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hmarg, Refine.tv, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl,
    ir_eq (a := (M : Int)) (b := 1) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩, cast_flag]
  simp only [seqPost, Post.after, E0_append]
  have hw24 : Mem.valid_access m1 .Mint64 Search.Block.dispatch (zOfInt 24) .Writable :=
    ⟨fun o ho => Mem.perm_storebytes_1 _ _ _ _ _ hst _ _ _ _ (hdw o ⟨by
      have := ho.1; change intOfZ _ ≤ intOfZ _ at this ⊢; simp [intOfZ_zOfInt] at this ⊢; omega, by
      have := ho.2; change intOfZ _ < intOfZ _ at this ⊢; rw [intOfZ_add] at this
      simp [intOfZ_zOfInt] at this ⊢; have : intOfZ (Common.Memdata.size_chunk .Mint64) = 8 := rfl
      omega⟩), ⟨zOfInt 3, rfl⟩⟩
  refine wp_subst (M := M) (temps_gss _ _ _) hld1 hw24 fun m2 hld2 hu2 hp2 hv2 => ?_
  simp only [seqPost, Post.after, E0_append]
  have hpf : ∀ b, b = Refine.Block.refine ∨ b = Refine.Block.refine1 ∨ b = Search.Block.updatecanFn ∨
      b = Search.Block.targetcellFn ∨ b = Search.Block.cheapautomFn →
      Mem.perm m2 b (zOfInt 0) .Cur .Nonempty := fun b hb => hp2 _ _ _ _ (hp1 _ _ (hfp b hb))
  obtain ⟨br, hbr, hbr'⟩ := dispatchOf3 M
  have hr := eval_dispNull (bI := bI) (le := PTree.set (idOf 703) (.Vint (if M = 1 then Lib.Integers.Int.one
    else Lib.Integers.Int.zero)) le) (t := Refine.refprocType) Search.field_dRefine (by decide) (by decide)
    ((hld2 3 (by decide)).trans (by rw [hbr])) (hpf br (by rcases hbr' with h | h <;> simp [h]))
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [hr]
  simp only [typeof, cop, Val.of_bool, Bool.false_eq_true, ite_false]
  have hlv : ∀ (i : Nat) (hi : i < 11) (hne : i ≠ 3),
      Mem.load .Mint64 m2 Search.Block.dispatch (zOfInt (8 * (i : Int))) =
        some (dispatchVals[i]'(by simp [dispatchVals]; omega)) := fun i hi hne => by
    rw [hld2 i hi]; simp [dispatchOf, List.getElem_set, Ne.symm hne]
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_dispNull Search.field_dUpdatecan (by decide) (by decide)
    (hlv 2 (by decide) (by decide)) (hpf _ (.inr (.inr (.inl rfl))))]
  simp only [typeof, cop, Val.of_bool, Bool.false_eq_true, ite_false]
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
  rw [ite_eq_right (by decide)]
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_dispNull Search.field_dTargetcell (by decide) (by decide)
    (hlv 6 (by decide) (by decide)) (hpf _ (.inr (.inr (.inr (.inl rfl)))))]
  simp only [typeof, cop, Val.of_bool, Bool.false_eq_true, ite_false]
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
  rw [ite_eq_right (by decide)]
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_dispNull Search.field_dCheapautom (by decide) (by decide)
    (hlv 5 (by decide) (by decide)) (hpf _ (.inr (.inr (.inr (.inr rfl)))))]
  simp only [typeof, cop, Val.of_bool, Bool.false_eq_true, ite_false]
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
  rw [ite_eq_right (by decide)]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  have hwr : ∀ (i : Nat), i < 11 →
      Mem.valid_access m2 .Mint64 Search.Block.dispatch (zOfInt (8 * (i : Int))) .Writable := by
    intro i hi
    refine ⟨fun o ho => hp2 _ _ _ _ (Mem.perm_storebytes_1 _ _ _ _ _ hst _ _ _ _ (hdw o ⟨?_, ?_⟩)),
      ⟨zOfInt i, ?_⟩⟩
    · have := ho.1; change intOfZ _ ≤ intOfZ _ at this ⊢; simp [intOfZ_zOfInt] at this ⊢; omega
    · have := ho.2; change intOfZ _ < intOfZ _ at this ⊢; rw [intOfZ_add] at this
      simp [intOfZ_zOfInt] at this ⊢
      have : intOfZ (Common.Memdata.size_chunk .Mint64) = 8 := rfl
      omega
    · apply intOfZ_injective; rw [intOfZ_mul]; simp [intOfZ_zOfInt]; rfl
  refine hQ _ m2 (fun i hi => ⟨hld2 i hi, hwr i hi⟩) (hu1.trans hu2)
    (fun z h => hv2 _ (Mem.storebytes_valid_block_1 _ _ _ _ _ hst _ h)) (fun x h1 h2 h3 h4 => ?_)
  rw [temps_gso _ _ h4, temps_gso _ _ h3, temps_gso _ _ h2, temps_gso _ _ h1]

end NautyVerified.Proofs.Top

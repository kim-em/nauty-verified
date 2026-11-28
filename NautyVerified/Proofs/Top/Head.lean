import NautyVerified.Proofs.Top.Densenauty
import NautyVerified.Proofs.Top.NautySizes
import NautyVerified.Proofs.Top.Copy
import NautyVerified.Proofs.Top.Fields
import NautyVerified.Proofs.Search.Node.Prologue

/-!
# The head of `nauty()`

`wp_headG`: `dispatch = *options->dispatch` (a copy of the program's dispatch
vector, `dispatchSrcG R` for the dispatch representation `R`), the `refine1`
substitution when `m = 1`, and the four `NULL` checks of the dispatch vector,
which pass. Afterwards `nauty:dispatch` holds `dispatchOfG R M`
(`DispatchAtG`). `OptionsAtG m bo bout bua bdg` is the options block at `bo`
with `outfile`, `userautomproc` and `dispatch` pointing at `bout`, `bua` and
`bdg`.

`wp_head` is the dense instance: the source is `dispatch_graph`, holding
`dispatchVals`, and `DispatchAt m M` is `DispatchAtG denseRep m M`.
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
open NautyVerified.Proofs.Dispatch (Ops DispatchRep denseRep)

set_option linter.unusedSimpArgs false

/-- The options block at `bo` as `nauty()` reads it, with `outfile`,
`userautomproc` and `dispatch` pointing at `bout`, `bua` and `bdg`. -/
structure OptionsAtG (m : mem) (bo bout bua bdg : block) : Prop where
  getcanon : FieldAt m .Mint32 bo 0 (.Vint (ir 1))
  digraph : FieldAt m .Mint32 bo 4 (.Vint (ir 0))
  writeautoms : FieldAt m .Mint32 bo 8 (.Vint (ir 0))
  writemarkers : FieldAt m .Mint32 bo 12 (.Vint (ir 0))
  defaultptn : FieldAt m .Mint32 bo 16 (.Vint (ir 0))
  cartesian : FieldAt m .Mint32 bo 20 (.Vint (ir 0))
  linelength : FieldAt m .Mint32 bo 24 (.Vint (ir 78))
  outfile : FieldAt m .Mint64 bo 32 (.Vptr bout Ptrofs.zero)
  userrefproc : FieldAt m .Mint64 bo 40 Vnullptr
  userautomproc : FieldAt m .Mint64 bo 48 (.Vptr bua Ptrofs.zero)
  userlevelproc : FieldAt m .Mint64 bo 56 Vnullptr
  usernodeproc : FieldAt m .Mint64 bo 64 Vnullptr
  usercanonproc : FieldAt m .Mint64 bo 72 Vnullptr
  invarproc : FieldAt m .Mint64 bo 80 Vnullptr
  tcLevel : FieldAt m .Mint32 bo 88 (.Vint (ir 100))
  mininvarlevel : FieldAt m .Mint32 bo 92 (.Vint (ir 0))
  maxinvarlevel : FieldAt m .Mint32 bo 96 (.Vint (ir 1))
  invararg : FieldAt m .Mint32 bo 100 (.Vint (ir 0))
  dispatch : FieldAt m .Mint64 bo 104 (.Vptr bdg Ptrofs.zero)
  schreier : FieldAt m .Mint32 bo 112 (.Vint (ir 0))
  extraOptions : FieldAt m .Mint64 bo 120 Vnullptr

theorem OptionsAtG.unch {m m' : mem} {S : block → Prop} {bo bout bua bdg : block}
    (h : OptionsAtG m bo bout bua bdg) (hu : Unch m m' S) (hb : ¬ S bo) :
    OptionsAtG m' bo bout bua bdg where
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

/-- The dense harness's options. -/
theorem _root_.NautyVerified.Proofs.Harness.OptionsAt.toG {m : mem} (h : OptionsAt m) :
    OptionsAtG m Harness.Block.options Harness.Block.dummyfile Harness.Block.emitGenerator
      Harness.Block.dispatchGraph :=
  ⟨h.getcanon, h.digraph, h.writeautoms, h.writemarkers, h.defaultptn, h.cartesian, h.linelength,
    h.outfile, h.userrefproc, h.userautomproc, h.userlevelproc, h.usernodeproc, h.usercanonproc,
    h.invarproc, h.tcLevel, h.mininvarlevel, h.maxinvarlevel, h.invararg, h.dispatch, h.schreier,
    h.extraOptions⟩

/-- Reading `options->fld` at byte `off`, the options at `bo`, in any program. -/
theorem eval_optFG {ge : genv} {e : env} {le : temp_env} {m : mem} {fld : ident}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {off : Int} {v : val} {bo : block}
    (hle : PTree.get dense.id.options le = some (.Vptr bo Ptrofs.zero))
    (hfld : ∀ l o, Exec.lvalOfField ge (.Tstruct dense.id.optionstruct Cfrontend.Ctypes.noattr) fld
      (.Vptr l o) = some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (hacc : Cfrontend.Ctypes.access_mode ty = .By_value chunk) (h0 : 0 ≤ off) (h1 : off < 2 ^ 64)
    (hf : FieldAt m chunk bo off v) :
    Exec.evalExpr ge e le m (optF fld ty) = some v := by
  simp only [optF, Exec.evalExpr, hle, typeof, Exec.derefLoc]
  simp only [hacc]
  simp only [Cfrontend.Ctypes.access_mode, Mem.loadv, hfld]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [Search.unsigned_add_off Ptrofs.zero h0 (by simpa using h1)]
  simpa using hf.load

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

theorem cast_flag (m : mem) (M : Nat) :
    Cfrontend.Cop.sem_cast (Val.of_bool (decide ((M : Int) = 1))) tint tbool m =
      some (.Vint (if M = 1 then Lib.Integers.Int.one else Lib.Integers.Int.zero)) := by
  by_cases h : M = 1
  · subst h; rfl
  · rw [decide_eq_false (by omega), if_neg h]; rfl

section Generic

variable {ge : genv} [E : NautyEnv ge] [T : TopEnv ge] {O : Ops}

/-- The dispatch vector of `R` as the program stores it (`dispatch_graph`,
`dispatch_sparse`): `isautom`, `testcanlab`, `updatecan`, `refine`,
`refine1`, `cheapautom`, `targetcell`, `freedyn`, `check`, `init` and
`cleanup = NULL`. -/
def dispatchSrcG (R : DispatchRep ge O) : List val :=
  [.Vptr R.isautom Ptrofs.zero, .Vptr R.testcanlab Ptrofs.zero, .Vptr R.updatecan Ptrofs.zero,
   .Vptr R.refine Ptrofs.zero, .Vptr R.refine1 Ptrofs.zero, .Vptr R.cheapautom Ptrofs.zero,
   .Vptr R.targetcell Ptrofs.zero, .Vptr R.freedyn Ptrofs.zero, .Vptr R.check Ptrofs.zero, R.init,
   Vnullptr]

/-- The dispatch vector `nauty()` uses: `refine` is `R.refineAt M`. -/
def dispatchOfG (R : DispatchRep ge O) (M : Nat) : List val :=
  (dispatchSrcG R).set 3 (.Vptr (R.refineAt M) Ptrofs.zero)

theorem dispatchSrcG_length (R : DispatchRep ge O) : (dispatchSrcG R).length = 11 := rfl

theorem dispatchOfG_length (R : DispatchRep ge O) (M : Nat) : (dispatchOfG R M).length = 11 := by
  simp [dispatchOfG, dispatchSrcG]

/-- `nauty:dispatch` holds `dispatchOfG R M`. -/
def DispatchAtG (R : DispatchRep ge O) (m : mem) (M : Nat) : Prop :=
  ∀ (i : Nat) (hi : i < 11), FieldAt m .Mint64 E.dispatch (8 * (i : Int))
    ((dispatchOfG R M)[i]'(by rw [dispatchOfG_length]; exact hi))

theorem dispatchOfG_ne (R : DispatchRep ge O) {M : Nat} (h : M ≠ 1) :
    dispatchOfG R M = dispatchSrcG R := by
  simp [dispatchOfG, dispatchSrcG, DispatchRep.refineAt, h]

theorem dispatchOfG_get (R : DispatchRep ge O) (M : Nat) {i : Nat} (hi : i < 11) (h3 : i ≠ 3) :
    (dispatchOfG R M)[i]'(by rw [dispatchOfG_length]; exact hi) =
      (dispatchSrcG R)[i]'(by rw [dispatchSrcG_length]; exact hi) := by
  simp [dispatchOfG, List.getElem_set, Ne.symm h3]

theorem dispatchOfG3 (R : DispatchRep ge O) (M : Nat) :
    (dispatchOfG R M)[3]'(by rw [dispatchOfG_length]; decide) = .Vptr (R.refineAt M) Ptrofs.zero := by
  simp [dispatchOfG, dispatchSrcG]

theorem refineAt_cases (R : DispatchRep ge O) (M : Nat) :
    R.refineAt M = R.refine ∨ R.refineAt M = R.refine1 := by
  unfold DispatchRep.refineAt; split
  · exact .inr rfl
  · exact .inl rfl

theorem eval_dispF {le : temp_env} {m : mem} {fld : ident} {t : Cfrontend.Ctypes.type} {off : Int} {v : val}
    (hfld : ∀ l o, Exec.lvalOfField ge (.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr) fld (.Vptr l o) =
      some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (h0 : 0 ≤ off) (h1 : off < 2 ^ 64)
    (hl : Mem.load .Mint64 m E.dispatch (zOfInt off) = some v) :
    Exec.evalExpr ge (nEnv bI) le m (dispF fld (tptr t)) = some v := by
  simp only [dispF, Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar,
    show PTree.get Source.dense.id.«nauty:dispatch» (nEnv bI : env) = none from rfl,
    E.find_dispatch, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, typeof]
  rw [hfld]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [Search.unsigned_add_off Ptrofs.zero h0 (by simpa using h1)]
  exact (show Mem.load .Mint64 m _ (zOfInt (intOfZ (Ptrofs.unsigned Ptrofs.zero) + off)) = _ by
    simpa using hl)

/-- `dispatch.refine` as a store target. -/
theorem lval_dispF {le : temp_env} {m : mem} {fld : ident} {t : Cfrontend.Ctypes.type} {off : Int}
    (hfld : ∀ l o, Exec.lvalOfField ge (.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr) fld (.Vptr l o) =
      some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full)) :
    Exec.evalLvalue ge (nEnv bI) le m (dispF fld (tptr t)) =
      some (E.dispatch, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt off)), .Full) := by
  simp only [dispF, Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar,
    show PTree.get Source.dense.id.«nauty:dispatch» (nEnv bI : env) = none from rfl,
    E.find_dispatch, Exec.derefLoc, Cfrontend.Ctypes.access_mode, typeof]
  exact hfld _ _

/-- `dispatch.fld == NULL` for a function pointer field. -/
theorem eval_dispNull {le : temp_env} {m : mem} {fld : ident} {t : Cfrontend.Ctypes.type} {off : Int}
    {b : block}
    (hfld : ∀ l o, Exec.lvalOfField ge (.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr) fld (.Vptr l o) =
      some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (h0 : 0 ≤ off) (h1 : off < 2 ^ 64)
    (hl : Mem.load .Mint64 m E.dispatch (zOfInt off) = some (.Vptr b Ptrofs.zero))
    (hp : Mem.perm m b (zOfInt 0) .Cur .Nonempty) :
    Exec.evalExpr ge (nEnv bI) le m (.Ebinop .Oeq (dispF fld (tptr t)) (.Ecast (ci 0 tint) (tptr .Tvoid))
      tint) = some (Val.of_bool false) := by
  rw [Exec.evalExpr, eval_dispF hfld h0 h1 hl]
  simp only [Exec.evalExpr, typeof, cop]
  rw [Search.cmp_null_ptr hp]
  rfl

set_option maxRecDepth 20000 in
variable {xi : ExternalCalls} in
/-- `if (m == 1 && dispatch.refine1) dispatch.refine = dispatch.refine1;` -/
theorem wp_substG (R : DispatchRep ge O) {f : function} {Q : Post} {le : temp_env} {m1 : mem} {M : Nat}
    (h703 : PTree.get (idOf 703) le =
      some (.Vint (if M = 1 then Lib.Integers.Int.one else Lib.Integers.Int.zero)))
    (hld1 : ∀ (i : Nat) (hi : i < 11), Mem.load .Mint64 m1 E.dispatch (zOfInt (8 * (i : Int))) =
      some ((dispatchSrcG R)[i]'(by rw [dispatchSrcG_length]; exact hi)))
    (hw24 : Mem.valid_access m1 .Mint64 E.dispatch (zOfInt 24) .Writable)
    (hQ : ∀ m2, (∀ (i : Nat) (hi : i < 11), Mem.load .Mint64 m2 E.dispatch (zOfInt (8 * (i : Int))) =
        some ((dispatchOfG R M)[i]'(by rw [dispatchOfG_length]; exact hi))) →
      Unch m1 m2 (· = E.dispatch) →
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
    obtain ⟨m2, hst⟩ := Mem.valid_access_store m1 Mptr _ _ (.Vptr R.refine1 Ptrofs.zero) hw24
    wp_step; wp_step
    apply wp_assign_eval
    rw [lval_dispF E.field_dRefine, eval_dispF E.field_dRefine1 (by decide) (by decide)
      (hld1 4 (by decide))]
    rw [show (dispatchSrcG R)[4]'(by rw [dispatchSrcG_length]; decide) = .Vptr R.refine1 Ptrofs.zero from rfl]
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
      rw [dispatchOfG3]
      simp [DispatchRep.refineAt, hM1]; rfl
    · rw [Mem.load_store_other _ _ _ _ _ _ hst _ _ _ (.inr (by
        rcases Nat.lt_or_gt_of_ne h3 with h | h
        · left; change intOfZ _ ≤ intOfZ _; rw [intOfZ_add]; simp [intOfZ_zOfInt]
          change 8 * (i : Int) + 8 ≤ 24; omega
        · right; change intOfZ _ ≤ intOfZ _; rw [intOfZ_add]; simp [intOfZ_zOfInt]
          change 24 + 8 ≤ 8 * (i : Int); omega)), hld1 i hi, dispatchOfG_get R M hi h3]
  · rw [if_neg hM1]
    rw [ite_eq_right (by decide)]
    apply wp_skip
    refine hQ m1 (fun i hi => ?_) (Unch.refl _ _) (fun _ _ _ _ h => h) (fun _ h => h)
    rw [hld1 i hi]
    simp [dispatchOfG_ne R hM1]

set_option maxRecDepth 20000 in
variable {xi : ExternalCalls} in
/-- The head of `nauty()` for the dispatch representation `R`, the options at
`bo` and the program's dispatch vector at `bdg`. -/
theorem wp_headG (R : DispatchRep ge O) {Q : Post} {le : temp_env} {m : mem} {M : Nat}
    {bo bout bua bdg : block}
    (hopt : PTree.get dense.id.options le = some (.Vptr bo Ptrofs.zero))
    (hO : OptionsAtG m bo bout bua bdg) (hbo : bo ≠ E.dispatch)
    (hdg : ∀ (i : Nat) (hi : i < 11), Mem.load .Mint64 m bdg (zOfInt (8 * (i : Int))) =
      some ((dispatchSrcG R)[i]'(by rw [dispatchSrcG_length]; exact hi)))
    (hdvp : Mem.valid_pointer m bdg (zOfInt 0) = true) (hdgd : E.dispatch ≠ bdg)
    (hdw : Mem.range_perm m E.dispatch (zOfInt 0) (zOfInt 88) .Cur .Writable)
    (hfp : ∀ b, b = R.refine ∨ b = R.refine1 ∨ b = R.updatecan ∨
      b = R.targetcell ∨ b = R.cheapautom → Mem.perm m b (zOfInt 0) .Cur .Nonempty)
    (hmarg : PTree.get dense.id.m_arg le = some (.Vint (ir M))) (hM : M < 2147483648)
    (hQ : ∀ le' m', DispatchAtG R m' M → Unch m m' (· = E.dispatch) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 703 → x ≠ idOf 704 → x ≠ idOf 705 → x ≠ idOf 706 →
        PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tSizes Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.body Q (nEnv bI) le m := by
  simp only [Nauty.body]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  have hdsp := eval_optFG (e := (nEnv bI)) (ty := tptr (.Tstruct dense.id.«_1027» Cfrontend.Ctypes.noattr))
    hopt T.field_oDispatch rfl (by decide) (by decide) hO.dispatch
  rw [Exec.evalExpr, hdsp]
  simp only [Exec.evalExpr, typeof, cop]
  have hdgp : Mem.perm m bdg (zOfInt 0) .Cur .Nonempty :=
    (Mem.valid_pointer_nonempty_perm m _ _).1 hdvp
  rw [Search.cmp_null_ptr hdgp]
  simp only [Option.map, Val.of_bool, cop]
  rw [ite_eq_right (by decide)]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar,
    show PTree.get Source.dense.id.«nauty:dispatch» (nEnv bI : env) = none from rfl,
    E.find_dispatch, hdsp, typeof, Exec.derefLoc, Cfrontend.Ctypes.access_mode, hopt, T.field_oDispatch,
    Mem.loadv]
  have hl104 : Mem.load Mptr m bo (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero
      (Ptrofs.repr (zOfInt 104)))) = some (.Vptr bdg Ptrofs.zero) := by
    rw [Search.unsigned_add_off Ptrofs.zero (by decide) (by decide)]
    exact (show Mem.load .Mint64 m _ (zOfInt (intOfZ (Ptrofs.unsigned Ptrofs.zero) + 104)) = _ by
      simpa using hO.dispatch.load)
  rw [hl104]
  simp only [cast_dispatch, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  have hcopy : Exec.copyOk ge.genv_cenv (Cfrontend.Ctypes.Tstruct dense.id._1027 Cfrontend.Ctypes.noattr)
      E.dispatch Ptrofs.zero bdg Ptrofs.zero := by
    refine ⟨?_, ?_, .inl hdgd.symm⟩ <;> rw [T.align_dispatch] <;> decide
  have hex : ∀ i : Nat, i < 11 → ∃ v, Mem.load .Mint64 m bdg (zOfInt (8 * (i : Int))) =
      some v := fun i hi => ⟨_, hdg i hi⟩
  obtain ⟨bytes, hlb⟩ := lb_of_loads 11 hex
  rw [ite_eq_left hcopy, T.sizeof_dispatch, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
    show zOfInt 88 = zOfInt (8 * ((11 : Nat) : Int)) from rfl, hlb]
  have hlen : bytes.length = 88 :=
    (Mem.loadbytes_length _ _ _ _ _ hlb).trans (zToNat_zOfInt 88)
  obtain ⟨m1, hst⟩ := Mem.range_perm_storebytes m E.dispatch (zOfInt 0) bytes (by
    have e : ZArith.BinInt.Z.add (zOfInt 0) (ZArith.BinInt.Z.of_nat bytes.length) = zOfInt 88 :=
      intOfZ_injective (by rw [intOfZ_add, intOfZ_of_nat, hlen]; simp [intOfZ_zOfInt])
    have := hdw; rw [← e] at this; exact this)
  simp only [hst]
  -- the copied fields
  have hld1 : ∀ (i : Nat) (hi : i < 11), Mem.load .Mint64 m1 E.dispatch (zOfInt (8 * (i : Int))) =
      some ((dispatchSrcG R)[i]'(by rw [dispatchSrcG_length]; exact hi)) := by
    intro i hi
    have e : (8 * (i : Int)) = ((8 * i : Nat) : Int) := by push_cast; rfl
    have h0 := hdg i hi
    rw [e] at h0 ⊢
    exact copy_load (N := 88) (chunk := .Mint64) (k := 8 * i) (s := 8) hlb hst rfl h0 (by omega)
      ⟨zOfInt i, by apply intOfZ_injective; rw [intOfZ_mul]; simp [intOfZ_zOfInt]; rfl⟩
  have hp1 : ∀ b z, Mem.perm m b z .Cur .Nonempty → Mem.perm m1 b z .Cur .Nonempty :=
    fun b z h => Mem.perm_storebytes_1 _ _ _ _ _ hst _ _ _ _ h
  have hu1 : Unch m m1 (· = E.dispatch) := Unch.storebytes hst
  have hO1 : OptionsAtG m1 bo bout bua bdg := OptionsAtG.unch hO hu1 hbo
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [eval_optFG hopt T.field_oUserrefproc rfl (by decide) (by decide) hO1.userrefproc]
  simp only [typeof]
  rw [bool_null]
  simp only [Bool.false_eq_true, ite_false]
  have hwv : ∀ b, b = R.refine ∨ b = R.refine1 ∨ b = R.updatecan ∨
      b = R.targetcell ∨ b = R.cheapautom →
      Mem.weak_valid_pointer m1 b (Ptrofs.unsigned Ptrofs.zero) = true := fun b hb => by
    have := (Mem.valid_pointer_nonempty_perm m1 b _).2 (hp1 _ _ (hfp b hb))
    unfold Mem.weak_valid_pointer
    show (Mem.valid_pointer m1 b (zOfInt 0) || _) = true
    rw [this, Bool.true_or]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [eval_dispF E.field_dRefine1 (by decide) (by decide) (hld1 4 (by decide))]
  rw [show (dispatchSrcG R)[4]'(by rw [dispatchSrcG_length]; decide) = .Vptr R.refine1 Ptrofs.zero from rfl]
  simp only [typeof, cop, hwv _ (.inr (.inl rfl)), ite_true]
  wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hmarg, Refine.tv, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl,
    ir_eq (a := (M : Int)) (b := 1) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩, cast_flag]
  simp only [seqPost, Post.after, E0_append]
  have hw24 : Mem.valid_access m1 .Mint64 E.dispatch (zOfInt 24) .Writable :=
    ⟨fun o ho => Mem.perm_storebytes_1 _ _ _ _ _ hst _ _ _ _ (hdw o ⟨by
      have := ho.1; change intOfZ _ ≤ intOfZ _ at this ⊢; simp [intOfZ_zOfInt] at this ⊢; omega, by
      have := ho.2; change intOfZ _ < intOfZ _ at this ⊢; rw [intOfZ_add] at this
      simp [intOfZ_zOfInt] at this ⊢; have : intOfZ (Common.Memdata.size_chunk .Mint64) = 8 := rfl
      omega⟩), ⟨zOfInt 3, rfl⟩⟩
  refine wp_substG R (M := M) (temps_gss _ _ _) hld1 hw24 fun m2 hld2 hu2 hp2 hv2 => ?_
  simp only [seqPost, Post.after, E0_append]
  have hpf : ∀ b, b = R.refine ∨ b = R.refine1 ∨ b = R.updatecan ∨
      b = R.targetcell ∨ b = R.cheapautom →
      Mem.perm m2 b (zOfInt 0) .Cur .Nonempty := fun b hb => hp2 _ _ _ _ (hp1 _ _ (hfp b hb))
  have hr := eval_dispNull (bI := bI) (le := PTree.set (idOf 703) (.Vint (if M = 1 then Lib.Integers.Int.one
    else Lib.Integers.Int.zero)) le) (t := Refine.refprocType) E.field_dRefine (by decide) (by decide)
    ((hld2 3 (by decide)).trans (by rw [dispatchOfG3]))
    (hpf _ (by rcases refineAt_cases R M with h | h <;> simp [h]))
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [hr]
  simp only [typeof, cop, Val.of_bool, Bool.false_eq_true, ite_false]
  have hlv : ∀ (i : Nat) (hi : i < 11) (hne : i ≠ 3),
      Mem.load .Mint64 m2 E.dispatch (zOfInt (8 * (i : Int))) =
        some ((dispatchSrcG R)[i]'(by rw [dispatchSrcG_length]; exact hi)) := fun i hi hne => by
    rw [hld2 i hi, dispatchOfG_get R M hi hne]
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_dispNull E.field_dUpdatecan (by decide) (by decide)
    (hlv 2 (by decide) (by decide)) (hpf _ (.inr (.inr (.inl rfl))))]
  simp only [typeof, cop, Val.of_bool, Bool.false_eq_true, ite_false]
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
  rw [ite_eq_right (by decide)]
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_dispNull E.field_dTargetcell (by decide) (by decide)
    (hlv 6 (by decide) (by decide)) (hpf _ (.inr (.inr (.inr (.inl rfl)))))]
  simp only [typeof, cop, Val.of_bool, Bool.false_eq_true, ite_false]
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
  rw [ite_eq_right (by decide)]
  wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_dispNull E.field_dCheapautom (by decide) (by decide)
    (hlv 5 (by decide) (by decide)) (hpf _ (.inr (.inr (.inr (.inr rfl)))))]
  simp only [typeof, cop, Val.of_bool, Bool.false_eq_true, ite_false]
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, Refine.tv, typeof, cop]
  rw [ite_eq_right (by decide)]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  have hwr : ∀ (i : Nat), i < 11 →
      Mem.valid_access m2 .Mint64 E.dispatch (zOfInt (8 * (i : Int))) .Writable := by
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

end Generic

/-! ### The dense instance -/

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

theorem dispatchSrcG_dense : dispatchSrcG denseRep = dispatchVals := rfl

theorem dispatchOfG_dense (M : Nat) : dispatchOfG denseRep M = dispatchOf M := by
  by_cases h : M = 1 <;> simp [dispatchOfG, dispatchOf, dispatchSrcG_dense, DispatchRep.refineAt, h] <;> rfl

theorem DispatchAtG.dense {m : mem} {M : Nat} (h : DispatchAtG denseRep m M) : DispatchAt m M :=
  fun i hi => by
    have := h i hi
    simp only [dispatchOfG_dense] at this
    exact this

theorem DispatchAt.toG {m : mem} {M : Nat} (h : DispatchAt m M) : DispatchAtG denseRep m M :=
  fun i hi => by
    simp only [DispatchAtG, dispatchOfG_dense]
    exact h i hi

theorem dispatchOf_ne {M : Nat} (h : M ≠ 1) : dispatchOf M = dispatchVals := by
  simp [dispatchOf, dispatchVals, h]

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
    Wp xi ge dense.fn.nauty Nauty.body Q (nEnv bI) le m :=
  wp_headG denseRep hopt hO.toG (by decide) hdg hdvp (by decide) hdw hfp hmarg hM
    fun le' m' hD hu hv ht => hQ le' m' hD.dense hu hv ht

end NautyVerified.Proofs.Top

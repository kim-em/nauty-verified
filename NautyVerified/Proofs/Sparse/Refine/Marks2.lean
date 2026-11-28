import NautyVerified.Proofs.Sparse.Prep
import NautyVerified.Proofs.Sparse.Refine.Blocks

/-!
# nausparse.c's second mark array

`vmark2`, its capacity `vmark2_sz` and stamp `vmark2_val`, which only
`refine_sg` uses (`MARK2`, `ISMARKED2`, `RESETMARKS2`, `preparemarks2`):
`Proofs/Sparse/Marks.lean` and `Proofs/Sparse/Prep.lean` for these globals.
`MarksAt`, `wp_resetmarks2` and `prep_satisfies` here are those files'
`MarksAt`, `wp_resetmarks1` and `prep_satisfies` with `vmark2` for `vmark1`.
-/

namespace NautyVerified.Proofs.Sparse.Marks2

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Program NautyVerified.Proofs.Sparse.Refine

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

namespace id
abbrev vmark2 : ident := sparse.id.«nausparse:vmark2»
abbrev vmark2Sz : ident := sparse.id.«nausparse:vmark2_sz»
abbrev vmark2Val : ident := sparse.id.«nausparse:vmark2_val»
end id

/-- The marks invariant (see the module docstring). -/
structure MarksAt (m : mem) (cap : Nat) (b : block) (st : Nat) (marks : Nat → Int) : Prop where
  dyn : Alloc.DynAt m Block.vmark2 Block.vmark2Sz 2 cap b
  valLd : Mem.load .Mint16signed m Block.vmark2Val (zOfInt 0) = some (.Vint (ir st))
  valW : Mem.valid_access m .Mint16signed Block.vmark2Val (zOfInt 0) .Writable
  val1 : 1 ≤ st
  val32 : st ≤ 32000
  arr : ArrayAt m .Mint16signed b 0 (markVals marks) cap
  bounds : ∀ i < cap, 0 ≤ marks i ∧ marks i ≤ st
  bval : 0 < cap → b ≠ Block.vmark2Val

/-- `RESETMARKS2`, with temporaries `t` (the old stamp) and `ij` (the index). -/
abbrev resetmarks2 (t ij : ident) : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence .Sskip (.Sset t (.Evar id.vmark2Val tshort)))
      (.Sassign (.Evar id.vmark2Val tshort) (.Ebinop .Oadd (.Etempvar t tshort) (ci 1 tint) tint)))
    (.Sifthenelse (.Ebinop .Oge (.Etempvar t tshort) (ci 32000 tint) tint)
      (.Ssequence
        (.Ssequence
          (.Ssequence .Sskip (.Sset ij (.Ecast (ci 0 tint) tulong)))
          (.Sloop
            (.Ssequence
              (.Ssequence .Sskip
                (.Sifthenelse (.Ebinop .Olt (.Etempvar ij tulong) (.Evar id.vmark2Sz tulong) tint)
                  .Sskip .Sbreak))
              (.Ssequence .Sskip
                (.Sassign (.Ederef (.Ebinop .Oadd (.Evar id.vmark2 (tptr tshort))
                  (.Etempvar ij tulong) (tptr tshort)) tshort) (ci 0 tint))))
            (.Ssequence .Sskip (.Sset ij (.Ebinop .Oadd (.Etempvar ij tulong) (ci 1 tint) tulong)))))
        (.Ssequence .Sskip (.Sassign (.Evar id.vmark2Val tshort) (ci 1 tint))))
      .Sskip)

theorem eval_val {le : temp_env} {m : mem} {st : Nat}
    (h : Mem.load .Mint16signed m Block.vmark2Val (zOfInt 0) = some (.Vint (ir st))) :
    Exec.evalExpr sge empty_env le m (.Evar id.vmark2Val tshort) = some (.Vint (ir st)) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.vmark2Val (empty_env : env) = none from rfl,
    find_vmark2Val, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv]
  exact h

/-- Storing a `short` stamp `x`. -/
theorem wp_storeVal {f : function} {Q : Post} {le : temp_env} {m : mem} {rhs : expr} {x : Nat}
    (hx : x < 32768) (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hW : Mem.valid_access m .Mint16signed Block.vmark2Val (zOfInt 0) .Writable)
    (hQ : ∀ m', Mem.store .Mint16signed m Block.vmark2Val (zOfInt 0) (.Vint (ir x)) = some m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (.Evar id.vmark2Val tshort) rhs) Q empty_env le m := by
  have hse := Search.sign_ext16_ir (a := (x : Int)) (by omega) (by omega)
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ (.Vint (ir x)) hW
  apply wp_assign_eval
  simp only [hrhs, Exec.evalLvalue, Exec.lvalOfVar,
    show PTree.get id.vmark2Val (empty_env : env) = none from rfl, find_vmark2Val, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [hse, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hst]
  exact hQ m' hst

/-- The zeroing loop of `RESETMARKS2`. -/
abbrev zeroLoop (ij : ident) : statement :=
  .Sloop
    (.Ssequence
      (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar ij tulong) (.Evar id.vmark2Sz tulong) tint)
          .Sskip .Sbreak))
      (.Ssequence .Sskip
        (.Sassign (.Ederef (.Ebinop .Oadd (.Evar id.vmark2 (tptr tshort))
          (.Etempvar ij tulong) (tptr tshort)) tshort) (ci 0 tint))))
    (.Ssequence .Sskip (.Sset ij (.Ebinop .Oadd (.Etempvar ij tulong) (ci 1 tint) tulong)))

theorem eval_sz {le : temp_env} {m : mem} {cap : Nat}
    (h : Mem.load .Mint64 m Block.vmark2Sz (zOfInt 0) = some (.Vlong (lr cap))) :
    Exec.evalExpr sge empty_env le m (.Evar id.vmark2Sz tulong) = some (.Vlong (lr cap)) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.vmark2Sz (empty_env : env) = none from rfl,
    find_vmark2Sz, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv]
  exact h

theorem eval_vmark2 {le : temp_env} {m : mem} {b : block}
    (h : Mem.load .Mint64 m Block.vmark2 (zOfInt 0) = some (.Vptr b Ptrofs.zero)) :
    Exec.evalExpr sge empty_env le m (.Evar id.vmark2 (tptr tshort)) = some (.Vptr b Ptrofs.zero) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.vmark2 (empty_env : env) = none from rfl,
    find_vmark2, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq]
  exact h

theorem wp_zeroLoop {f : function} {Q : Post} {le : temp_env} {m : mem} {cap : Nat} {b : block}
    {marks : Nat → Int} {ij : ident}
    (hcap : Mem.load .Mint64 m Block.vmark2Sz (zOfInt 0) = some (.Vlong (lr cap)))
    (hcapLt : cap < 2147483648)
    (hp : 0 < cap → Mem.load .Mint64 m Block.vmark2 (zOfInt 0) = some (.Vptr b Ptrofs.zero))
    (harr : ArrayAt m .Mint16signed b 0 (markVals marks) cap)
    (hb : 0 < cap → b ≠ Block.vmark2Sz ∧ b ≠ Block.vmark2)
    (hij : PTree.get ij le = some (.Vlong (lr 0)))
    (hQ : ∀ le' m', ArrayAt m' .Mint16signed b 0 (markVals fun _ => 0) cap →
      Unch m m' (fun z => 0 < cap ∧ z = b) → Alloc.Keep m m' b → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ ij → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge f (zeroLoop ij) Q empty_env le m := by
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k, k ≤ cap ∧ v = cap - k ∧ PTree.get ij le' = some (.Vlong (lr k)) ∧
      ArrayAt m' .Mint16signed b 0 (markVals fun i => if i < k then 0 else marks i) cap ∧
      Unch m m' (fun z => 0 < cap ∧ z = b) ∧ Alloc.Keep m m' b ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧ ∀ x, x ≠ ij → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k, k < cap ∧ v = cap - k ∧ PTree.get ij le' = some (.Vlong (lr k)) ∧
      ArrayAt m' .Mint16signed b 0 (markVals fun i => if i < k + 1 then 0 else marks i) cap ∧
      Unch m m' (fun z => 0 < cap ∧ z = b) ∧ Alloc.Keep m m' b ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧ ∀ x, x ≠ ij → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := cap - 0)
    ⟨rfl, rfl, 0, Nat.zero_le _, rfl, hij, harr.congr fun i _ => by simp [markVals],
      Unch.refl _ _, Alloc.Keep.refl _ _, fun _ h => h, fun _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, k, hk, rfl, hk', harr', hu, hkp, hg, ho⟩
    have hcap' : Mem.load .Mint64 m' Block.vmark2Sz (zOfInt 0) = some (.Vlong (lr cap)) := by
      rw [hu.load _ _ _ (fun ⟨hc, h⟩ => (hb hc).1 h.symm)]; exact hcap
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (.Etempvar ij tulong) = _ from hk',
      eval_sz hcap']
    simp only [typeof, cop, Alloc.ltu_lr (a := k) (b := cap) (by omega) (by omega)]
    by_cases hkc : k < cap
    · rw [ite_eq_left (by simpa using hkc)]
      apply wp_skip
      have hp' : Mem.load .Mint64 m' Block.vmark2 (zOfInt 0) = some (.Vptr b Ptrofs.zero) := by
        rw [hu.load _ _ _ (fun ⟨hc, h⟩ => (hb hc).2 h.symm)]; exact hp (by omega)
      wp_step; wp_step
      refine wp_idx_store_l (chunk := .Mint16signed) (bo := b) (ofs := Ptrofs.zero) harr' (by omega)
        (eval_vmark2 hp') rfl rfl rfl (.Etempvar ij tulong) k hkc hk' rfl _ tint rfl _ (.Vint (ir 0)) rfl
        (cast_zero_short m') rfl ?_
      intro m'' harr'' hu' hkp' hg'
      refine ⟨by simp, rfl, k, hkc, rfl, hk', harr''.congr fun i _ => ?_,
        hu.trans (hu'.mono fun z hz => ⟨by omega, hz⟩), hkp.trans hkp', fun z h => hg' _ (hg _ h), ho⟩
      by_cases hik : i = k
      · subst hik; simp [markVals]
      · rw [upd_ne _ _ hik]; simp only [markVals]
        by_cases hi : i < k
        · rw [ite_eq_left hi, ite_eq_left (show i < k + 1 by omega)]
        · rw [ite_eq_right hi, ite_eq_right (show ¬ i < k + 1 by omega)]
    · rw [ite_eq_right (by simpa using hkc)]
      apply wp_break
      have : k = cap := by omega
      subst this
      exact hQ le' m' (harr'.congr fun i hi => by simp [markVals, hi]) hu hkp hg ho
  · rintro v t e' le' m' ⟨rfl, rfl, k, hk, rfl, hk', harr', hu, hkp, hg, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (.Etempvar ij tulong) = _ from hk']
    simp only [Exec.evalExpr, typeof, cop, Alloc.add_lr_one]
    exact ⟨cap - (k + 1), by omega, by simp, rfl, k + 1, hk, rfl, temps_gss _ _ _, harr', hu, hkp, hg,
      fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩

/-- `RESETMARKS2`: afterwards every entry is below the stamp. -/
theorem wp_resetmarks2 {f : function} {Q : Post} {le : temp_env} {m : mem} {cap : Nat} {b : block}
    {st : Nat} {marks : Nat → Int} {t ij : ident}
    (hM : MarksAt m cap b st marks)
    (hQ : ∀ le' m' val' marks', MarksAt m' cap b val' marks' → (∀ i < cap, marks' i < val') →
      Unch m m' (fun z => z = Block.vmark2Val ∨ (0 < cap ∧ z = b)) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ t → x ≠ ij → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge f (resetmarks2 t ij) Q empty_env le m := by
  have hV1 := hM.val1
  have hV2 := hM.val32
  have hD := hM.dyn
  have hne1 : Block.vmark2Val ≠ Block.vmark2 := by decide
  have hne2 : Block.vmark2Val ≠ Block.vmark2Sz := by decide
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_val hM.valLd]
  let le1 := PTree.set t (.Vint (ir st)) le
  have ht1 : PTree.get t le1 = some (.Vint (ir st)) := temps_gss _ _ _
  refine wp_storeVal (x := st + 1) (by omega) ?_ rfl hM.valW ?_
  · simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]; push_cast; rfl
  intro m1 hst1
  have hu1 : Unch m m1 (· = Block.vmark2Val) := Unch.store hst1 rfl
  have hval1 : Mem.load .Mint16signed m1 Block.vmark2Val (zOfInt 0) = some (.Vint (ir (st + 1))) := by
    have := Mem.load_store_same _ _ _ _ _ _ hst1
    rw [this]
    exact congrArg (fun x => some (val.Vint x)) (Search.sign_ext16_ir (a := ((st + 1 : Nat) : Int))
      (by omega) (by omega))
  have hW1 : Mem.valid_access m1 .Mint16signed Block.vmark2Val (zOfInt 0) .Writable :=
    Mem.store_valid_access_1 _ _ _ _ _ _ hst1 _ _ _ _ hM.valW
  have hg1 : ∀ z, Mem.valid_block m z → Mem.valid_block m1 z :=
    fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hst1 _ h
  have hnb : 0 < cap → ¬ b = Block.vmark2Val := fun hc h => hM.bval hc h
  have hD1 : Alloc.DynAt m1 Block.vmark2 Block.vmark2Sz 2 cap b :=
    { hD with
      capLd := by rw [hu1.load _ _ _ hne2.symm]; exact hD.capLd
      bsW := hu1.access _ _ _ _ hne2.symm hD.bsW
      bpW := hu1.access _ _ _ _ hne1.symm hD.bpW
      ptr := fun hc => by rw [hu1.load _ _ _ hne1.symm]; exact hD.ptr hc
      mal := fun hc => (hD.mal hc).keep (Alloc.Keep.unch hu1 (hnb hc))
      null := fun hc => by rw [hu1.load _ _ _ hne1.symm]; exact hD.null hc }
  have harr1 : ArrayAt m1 .Mint16signed b 0 (markVals marks) cap := by
    by_cases hc : 0 < cap
    · exact hM.arr.unch hu1 (hnb hc)
    · have : cap = 0 := by omega
      subst this; exact ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
        fun _ h => absurd h (by omega)⟩
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, typeof, cop]
  rw [ir_lt (a := (st : Int)) (b := 32000) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
  have hle1 : ∀ x, x ≠ t → PTree.get x le1 = PTree.get x le := fun x hx => temps_gso _ _ hx
  by_cases hv : st < 32000
  · rw [show decide ((st : Int) < 32000) = true from decide_eq_true (by omega)]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [E0_append]
    refine hQ le1 m1 (st + 1) marks ⟨hD1, by rw [hval1]; push_cast; rfl, hW1, by omega, by omega,
      harr1, fun i hi => ⟨(hM.bounds i hi).1, by have := (hM.bounds i hi).2; omega⟩, hM.bval⟩
      (fun i hi => by have := (hM.bounds i hi).2; omega) (hu1.mono fun z hz => .inl hz) hg1
      (fun x hx _ => hle1 x hx)
  · have hst : st = 32000 := by omega
    subst hst
    rw [show decide (((32000 : Nat) : Int) < 32000) = false by decide]
    simp only [Bool.not_false, ite_true]
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
    let le2 := PTree.set ij (.Vlong (lr 0)) le1
    refine wp_zeroLoop (le := le2) hD1.capLd hD1.capLt hD1.ptr harr1 hD1.bne (temps_gss _ _ _) ?_
    intro le3 m3 harr3 hu3 hkp3 hg3 ho3
    wp_step; wp_step
    have hW3 : Mem.valid_access m3 .Mint16signed Block.vmark2Val (zOfInt 0) .Writable :=
      hu3.access _ _ _ _ (fun ⟨hc, h⟩ => hnb hc h.symm) hW1
    refine wp_storeVal (x := 1) (by decide) (by simp only [Exec.evalExpr]; rfl) rfl hW3 ?_
    intro m4 hst4
    have hu4 : Unch m3 m4 (· = Block.vmark2Val) := Unch.store hst4 rfl
    have hnS : ∀ z, (z = Block.vmark2 ∨ z = Block.vmark2Sz) →
        ¬ ((z = Block.vmark2Val) ∨ (0 < cap ∧ z = b)) := by
      rintro z (rfl | rfl) (h | ⟨hc, h⟩)
      · exact hne1 h.symm
      · exact (hD.bne hc).2 h.symm
      · exact hne2 h.symm
      · exact (hD.bne hc).1 h.symm
    have hu : Unch m m4 (fun z => z = Block.vmark2Val ∨ (0 < cap ∧ z = b)) :=
      ((hu1.mono fun z hz => .inl hz).trans (hu3.mono fun z hz => .inr hz)).trans
        (hu4.mono fun z hz => .inl hz)
    have hval4 : Mem.load .Mint16signed m4 Block.vmark2Val (zOfInt 0) = some (.Vint (ir 1)) := by
      rw [Mem.load_store_same _ _ _ _ _ _ hst4]; rfl
    have harr4 : ArrayAt m4 .Mint16signed b 0 (markVals fun _ => 0) cap := by
      by_cases hc : 0 < cap
      · exact harr3.unch hu4 (hnb hc)
      · have : cap = 0 := by omega
        subst this; exact ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
          fun _ h => absurd h (by omega)⟩
    have hD4 : Alloc.DynAt m4 Block.vmark2 Block.vmark2Sz 2 cap b :=
      { hD with
        capLd := by rw [hu.load _ _ _ (hnS _ (.inr rfl))]; exact hD.capLd
        bsW := hu.access _ _ _ _ (hnS _ (.inr rfl)) hD.bsW
        bpW := hu.access _ _ _ _ (hnS _ (.inl rfl)) hD.bpW
        ptr := fun hc => by rw [hu.load _ _ _ (hnS _ (.inl rfl))]; exact hD.ptr hc
        mal := fun hc => ((hD1.mal hc).keep hkp3).keep (Alloc.Keep.unch hu4 (hnb hc))
        null := fun hc => by rw [hu.load _ _ _ (hnS _ (.inl rfl))]; exact hD.null hc }
    refine hQ le3 m4 1 (fun _ => 0) ⟨hD4, hval4, Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _ hW3,
      by decide, by decide, harr4, fun _ _ => ⟨Int.le_refl _, by decide⟩, hM.bval⟩
      (fun _ _ => by decide) hu (fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hst4 _ (hg3 _ (hg1 _ h)))
      (fun x hx hx' => by rw [ho3 x hx', temps_gso _ _ hx', hle1 x hx])

/-- `MarksAt` survives a change confined to the marks array, which keeps
the array's block. -/
theorem MarksAt.update {m m' : mem} {cap : Nat} {b : block} {st : Nat} {marks marks' : Nat → Int}
    (h : MarksAt m cap b st marks) (hc : 0 < cap) (hu : Unch m m' (· = b)) (hk : Alloc.Keep m m' b)
    (harr : ArrayAt m' .Mint16signed b 0 (markVals marks') cap)
    (hb : ∀ i < cap, 0 ≤ marks' i ∧ marks' i ≤ st) : MarksAt m' cap b st marks' where
  dyn := h.dyn.keep hu (fun e => (h.dyn.bne hc).2 e.symm) (fun e => (h.dyn.bne hc).1 e.symm)
    (fun _ => hk)
  valLd := by rw [hu.load _ _ _ (fun e => h.bval hc e.symm)]; exact h.valLd
  valW := hu.access _ _ _ _ (fun e => h.bval hc e.symm) h.valW
  val1 := h.val1
  val32 := h.val32
  arr := harr
  bounds := hb
  bval := h.bval

/-- `MarksAt` survives a change outside the marks globals and array. -/
theorem MarksAt.unch {m m' : mem} {cap : Nat} {b : block} {st : Nat} {marks : Nat → Int}
    {S : block → Prop} (h : MarksAt m cap b st marks) (hu : Unch m m' S)
    (h1 : ¬ S Block.vmark2) (h2 : ¬ S Block.vmark2Sz) (h3 : ¬ S Block.vmark2Val)
    (h4 : 0 < cap → ¬ S b) : MarksAt m' cap b st marks where
  dyn := h.dyn.keep hu h1 h2 (fun hc => Alloc.Keep.unch hu (h4 hc))
  valLd := by rw [hu.load _ _ _ h3]; exact h.valLd
  valW := hu.access _ _ _ _ h3 h.valW
  val1 := h.val1
  val32 := h.val32
  arr := by
    by_cases hc : 0 < cap
    · exact h.arr.unch hu (h4 hc)
    · have : cap = 0 := by omega
      subst this; exact ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
        fun _ h => absurd h (by omega)⟩
  bounds := h.bounds
  bval := h.bval

/-- The blocks the marks may occupy after `preparemarks2`: the three globals,
the old array (if any) and a new one. -/
def MarksS (m : mem) (cap : Nat) (b b' : block) (z : block) : Prop :=
  z = Block.vmark2 ∨ z = Block.vmark2Sz ∨ z = Block.vmark2Val ∨ (0 < cap ∧ z = b) ∨
    (¬ Mem.valid_block m b' ∧ z = b')

/-- `preparemarks2(nn)`: afterwards the marks hold at least `nn` entries; a
reallocated array is a block new to `m`. -/
def prepSpec (nn cap : Nat) (b : block) (st : Nat) (marks : Nat → Int) : FunSpec where
  pre args m := args = [.Vlong (lr nn)] ∧ MarksAt m cap b st marks ∧ nn < 2147483648
  post _ m t _ m' := t = E0 ∧ ∃ cap' b' st' marks', MarksAt m' cap' b' st' marks' ∧ nn ≤ cap' ∧
    ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') ∧ Unch m m' (MarksS m cap b b') ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z)

namespace Prep2

abbrev nn : ident := sparse.id.nn
abbrev oldsize : ident := sparse.id.oldsize
abbrev oldpos : ident := sparse.id.oldpos
abbrev t : ident := idOf 705

/-- The body of `preparemarks2`, factored. -/
abbrev body : statement :=
  .Ssequence (Alloc.sk (.Sset oldsize (.Evar id.vmark2Sz tulong)))
   (.Ssequence (Alloc.sk (.Sset oldpos (.Evar id.vmark2 (tptr tshort))))
    (.Ssequence (Alloc.dynalloc1 id.vmark2Sz id.vmark2 tshort (.Etempvar nn tulong) (idOf 703) (idOf 704)
        sparse.id.«nausparse:__stringlit_1» 13)
      (.Ssequence
        (Alloc.sk (.Sifthenelse
          (.Ebinop .One (.Evar id.vmark2Sz tulong) (.Etempvar oldsize tulong) tint)
          (.Sset t (ci 1 tint))
          (Alloc.sk (.Sset t (.Ecast (.Ebinop .One (.Evar id.vmark2 (tptr tshort))
            (.Etempvar oldpos (tptr tshort)) tint) tbool)))))
        (.Sifthenelse (.Etempvar t tint)
          (Alloc.sk (.Sassign (.Evar id.vmark2Val tshort) (ci 32000 tint))) .Sskip))))

kernel_rfl body_eq : sparse.body.«nausparse:preparemarks2» = body

def entryTemps (nv : Nat) : temp_env :=
  PTree.set nn (.Vlong (lr nv)) (create_undef_temps sparse.fn.«nausparse:preparemarks2».fn_temps)

theorem eval_ptr {le : temp_env} {m : mem} {v : val}
    (h : Mem.load .Mint64 m Block.vmark2 (zOfInt 0) = some v) :
    Exec.evalExpr sge empty_env le m (.Evar id.vmark2 (tptr tshort)) = some v := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.vmark2 (empty_env : env) = none from rfl,
    find_vmark2, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq]
  exact h

end Prep2

open Prep2 in
theorem prep_satisfies (nv cap : Nat) (b : block) (st : Nat) (marks : Nat → Int) :
    Satisfies xi sge (.Internal sparse.fn.«nausparse:preparemarks2») (prepSpec nv cap b st marks) := by
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
    rw [sparse.fn.«nausparse:preparemarks2».fn_body_eq, body_eq]
    have hD := hM.dyn
    have hcap := hD.capLt
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_sz hD.capLd]
    let pv : val := if 0 < cap then .Vptr b Ptrofs.zero else Vnullptr
    have hpv : Mem.load .Mint64 m Block.vmark2 (zOfInt 0) = some pv := by
      by_cases h0 : 0 < cap
      · simp only [pv, h0, ite_true]; exact hD.ptr h0
      · simp only [pv, h0, ite_false]; exact hD.null (by omega)
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_ptr hpv]
    wp_step
    refine Alloc.wp_dynalloc1L (E := NautyEnv.sparse) find_vmark2Sz find_vmark2 rfl hD
      (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]) hn31 (show 2 * nv < 2 ^ 62 by omega) ?_
    intro le1 m1 cap1 b1 hD1 hnc hu1 hor hg1 ho1
    have hD1' : Alloc.DynAt m1 Block.vmark2 Block.vmark2Sz 2 cap1 b1 := hD1
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
    simp only [typeof, cop, Prep.eq_lr (a := cap1) (b := cap) (by omega) (by omega)]
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
      have hcv : Exec.evalExpr sge empty_env le1 m1 (.Ecast (.Ebinop .One (.Evar id.vmark2 (tptr tshort))
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
      exact ⟨m1, Prep.free_empty _, rfl, cap1, b1, st, marks, hM, hnc, .inl ⟨rfl, rfl⟩, Unch.refl _ _,
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
      have hvV : Mem.valid_block m Block.vmark2Val := Alloc.valid_of_access hM.valW
      have hVS : ¬ (Block.vmark2Val = Block.vmark2Sz ∨ Block.vmark2Val = Block.vmark2 ∨
          0 < cap ∧ Block.vmark2Val = b ∨ ¬Mem.valid_block m b1 ∧ Block.vmark2Val = b1) := by
        rintro (h | h | ⟨h0, h⟩ | ⟨h0, h⟩)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact hM.bval h0 h.symm
        · exact h0 (h ▸ hvV)
      have hW := hu1.access _ _ _ _ hVS hM.valW
      refine wp_storeVal (x := 32000) (rhs := ci 32000 tint) (by decide) rfl rfl hW ?_
      intro m2 hst2
      have hu2 : Unch m1 m2 (· = Block.vmark2Val) := Unch.store hst2 rfl
      have hb1V : b1 ≠ Block.vmark2Val := fun h => hnew (h ▸ hvV)
      have hc1 : 0 < cap1 := by omega
      have hmal := hD1'.mal hc1
      have hD2 : Alloc.DynAt m2 Block.vmark2 Block.vmark2Sz 2 cap1 b1 :=
        hD1'.keep hu2 (by decide) (by decide) (fun _ => Alloc.Keep.unch hu2 hb1V)
      have harr : ArrayAt m2 .Mint16signed b1 0 (markVals fun _ => 0) cap1 :=
        (hz'.unch hu2 hb1V).array (fun o h1 h2 => Mem.perm_store_1 _ _ _ _ _ _ hst2 _ _ _ _
          (hmal.perm o (by omega) h2)) hD1'.small .Mint16signed 2 rfl rfl _ rfl cap1 (Nat.le_refl _)
      refine ⟨m2, Prep.free_empty _, rfl, cap1, b1, 32000, fun _ => 0, ⟨hD2, ?_,
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

end NautyVerified.Proofs.Sparse.Marks2

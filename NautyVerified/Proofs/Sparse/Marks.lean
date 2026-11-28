import NautyVerified.Proofs.Sparse.Graph
import NautyVerified.Proofs.Search.Ops
import NautyVerified.Proofs.Sparse.Cop

/-!
# nausparse.c's marks

`vmark1` is a `DYNALLSTAT(short, vmark1, vmark1_sz)` array with the stamp
`static short vmark1_val = 32000`; `MARK1(i)` stores the stamp at `i`,
`UNMARK1(i)` stores 0, and `i` is marked when its entry equals the stamp.
`MarksAt m cap b st marks`: capacity `cap`, array block `b`, stamp `st`,
entries `marks`, with the invariant `0 ≤ marks i ≤ st ≤ 32000` and
`1 ≤ st`. `RESETMARKS1` (`wp_resetmarks1`) re-establishes it with every
entry below the new stamp: either the stamp grows by one, or (when it had
reached 32000) the array is zeroed and the stamp set to 1.
-/

namespace NautyVerified.Proofs.Sparse

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source

variable {xi : ExternalCalls}

namespace id
abbrev vmark1 : ident := sparse.id.«nausparse:vmark1»
abbrev vmark1Sz : ident := sparse.id.«nausparse:vmark1_sz»
abbrev vmark1Val : ident := sparse.id.«nausparse:vmark1_val»
end id

/-- The values of a `short` array holding `marks`. -/
def markVals (marks : Nat → Int) (i : Nat) : val := .Vint (ir (marks i))

/-- The marks invariant (see the module docstring). -/
structure MarksAt (m : mem) (cap : Nat) (b : block) (st : Nat) (marks : Nat → Int) : Prop where
  dyn : Alloc.DynAt m Block.vmark1 Block.vmark1Sz 2 cap b
  valLd : Mem.load .Mint16signed m Block.vmark1Val (zOfInt 0) = some (.Vint (ir st))
  valW : Mem.valid_access m .Mint16signed Block.vmark1Val (zOfInt 0) .Writable
  val1 : 1 ≤ st
  val32 : st ≤ 32000
  arr : ArrayAt m .Mint16signed b 0 (markVals marks) cap
  bounds : ∀ i < cap, 0 ≤ marks i ∧ marks i ≤ st
  bval : 0 < cap → b ≠ Block.vmark1Val

/-- `RESETMARKS1`, with temporaries `t` (the old stamp) and `ij` (the index). -/
abbrev resetmarks1 (t ij : ident) : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence .Sskip (.Sset t (.Evar id.vmark1Val tshort)))
      (.Sassign (.Evar id.vmark1Val tshort) (.Ebinop .Oadd (.Etempvar t tshort) (ci 1 tint) tint)))
    (.Sifthenelse (.Ebinop .Oge (.Etempvar t tshort) (ci 32000 tint) tint)
      (.Ssequence
        (.Ssequence
          (.Ssequence .Sskip (.Sset ij (.Ecast (ci 0 tint) tulong)))
          (.Sloop
            (.Ssequence
              (.Ssequence .Sskip
                (.Sifthenelse (.Ebinop .Olt (.Etempvar ij tulong) (.Evar id.vmark1Sz tulong) tint)
                  .Sskip .Sbreak))
              (.Ssequence .Sskip
                (.Sassign (.Ederef (.Ebinop .Oadd (.Evar id.vmark1 (tptr tshort))
                  (.Etempvar ij tulong) (tptr tshort)) tshort) (ci 0 tint))))
            (.Ssequence .Sskip (.Sset ij (.Ebinop .Oadd (.Etempvar ij tulong) (ci 1 tint) tulong)))))
        (.Ssequence .Sskip (.Sassign (.Evar id.vmark1Val tshort) (ci 1 tint))))
      .Sskip)

theorem eval_val {le : temp_env} {m : mem} {st : Nat}
    (h : Mem.load .Mint16signed m Block.vmark1Val (zOfInt 0) = some (.Vint (ir st))) :
    Exec.evalExpr sge empty_env le m (.Evar id.vmark1Val tshort) = some (.Vint (ir st)) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.vmark1Val (empty_env : env) = none from rfl,
    find_vmark1Val, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv]
  exact h

/-- Storing a `short` stamp `x`. -/
theorem wp_storeVal {f : function} {Q : Post} {le : temp_env} {m : mem} {rhs : expr} {x : Nat}
    (hx : x < 32768) (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hW : Mem.valid_access m .Mint16signed Block.vmark1Val (zOfInt 0) .Writable)
    (hQ : ∀ m', Mem.store .Mint16signed m Block.vmark1Val (zOfInt 0) (.Vint (ir x)) = some m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (.Evar id.vmark1Val tshort) rhs) Q empty_env le m := by
  have hse := Search.sign_ext16_ir (a := (x : Int)) (by omega) (by omega)
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ (.Vint (ir x)) hW
  apply wp_assign_eval
  simp only [hrhs, Exec.evalLvalue, Exec.lvalOfVar,
    show PTree.get id.vmark1Val (empty_env : env) = none from rfl, find_vmark1Val, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [hse, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hst]
  exact hQ m' hst

/-- The zeroing loop of `RESETMARKS1`. -/
abbrev zeroLoop (ij : ident) : statement :=
  .Sloop
    (.Ssequence
      (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar ij tulong) (.Evar id.vmark1Sz tulong) tint)
          .Sskip .Sbreak))
      (.Ssequence .Sskip
        (.Sassign (.Ederef (.Ebinop .Oadd (.Evar id.vmark1 (tptr tshort))
          (.Etempvar ij tulong) (tptr tshort)) tshort) (ci 0 tint))))
    (.Ssequence .Sskip (.Sset ij (.Ebinop .Oadd (.Etempvar ij tulong) (ci 1 tint) tulong)))

theorem eval_sz {le : temp_env} {m : mem} {cap : Nat}
    (h : Mem.load .Mint64 m Block.vmark1Sz (zOfInt 0) = some (.Vlong (lr cap))) :
    Exec.evalExpr sge empty_env le m (.Evar id.vmark1Sz tulong) = some (.Vlong (lr cap)) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.vmark1Sz (empty_env : env) = none from rfl,
    find_vmark1Sz, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv]
  exact h

theorem eval_vmark1 {le : temp_env} {m : mem} {b : block}
    (h : Mem.load .Mint64 m Block.vmark1 (zOfInt 0) = some (.Vptr b Ptrofs.zero)) :
    Exec.evalExpr sge empty_env le m (.Evar id.vmark1 (tptr tshort)) = some (.Vptr b Ptrofs.zero) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.vmark1 (empty_env : env) = none from rfl,
    find_vmark1, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq]
  exact h

theorem cast_zero_short (m : mem) :
    Cfrontend.Cop.sem_cast (.Vint (ir 0)) tint tshort m = some (.Vint (ir 0)) := rfl

theorem wp_zeroLoop {f : function} {Q : Post} {le : temp_env} {m : mem} {cap : Nat} {b : block}
    {marks : Nat → Int} {ij : ident}
    (hcap : Mem.load .Mint64 m Block.vmark1Sz (zOfInt 0) = some (.Vlong (lr cap)))
    (hcapLt : cap < 2147483648)
    (hp : 0 < cap → Mem.load .Mint64 m Block.vmark1 (zOfInt 0) = some (.Vptr b Ptrofs.zero))
    (harr : ArrayAt m .Mint16signed b 0 (markVals marks) cap)
    (hb : 0 < cap → b ≠ Block.vmark1Sz ∧ b ≠ Block.vmark1)
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
    have hcap' : Mem.load .Mint64 m' Block.vmark1Sz (zOfInt 0) = some (.Vlong (lr cap)) := by
      rw [hu.load _ _ _ (fun ⟨hc, h⟩ => (hb hc).1 h.symm)]; exact hcap
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (.Etempvar ij tulong) = _ from hk',
      eval_sz hcap']
    simp only [typeof, cop, Alloc.ltu_lr (a := k) (b := cap) (by omega) (by omega)]
    by_cases hkc : k < cap
    · rw [ite_eq_left (by simpa using hkc)]
      apply wp_skip
      have hp' : Mem.load .Mint64 m' Block.vmark1 (zOfInt 0) = some (.Vptr b Ptrofs.zero) := by
        rw [hu.load _ _ _ (fun ⟨hc, h⟩ => (hb hc).2 h.symm)]; exact hp (by omega)
      wp_step; wp_step
      refine wp_idx_store_l (chunk := .Mint16signed) (bo := b) (ofs := Ptrofs.zero) harr' (by omega)
        (eval_vmark1 hp') rfl rfl rfl (.Etempvar ij tulong) k hkc hk' rfl _ tint rfl _ (.Vint (ir 0)) rfl
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

/-- `RESETMARKS1`: afterwards every entry is below the stamp. -/
theorem wp_resetmarks1 {f : function} {Q : Post} {le : temp_env} {m : mem} {cap : Nat} {b : block}
    {st : Nat} {marks : Nat → Int} {t ij : ident}
    (hM : MarksAt m cap b st marks)
    (hQ : ∀ le' m' val' marks', MarksAt m' cap b val' marks' → (∀ i < cap, marks' i < val') →
      Unch m m' (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b)) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ t → x ≠ ij → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge f (resetmarks1 t ij) Q empty_env le m := by
  have hV1 := hM.val1
  have hV2 := hM.val32
  have hD := hM.dyn
  have hne1 : Block.vmark1Val ≠ Block.vmark1 := by decide
  have hne2 : Block.vmark1Val ≠ Block.vmark1Sz := by decide
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_val hM.valLd]
  let le1 := PTree.set t (.Vint (ir st)) le
  have ht1 : PTree.get t le1 = some (.Vint (ir st)) := temps_gss _ _ _
  refine wp_storeVal (x := st + 1) (by omega) ?_ rfl hM.valW ?_
  · simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]; push_cast; rfl
  intro m1 hst1
  have hu1 : Unch m m1 (· = Block.vmark1Val) := Unch.store hst1 rfl
  have hval1 : Mem.load .Mint16signed m1 Block.vmark1Val (zOfInt 0) = some (.Vint (ir (st + 1))) := by
    have := Mem.load_store_same _ _ _ _ _ _ hst1
    rw [this]
    exact congrArg (fun x => some (val.Vint x)) (Search.sign_ext16_ir (a := ((st + 1 : Nat) : Int))
      (by omega) (by omega))
  have hW1 : Mem.valid_access m1 .Mint16signed Block.vmark1Val (zOfInt 0) .Writable :=
    Mem.store_valid_access_1 _ _ _ _ _ _ hst1 _ _ _ _ hM.valW
  have hg1 : ∀ z, Mem.valid_block m z → Mem.valid_block m1 z :=
    fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hst1 _ h
  have hnb : 0 < cap → ¬ b = Block.vmark1Val := fun hc h => hM.bval hc h
  have hD1 : Alloc.DynAt m1 Block.vmark1 Block.vmark1Sz 2 cap b :=
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
    have hW3 : Mem.valid_access m3 .Mint16signed Block.vmark1Val (zOfInt 0) .Writable :=
      hu3.access _ _ _ _ (fun ⟨hc, h⟩ => hnb hc h.symm) hW1
    refine wp_storeVal (x := 1) (by decide) (by simp only [Exec.evalExpr]; rfl) rfl hW3 ?_
    intro m4 hst4
    have hu4 : Unch m3 m4 (· = Block.vmark1Val) := Unch.store hst4 rfl
    have hnS : ∀ z, (z = Block.vmark1 ∨ z = Block.vmark1Sz) →
        ¬ ((z = Block.vmark1Val) ∨ (0 < cap ∧ z = b)) := by
      rintro z (rfl | rfl) (h | ⟨hc, h⟩)
      · exact hne1 h.symm
      · exact (hD.bne hc).2 h.symm
      · exact hne2 h.symm
      · exact (hD.bne hc).1 h.symm
    have hu : Unch m m4 (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b)) :=
      ((hu1.mono fun z hz => .inl hz).trans (hu3.mono fun z hz => .inr hz)).trans
        (hu4.mono fun z hz => .inl hz)
    have hval4 : Mem.load .Mint16signed m4 Block.vmark1Val (zOfInt 0) = some (.Vint (ir 1)) := by
      rw [Mem.load_store_same _ _ _ _ _ _ hst4]; rfl
    have harr4 : ArrayAt m4 .Mint16signed b 0 (markVals fun _ => 0) cap := by
      by_cases hc : 0 < cap
      · exact harr3.unch hu4 (hnb hc)
      · have : cap = 0 := by omega
        subst this; exact ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
          fun _ h => absurd h (by omega)⟩
    have hD4 : Alloc.DynAt m4 Block.vmark1 Block.vmark1Sz 2 cap b :=
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

theorem lr_add (a b : Nat) : Lib.Integers.Int64.add (lr a) (lr b) = lr ((a + b : Nat) : Int) := by
  apply bv64_inj.1
  simp only [bv64_add, bv64_repr, intOfZ_zOfInt, ← BitVec.ofInt_add]
  push_cast; rfl

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
    (h1 : ¬ S Block.vmark1) (h2 : ¬ S Block.vmark1Sz) (h3 : ¬ S Block.vmark1Val)
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

end NautyVerified.Proofs.Sparse

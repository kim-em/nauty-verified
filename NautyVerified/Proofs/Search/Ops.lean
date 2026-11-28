import NautyVerified.Program.Env
import NautyVerified.Proofs.Search.Frame
import NautyVerified.Logic.ForC
import NautyVerified.Proofs.Alloc.Global

/-!
# Reading and writing nauty.c's globals

`wp_gint`: `g = rhs` for a static `int`. `eval_gint`: reading it.
`statsF fld ty`: `stats->fld`; the `fld_*` lemmas pin `statsblk`'s layout, and
`wp_statsStore` writes a member.
-/

namespace NautyVerified.Proofs.Search

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

theorem wp_gint {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {g : ident}
    {b : block} (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some b)
    (hw : Mem.valid_access m .Mint32 b (zOfInt 0) .Writable) {rhs : expr} {x : Int}
    (hr : Exec.evalExpr ge e le m rhs = some (.Vint (ir x))) (hrt : typeof rhs = tint)
    (hQ : ∀ m', IntAt m' b x → Unch m m' (· = b) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar g tint) rhs) Q e le m := by
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ (.Vint (ir x)) hw
  apply wp_assign_eval
  simp only [hr, hrt]
  simp only [Exec.evalLvalue, Exec.lvalOfVar, hge, hg, typeof, cop, Exec.assignLoc,
    Cfrontend.Ctypes.access_mode, Mem.storev, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
    hst]
  exact hQ m' ⟨by rw [Mem.load_store_same _ _ _ _ _ _ hst]; rfl,
    Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hw⟩ (Unch.store hst rfl)
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

theorem eval_gint {e : env} {le : temp_env} {m : mem} {g : ident} {b : block} {x : Int}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some b)
    (h : IntAt m b x) : Exec.evalExpr ge e le m (.Evar g tint) = some (.Vint (ir x)) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg, Exec.derefLoc, Cfrontend.Ctypes.access_mode,
    Mem.loadv, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  exact h.load

/-- `g[a] = rhs` for an `int *` global, with validity preserved. -/
theorem wp_gstoreV {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {g : Common.AST.ident} {bg b : block} {vals : Nat → val} {n : Nat}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr b Ptrofs.zero))
    (harr : ArrayAt m .Mint32 b 0 vals n) (hn : n < 2147483648)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (x : Int) (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 b 0 (upd vals c (.Vint (ir x))) n → Unch m m' (· = b) →
      Alloc.Keep m m' b → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (Alloc.gat g a) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hge, hg, ha, hty, hrhs, hrty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp, Exec.assignLoc, Mem.storev]
  show match Mem.store .Mint32 m b (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [Alloc.addr_int c (by omega), hst]
  exact hQ m' harr' (Unch.store hst rfl) (Alloc.Keep.store hst (by
    simp only [elemOfs, intOfZ_zOfInt, show csize .Mint32 = 4 from rfl]; omega))
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

/-- `p[a] = rhs` for an `int *` temporary, with validity preserved. -/
theorem wp_storeV {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bo : block}
    {ofs : ptrofs} {o : Array Nat} {n : Nat}
    (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n)
    (hn : n < 2147483648) (p : Common.AST.ident) (hp : PTree.get p le = some (.Vptr bo ofs))
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (x : Int) (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (upd (ints o) c (.Vint (ir x))) n →
      Unch m m' (· = bo) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar p (tptr tint)) a (tptr tint)) tint) rhs)
      Q e le m := by
  have haddr : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tint)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint32 (intOfZ (Ptrofs.unsigned ofs)) c := by
    apply addr_elem ofs _ .Mint32 rfl rfl (by omega)
    have hf := harr.fits
    have h4 : csize .Mint32 = 4 := rfl
    rw [h4] at hf ⊢
    omega
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hrhs, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint32 m bo (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [haddr, hst]
  exact hQ m' harr' (Unch.store hst rfl) (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

/-- `if (c) g = rhs;` for a static `int` `g` holding `v`: afterwards it holds
`if c then x else v`. -/
theorem wp_clamp {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {g : ident}
    {b : block} {v : Int} (hge : PTree.get g e = none)
    (hg : Genv.find_symbol ge.genv_genv g = some b) (hI : IntAt m b v) {cond rhs : expr}
    {c : Bool} (hc : Exec.evalExpr ge e le m cond = some (Val.of_bool c)) (hct : typeof cond = tint)
    {x : Int} (hr : Exec.evalExpr ge e le m rhs = some (.Vint (ir x))) (hrt : typeof rhs = tint)
    (hQ : ∀ m', IntAt m' b (if c then x else v) → Unch m m' (· = b) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Ssequence .Sskip (.Sifthenelse cond (.Ssequence .Sskip (.Sassign (.Evar g tint) rhs))
      .Sskip)) Q e le m := by
  wp_step; wp_step
  apply wp_if_eval
  rw [hc, hct]
  simp only [cop]
  cases c
  · simp only [Bool.false_eq_true, ite_false]
    exact wp_skip (hQ m (by simpa using hI) (Unch.refl _ _) fun _ h => h)
  · simp only [ite_true]
    wp_step; wp_step
    exact wp_gint hge hg hI.writable hr hrt fun m' hI' hu hv => hQ m' (by simpa using hI') hu hv

theorem IntAt.ite_nat {m : mem} {b : block} {p : Prop} [Decidable p] {x y : Nat}
    (h : IntAt m b (if decide p = true then (x : Int) else (y : Int))) :
    IntAt m b ((if p then x else y : Nat) : Int) := by
  by_cases hp : p
  · simp only [hp, decide_true, ite_true] at h ⊢; exact h
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false] at h ⊢; exact h

/-! ## `short` values -/

theorem ir_shl16 {a : _root_.Int} (h0 : 0 ≤ a) (ha : a < 32768) :
    Lib.Integers.Int.shl (ir a) (ir 16) = ir (a * 65536) := by
  apply bv32_inj.1
  rw [bv32_shl, toNat_ir (by omega) (by omega), bv32_ir, bv32_ir]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofInt, Nat.shiftLeft_eq,
    show Int.toNat 16 = 16 from rfl, Nat.reducePow]
  omega

/-- A nonnegative `short` value is unchanged by sign extension. -/
theorem sign_ext16_ir {a : _root_.Int} (h0 : 0 ≤ a) (ha : a < 32768) :
    Lib.Integers.Int.sign_ext (zOfInt 16) (ir a) = ir a := by
  have h := CompCert4Lean.Lib.Integers.Int.sign_ext_shr_shl_proof (zOfInt 16) (ir a)
    ⟨show (0 : _root_.Int) < intOfZ (zOfInt 16) by decide,
     show intOfZ (zOfInt 16) ≤ 32 by decide⟩
  simp only at h
  rw [h]
  change Lib.Integers.Int.shr (Lib.Integers.Int.shl (ir a) (ir 16)) (ir 16) = ir a
  rw [ir_shl16 h0 ha]
  have := ir_shr (a := a * 65536) 16 ⟨by omega, by omega⟩ (by decide)
  exact this.trans (by congr 1; omega)

section Cop
variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
variable (m : mem) (a b : attr) (x : Lib.Integers.int)

@[simp, cop] theorem cast_is : Cfrontend.Cop.sem_cast (.Vint x) (Tint .I32 .Signed a)
    (Tint .I16 .Signed b) m = some (.Vint (Lib.Integers.Int.sign_ext (zOfInt 16) x)) := rfl
@[simp, cop] theorem cast_ss : Cfrontend.Cop.sem_cast (.Vint x) (Tint .I16 .Signed a)
    (Tint .I16 .Signed b) m = some (.Vint (Lib.Integers.Int.sign_ext (zOfInt 16) x)) := rfl
end Cop

/-- `g[a]` for a `short *` global `g`. -/
abbrev gats (g : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar g (tptr tshort)) a (tptr tshort)) tshort

theorem addr_short (c : Nat) (hc : c < 2147483648) :
    Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tshort)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint16signed 0 c := by
  apply addr_elem Ptrofs.zero _ .Mint16signed rfl (base := 0) rfl (by omega)
  have h2 : csize .Mint16signed = 2 := rfl
  rw [h2]; omega

theorem eval_gats {e : env} {le : temp_env} {m : mem} {g : Common.AST.ident} {bg b : block}
    {vals : Nat → val} {n : Nat} (hge : PTree.get g e = none)
    (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr b Ptrofs.zero))
    (harr : ArrayAt m .Mint16signed b 0 vals n) (hn : n < 2147483648)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m (gats g a) = some (vals c) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg, ha, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [addr_short c (by omega)]
  exact harr.load c hc

theorem wp_gstoreS {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {g : Common.AST.ident} {bg b : block} {vals : Nat → val} {n : Nat}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr b Ptrofs.zero))
    (harr : ArrayAt m .Mint16signed b 0 vals n) (hn : n < 2147483648)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (x : Nat) (hx : x < 32768)
    (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint ∨ typeof rhs = tshort)
    (hQ : ∀ m', ArrayAt m' .Mint16signed b 0 (upd vals c (.Vint (ir x))) n → Unch m m' (· = b) →
      Alloc.Keep m m' b → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (gats g a) rhs) Q e le m := by
  have hse := sign_ext16_ir (a := (x : Int)) (by omega) (by omega)
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc (.Vint (ir x))
    (by show Val.load_result _ _ = _; exact congrArg val.Vint hse)
  apply wp_assign_eval
  simp only [hrhs]
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hge, hg, ha, hty]
  rcases hrty with hrty | hrty <;> rw [hrty] <;>
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp, Exec.assignLoc, Mem.storev, hse] <;>
  show match Mem.store .Mint16signed m b (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False <;>
  rw [addr_short c (by omega), hst] <;>
  exact hQ m' harr' (Unch.store hst rfl) (Alloc.Keep.store hst (by
    simp only [elemOfs, intOfZ_zOfInt, show csize .Mint16signed = 2 from rfl]; omega))
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

theorem shorts_set {o : Array Nat} {j : Nat} (hj : j < o.size) (v : Nat) :
    shorts (o.set! j v) = upd (shorts o) j (.Vint (ir (v : Int))) := by
  funext i
  simp only [shorts, upd]
  by_cases h : i = j
  · subst h; rw [ite_eq_left rfl, Array.getElem!_set!_self _ _ _ hj]
  · rw [ite_eq_right h, Array.getElem!_set!_ne _ _ _ _ (Ne.symm h)]

theorem intsZ_set {o : Array Int} {j : Nat} (hj : j < o.size) (v : Int) :
    intsZ (o.set! j v) = upd (intsZ o) j (.Vint (ir v)) := by
  funext i
  simp only [intsZ, upd]
  by_cases h : i = j
  · subst h; rw [ite_eq_left rfl, Array.getElem!_set!_self _ _ _ hj]
  · rw [ite_eq_right h, Array.getElem!_set!_ne _ _ _ _ (Ne.symm h)]

/-! ## Stores and `FieldAt` -/

/-- After storing `w` at a field, it holds `load_result w`. -/
theorem FieldAt.store_same {m m' : mem} {chunk : memory_chunk} {b : block} {off : Int} {w : val}
    (hst : Mem.store chunk m b (zOfInt off) w = some m')
    (hw : Mem.valid_access m chunk b (zOfInt off) .Writable) :
    FieldAt m' chunk b off (Val.load_result chunk w) :=
  ⟨Mem.load_store_same _ _ _ _ _ _ hst, Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hw⟩

/-- A store into the same block at a disjoint byte range leaves a field. -/
theorem FieldAt.store_other {m m' : mem} {chunk c' : memory_chunk} {b : block} {off off' : Int}
    {v w : val} (h : FieldAt m chunk b off v) (hst : Mem.store c' m b (zOfInt off') w = some m')
    (hd : off + csize chunk ≤ off' ∨ off' + csize c' ≤ off) : FieldAt m' chunk b off v := by
  refine ⟨?_, Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ h.writable⟩
  rw [Mem.load_store_other _ _ _ _ _ _ hst _ _ _ (.inr (by
    rcases hd with hd | hd
    · left; change intOfZ _ ≤ intOfZ _; simp only [intOfZ_add, intOfZ_zOfInt]
      exact hd
    · right; change intOfZ _ ≤ intOfZ _; simp only [intOfZ_add, intOfZ_zOfInt]
      exact hd))]
  exact h.load

/-- `StatsFix` survives a store to a `statsblk` member at offsets 12 to 20 or
from 24 on. -/
theorem StatsFix.store {m m' : mem} {S : SLoc} (h : StatsFix m S) {c : memory_chunk} {off : Int}
    {w : val} (hst : Mem.store c m S.bst (zOfInt off) w = some m')
    (hd : S.sb + 24 ≤ off ∨ (S.sb + 12 ≤ off ∧ off + csize c ≤ S.sb + 20)) : StatsFix m' S := by
  have c4 : csize .Mint32 = 4 := rfl
  have c8 : csize .Mfloat64 = 8 := rfl
  refine ⟨fun o ho => Mem.perm_store_1 _ _ _ _ _ _ hst _ _ _ _ (h.perm o ho),
    h.errstatus.store_other hst (by omega), ?_, ?_⟩
  · obtain ⟨x, hx⟩ := h.grpsize1; exact ⟨x, hx.store_other hst (by omega)⟩
  · obtain ⟨i, hi⟩ := h.grpsize2; exact ⟨i, hi.store_other hst (by omega)⟩

/-! ## `statsblk` members -/

/-- `stats->fld`. -/
abbrev statsF (fld : ident) (ty : Cfrontend.Ctypes.type) : expr :=
  .Efield (.Ederef (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
    (Tstruct dense.id.«_1024» noattr)) fld ty

theorem fld_numorbits : ∀ (l : block) (o : Lib.Integers.ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.numorbits (.Vptr l o) =
    some (l, Ptrofs.add o (Ptrofs.repr (zOfInt 12)), .Full) :=
  E.field_statsNumorbits
theorem fld_numgenerators : ∀ (l : block) (o : Lib.Integers.ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.numgenerators (.Vptr l o) =
    some (l, Ptrofs.add o (Ptrofs.repr (zOfInt 16)), .Full) :=
  E.field_statsNumgenerators
theorem fld_numnodes : ∀ (l : block) (o : Lib.Integers.ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.numnodes (.Vptr l o) =
    some (l, Ptrofs.add o (Ptrofs.repr (zOfInt 24)), .Full) :=
  E.field_statsNumnodes
theorem fld_numbadleaves : ∀ (l : block) (o : Lib.Integers.ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.numbadleaves (.Vptr l o) =
    some (l, Ptrofs.add o (Ptrofs.repr (zOfInt 32)), .Full) :=
  E.field_statsNumbadleaves
theorem fld_maxlevel : ∀ (l : block) (o : Lib.Integers.ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.maxlevel (.Vptr l o) =
    some (l, Ptrofs.add o (Ptrofs.repr (zOfInt 40)), .Full) :=
  E.field_statsMaxlevel
theorem fld_tctotal : ∀ (l : block) (o : Lib.Integers.ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.tctotal (.Vptr l o) =
    some (l, Ptrofs.add o (Ptrofs.repr (zOfInt 48)), .Full) :=
  E.field_statsTctotal
theorem fld_canupdates : ∀ (l : block) (o : Lib.Integers.ptrofs),
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.canupdates (.Vptr l o) =
    some (l, Ptrofs.add o (Ptrofs.repr (zOfInt 56)), .Full) :=
  E.field_statsCanupdates

theorem unsigned_add_off (o : Lib.Integers.ptrofs) {off : Int} (h0 : 0 ≤ off)
    (h1 : intOfZ (Ptrofs.unsigned o) + off < 2 ^ 64) :
    Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (zOfInt off))) =
      zOfInt (intOfZ (Ptrofs.unsigned o) + off) := by
  have hu := intOfZ_Ptrofs_unsigned o
  have hb : (bvp o).toNat < 2 ^ 64 := (bvp o).isLt
  rw [← zOfInt_intOfZ (Ptrofs.unsigned _)]
  congr 1
  rw [intOfZ_Ptrofs_unsigned, bvp_add, bvp_repr, intOfZ_zOfInt, BitVec.toNat_add,
    BitVec.toNat_ofInt, hu]
  have : (((2 ^ 64 : Nat) : Int)) = 2 ^ 64 := by norm_cast
  rw [this]
  have h2 : off % 2 ^ 64 = off := Int.emod_eq_of_lt h0 (by omega)
  rw [h2]
  rw [hu] at h1
  omega

/-- Reading `stats->fld` at byte `off`. -/
theorem eval_statsF {e : env} {le : temp_env} {m : mem} {S : SLoc} {fld : ident}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {off : Int} {v : val}
    (hge : PTree.get dense.id.«nauty:stats» e = none)
    (hfld : ∀ l o, Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) fld (.Vptr l o) =
      some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (hacc : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hp : PtrAt m E.stats (.Vptr S.bst S.sofs)) (h0 : 0 ≤ off) (h1 : S.sb + off < 2 ^ 64)
    (hf : FieldAt m chunk S.bst (S.sb + off) v) :
    Exec.evalExpr ge e le m (statsF fld ty) = some v := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, E.find_stats, typeof, Exec.derefLoc]
  simp only [hacc]
  simp only [Cfrontend.Ctypes.access_mode, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, Alloc.Mptr_eq, hp.load, hfld]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [unsigned_add_off S.sofs h0 h1]
  exact hf.load

/-- `stats->fld = rhs` at byte `off`, `rhs` already of the member's type. -/
theorem wp_statsStore {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {fld : ident} {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {off : Int}
    (hge : PTree.get dense.id.«nauty:stats» e = none)
    (hfld : ∀ l o, Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) fld (.Vptr l o) =
      some (l, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (hacc : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hp : PtrAt m E.stats (.Vptr S.bst S.sofs)) (h0 : 0 ≤ off) (h1 : S.sb + off < 2 ^ 64)
    (hw : Mem.valid_access m chunk S.bst (zOfInt (S.sb + off)) .Writable)
    {rhs : expr} {w w' : val} (hr : Exec.evalExpr ge e le m rhs = some w)
    (hc : Cfrontend.Cop.sem_cast w (typeof rhs) ty m = some w')
    (hQ : ∀ m', Mem.store chunk m S.bst (zOfInt (S.sb + off)) w' = some m' →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (statsF fld ty) rhs) Q e le m := by
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ w' hw
  apply wp_assign_eval
  simp only [hr, show typeof (statsF fld ty) = ty from rfl, hc]
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hge, E.find_stats, Exec.derefLoc,
    Exec.assignLoc]
  simp only [hacc]
  simp only [Cfrontend.Ctypes.access_mode, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, Alloc.Mptr_eq, hp.load,
    show typeof (.Ederef (.Evar dense.id.«nauty:stats» (tptr (Tstruct dense.id.«_1024» noattr)))
      (Tstruct dense.id.«_1024» noattr)) = Tstruct dense.id.«_1024» noattr from rfl, hfld,
    show typeof (statsF fld ty) = ty from rfl, hc, Mem.storev]
  rw [unsigned_add_off S.sofs h0 h1, hst]
  exact hQ m' hst

end NautyVerified.Proofs.Search

import NautyVerified.Proofs.Sparse.Blocks
import NautyVerified.Logic.Ints
import NautyVerified.Proofs.Alloc.Zalloc
import NautyVerified.Proofs.Alloc.Keep
import NautyVerified.Proofs.Sparse.Cop

/-!
# Array elements through any pointer expression

`eval_idx` reads `p[a]` and `wp_idx_store` writes it, for a pointer
expression `p` of type `ty *` (a temporary or a pointer global) holding
the start of an array of `ty`, and an index `a` of type `int` or (`_l`
forms) `unsigned long`. Stated over any global environment.
-/

namespace NautyVerified.Proofs.Sparse

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs

variable {xi : ExternalCalls} {ge : genv}

/-- C's `p + i`, for an `unsigned long` index `i` inside the array, is the
address of element `i`. -/
theorem addr_elem_l (ofs : ptrofs) (sz : Z) (chunk : memory_chunk)
    (hsz : intOfZ sz = csize chunk) {base : Int} (hbase : intOfZ (Ptrofs.unsigned ofs) = base)
    {i : Nat} (hi : i < 2 ^ 63) (hfit : base + csize chunk * i < 2 ^ 64) :
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_int64 (lr i)))) =
      elemOfs chunk base i := by
  apply intOfZ_injective
  rw [intOfZ_Ptrofs_unsigned, elemOfs, intOfZ_zOfInt]
  simp only [bvp_add, bvp_mul, bvp_repr, bvp_of_int64, hsz, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_ofInt, Alloc.toNat_lr hi]
  have hc := csize_pos chunk
  have hbase' : ((bvp ofs).toNat : Int) = base := by rw [← hbase, intOfZ_Ptrofs_unsigned]
  have hcs : csize chunk ≤ 8 := by cases chunk <;> decide
  have e1 : (csize chunk % ((2 ^ 64 : Nat) : Int)).toNat = (csize chunk).toNat := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rw [e1]
  have hprod : (((csize chunk).toNat * i : Nat) : Int) = csize chunk * i := by
    push_cast; rw [Int.toNat_of_nonneg (by omega)]
  have hb0 : 0 ≤ base := by rw [← hbase']; exact Int.natCast_nonneg _
  have hlt : (csize chunk).toNat * i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  have hlt2 : (bvp ofs).toNat + (csize chunk).toNat * i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2]
  push_cast
  omega

/-- Reading `p[a]`, `a` an `int` index holding `c < n`. -/
theorem eval_idx {e : env} {le : temp_env} {m : mem} {pe : expr} {ty : Cfrontend.Ctypes.type}
    {chunk : memory_chunk} {bo : block} {ofs : ptrofs} {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m chunk bo (intOfZ (Ptrofs.unsigned ofs)) vals n) (hn : n < 2147483648)
    (hp : Exec.evalExpr ge e le m pe = some (.Vptr bo ofs)) (hpty : typeof pe = tptr ty)
    (hmode : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hsz : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv ty) = csize chunk)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m (.Ederef (.Ebinop .Oadd pe a (tptr ty)) ty) = some (vals c) := by
  simp only [Exec.evalExpr, hp, ha, hty, hpty]
  simp only [cop, Exec.derefLoc, hmode]
  apply load_array harr hc
  apply addr_elem ofs _ chunk hsz rfl (by omega)
  have hf := harr.fits
  have hcs : csize chunk ≤ 8 := by cases chunk <;> decide
  have : csize chunk * c ≤ csize chunk * n :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by have := csize_pos chunk; omega)
  omega

/-- Reading `p[a]`, `a` an `unsigned long` index holding `c < n`. -/
theorem eval_idx_l {e : env} {le : temp_env} {m : mem} {pe : expr} {ty : Cfrontend.Ctypes.type}
    {chunk : memory_chunk} {bo : block} {ofs : ptrofs} {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m chunk bo (intOfZ (Ptrofs.unsigned ofs)) vals n) (hn : n < 2 ^ 63)
    (hp : Exec.evalExpr ge e le m pe = some (.Vptr bo ofs)) (hpty : typeof pe = tptr ty)
    (hmode : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hsz : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv ty) = csize chunk)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vlong (lr c))) (hty : typeof a = tulong) :
    Exec.evalExpr ge e le m (.Ederef (.Ebinop .Oadd pe a (tptr ty)) ty) = some (vals c) := by
  simp only [Exec.evalExpr, hp, ha, hty, hpty]
  simp only [cop, Exec.derefLoc, hmode]
  apply load_array harr hc
  have hf := harr.fits
  have hb := harr.base_nonneg
  have hcp := csize_pos chunk
  have : csize chunk * c ≤ csize chunk * n :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  apply addr_elem_l ofs _ chunk hsz rfl (by omega) (by omega)

/-- Writing `p[a] = x`, `a` an `int` index holding `c < n`. -/
theorem wp_idx_store {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {pe : expr}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {bo : block} {ofs : ptrofs}
    {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m chunk bo (intOfZ (Ptrofs.unsigned ofs)) vals n) (hn : n < 2147483648)
    (hp : Exec.evalExpr ge e le m pe = some (.Vptr bo ofs)) (hpty : typeof pe = tptr ty)
    (hmode : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hsz : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv ty) = csize chunk)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (rty : Cfrontend.Ctypes.type) (hrty : typeof rhs = rty) (v w : val)
    (hrhs : Exec.evalExpr ge e le m rhs = some v)
    (hcast : Cfrontend.Cop.sem_cast v rty ty m = some w)
    (hw : Val.load_result chunk w = w)
    (hQ : ∀ m', ArrayAt m' chunk bo (intOfZ (Ptrofs.unsigned ofs)) (upd vals c w) n →
      Unch m m' (· = bo) → Alloc.Keep m m' bo → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (.Ebinop .Oadd pe a (tptr ty)) ty) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc w hw
  have haddr : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv ty)) (Ptrofs.of_ints (ir c)))) =
      elemOfs chunk (intOfZ (Ptrofs.unsigned ofs)) c := by
    apply addr_elem ofs _ chunk hsz rfl (by omega)
    have hf := harr.fits
    have : csize chunk * c ≤ csize chunk * n :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by have := csize_pos chunk; omega)
    omega
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hpty, hrhs, hrty]
  simp only [typeof, cop, hcast, Exec.assignLoc, hmode, Mem.storev]
  rw [haddr, hst]
  exact hQ m' harr' (Unch.store hst rfl) (Alloc.Keep.store hst (by
    have := harr.base_nonneg; have := csize_pos chunk
    simp only [elemOfs, intOfZ_zOfInt]
    have : 0 ≤ csize chunk * (c : Int) := Int.mul_nonneg (by omega) (by omega)
    omega))
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

/-- Writing `p[a] = x`, `a` an `unsigned long` index holding `c < n`. -/
theorem wp_idx_store_l {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {pe : expr}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {bo : block} {ofs : ptrofs}
    {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m chunk bo (intOfZ (Ptrofs.unsigned ofs)) vals n) (hn : n < 2 ^ 63)
    (hp : Exec.evalExpr ge e le m pe = some (.Vptr bo ofs)) (hpty : typeof pe = tptr ty)
    (hmode : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hsz : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv ty) = csize chunk)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vlong (lr c))) (hty : typeof a = tulong)
    (rhs : expr) (rty : Cfrontend.Ctypes.type) (hrty : typeof rhs = rty) (v w : val)
    (hrhs : Exec.evalExpr ge e le m rhs = some v)
    (hcast : Cfrontend.Cop.sem_cast v rty ty m = some w)
    (hw : Val.load_result chunk w = w)
    (hQ : ∀ m', ArrayAt m' chunk bo (intOfZ (Ptrofs.unsigned ofs)) (upd vals c w) n →
      Unch m m' (· = bo) → Alloc.Keep m m' bo → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (.Ebinop .Oadd pe a (tptr ty)) ty) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc w hw
  have hf := harr.fits
  have hb := harr.base_nonneg
  have hcp := csize_pos chunk
  have : csize chunk * c ≤ csize chunk * n :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have haddr := addr_elem_l ofs (Cfrontend.Ctypes.sizeof ge.genv_cenv ty) chunk hsz rfl (i := c)
    (by omega) (by omega)
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hpty, hrhs, hrty]
  simp only [typeof, cop, hcast, Exec.assignLoc, hmode, Mem.storev]
  rw [haddr, hst]
  exact hQ m' harr' (Unch.store hst rfl) (Alloc.Keep.store hst (by
    have := harr.base_nonneg; have := csize_pos chunk
    simp only [elemOfs, intOfZ_zOfInt]
    have : 0 ≤ csize chunk * (c : Int) := Int.mul_nonneg (by omega) (by omega)
    omega))
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

/-- `eval_idx` for a pointer temporary `q`. -/
theorem eval_tidx {e : env} {le : temp_env} {m : mem} {q : ident} {ty : Cfrontend.Ctypes.type}
    {chunk : memory_chunk} {bo : block} {ofs : ptrofs} {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m chunk bo (intOfZ (Ptrofs.unsigned ofs)) vals n) (hn : n < 2147483648)
    (hq : PTree.get q le = some (.Vptr bo ofs))
    (hmode : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hsz : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv ty) = csize chunk)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m (.Ederef (.Ebinop .Oadd (.Etempvar q (tptr ty)) a (tptr ty)) ty) =
      some (vals c) :=
  eval_idx (pe := .Etempvar q (tptr ty)) harr hn hq rfl hmode hsz a c hc ha hty

end NautyVerified.Proofs.Sparse

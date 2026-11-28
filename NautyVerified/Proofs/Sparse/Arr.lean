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

/-- `wp_idx_store`, keeping a second array of the same block that lies after
the first. -/
theorem wp_idx_store_far {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {pe : expr}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {bo : block} {ofs : ptrofs}
    {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m chunk bo (intOfZ (Ptrofs.unsigned ofs)) vals n) (hn : n < 2147483648)
    {base' : Int} {vals' : Nat → val} {n' : Nat} (hfar : ArrayAt m chunk bo base' vals' n')
    (hb : intOfZ (Ptrofs.unsigned ofs) + csize chunk * n ≤ base')
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
      ArrayAt m' chunk bo base' vals' n' →
      Unch m m' (· = bo) → Alloc.Keep m m' bo → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (.Ebinop .Oadd pe a (tptr ty)) ty) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc w hw
  have hcp := csize_pos chunk
  have hcn : csize chunk * ((c : Int) + 1) ≤ csize chunk * n :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have haddr : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv ty)) (Ptrofs.of_ints (ir c)))) =
      elemOfs chunk (intOfZ (Ptrofs.unsigned ofs)) c := by
    apply addr_elem ofs _ chunk hsz rfl (by omega)
    have hf := harr.fits
    have : csize chunk * c ≤ csize chunk * n :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  have hfar' : ArrayAt m' chunk bo base' vals' n' := hfar.store_away hst (.inr (.inl (by
    simp only [elemOfs, intOfZ_zOfInt]
    rw [Int.mul_add, Int.mul_one] at hcn
    omega)))
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hpty, hrhs, hrty]
  simp only [typeof, cop, hcast, Exec.assignLoc, hmode, Mem.storev]
  rw [haddr, hst]
  exact hQ m' harr' hfar' (Unch.store hst rfl) (Alloc.Keep.store hst (by
    have := harr.base_nonneg
    simp only [elemOfs, intOfZ_zOfInt]
    have : 0 ≤ csize chunk * (c : Int) := Int.mul_nonneg (by omega) (by omega)
    omega))
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

/-- `wp_idx_store`, recording that the block changed only inside the array. -/
theorem wp_idx_store_out {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {pe : expr}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {bo : block} {ofs : ptrofs}
    {vals : Nat → val} {n : Nat}
    (harr : ArrayAt m chunk bo (intOfZ (Ptrofs.unsigned ofs)) vals n) (hn : n < 2147483648)
    {lo hi : Int} (hlo : lo ≤ intOfZ (Ptrofs.unsigned ofs))
    (hhi : intOfZ (Ptrofs.unsigned ofs) + csize chunk * n ≤ hi)
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
      Outside m m' bo lo hi →
      Unch m m' (· = bo) → Alloc.Keep m m' bo → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (.Ebinop .Oadd pe a (tptr ty)) ty) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc w hw
  have hcp := csize_pos chunk
  have haddr : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv ty)) (Ptrofs.of_ints (ir c)))) =
      elemOfs chunk (intOfZ (Ptrofs.unsigned ofs)) c := by
    apply addr_elem ofs _ chunk hsz rfl (by omega)
    have hf := harr.fits
    have : csize chunk * c ≤ csize chunk * n :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  have ho : Outside m m' bo lo hi := Outside.store harr hc hst hlo hhi
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hpty, hrhs, hrty]
  simp only [typeof, cop, hcast, Exec.assignLoc, hmode, Mem.storev]
  rw [haddr, hst]
  exact hQ m' harr' ho (Unch.store hst rfl) (Alloc.Keep.store hst (by
    have := harr.base_nonneg
    simp only [elemOfs, intOfZ_zOfInt]
    have : 0 ≤ csize chunk * (c : Int) := Int.mul_nonneg (by omega) (by omega)
    omega))
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

/-- An array of a block past the range a computation changed survives. -/
theorem _root_.NautyVerified.Logic.ArrayAt.past {m m' : mem} {chunk : memory_chunk} {b : block}
    {base : Int} {vals : Nat → val} {N : Nat} (h : ArrayAt m chunk b base vals N) {lo hi : Int}
    (ho : Outside m m' b lo hi) (hb : hi ≤ base) : ArrayAt m' chunk b base vals N := by
  have hc := csize_pos chunk
  refine ⟨h.base_nonneg, h.fits, fun i hi' => ?_, fun i hi' => ho.access _ _ _ (h.writable i hi')⟩
  have h0 : 0 ≤ csize chunk * (i : Int) := Int.mul_nonneg (by omega) (by omega)
  rw [elemOfs, ho.load _ _ (.inr (by omega))]
  exact h.load i hi'

/-! ### Arrays of small naturals -/

/-- Two adjacent arrays of a block as one. -/
theorem _root_.NautyVerified.Logic.ArrayAt.append {m : mem} {chunk : memory_chunk} {b : block} {base : Int}
    {v1 v2 : Nat → val} {n1 n2 : Nat} (h1 : ArrayAt m chunk b base v1 n1)
    (h2 : ArrayAt m chunk b (base + csize chunk * n1) v2 n2) :
    ArrayAt m chunk b base (fun i => if i < n1 then v1 i else v2 (i - n1)) (n1 + n2) := by
  have hc := csize_pos chunk
  refine ⟨h1.base_nonneg, by have := h2.fits; push_cast; rw [Int.mul_add]; omega,
    fun i hi => ?_, fun i hi => ?_⟩
  · by_cases h : i < n1
    · rw [ite_eq_left h]; exact h1.load i h
    · rw [ite_eq_right h]
      have := h2.load (i - n1) (by omega)
      rwa [elemOfs_slice, show n1 + (i - n1) = i by omega] at this
  · by_cases h : i < n1
    · exact h1.writable i h
    · have := h2.writable (i - n1) (by omega)
      rwa [elemOfs_slice, show n1 + (i - n1) = i by omega] at this

/-- Block `b` holds `c` `int`s from offset 0, each a natural below `2^31`
(nausparse.c's `HITS` array). -/
def HitsOk (m : mem) (c : Nat) (b : block) : Prop :=
  ∃ T : Nat → Nat, (∀ i, T i < 2147483648) ∧ ArrayAt m .Mint32 b 0 (fun i => .Vint (ir (T i))) c

theorem HitsOk.unch {m m' : mem} {S : block → Prop} {c : Nat} {b : block} (h : HitsOk m c b)
    (hu : Unch m m' S) (hb : ¬ S b) : HitsOk m' c b :=
  let ⟨T, hT, ha⟩ := h; ⟨T, hT, ha.unch hu hb⟩

theorem HitsOk.zero (m : mem) (b : block) : HitsOk m 0 b :=
  ⟨fun _ => 0, fun _ => Nat.zero_lt_succ _, ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
    fun _ h => absurd h (by omega)⟩⟩

/-- A zero-filled block of `4 * c` bytes. -/
theorem HitsOk.zeros {m : mem} {c : Nat} {b : block} (hz : Alloc.Zeros m b (4 * c))
    (hmal : Alloc.Malloced m b (4 * c)) : HitsOk m c b :=
  ⟨fun _ => 0, fun _ => Nat.zero_lt_succ _, Alloc.Zeros.array hz (fun o h1 h2 => hmal.perm o (by omega) h2)
    (by have := hmal.small; omega) .Mint32 4 rfl rfl (.Vint (ir 0)) rfl c (Nat.le_refl _)⟩

/-- The first `n` entries, as naturals. -/
theorem HitsOk.head {m : mem} {c : Nat} {b : block} (h : HitsOk m c b) {n : Nat} (hn : n ≤ c) :
    ∃ H : Array Nat, H.size = n ∧ ArrayAt m .Mint32 b 0 (ints H) n ∧ ∀ i < n, H[i]! < 2147483648 := by
  obtain ⟨T, hT, ha⟩ := h
  have hg : ∀ i < n, (Array.ofFn (n := n) fun j => T j)[i]! = T i := fun i hi => by
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  refine ⟨Array.ofFn (n := n) fun j => T j, Array.size_ofFn, ?_, fun i hi => by rw [hg i hi]; exact hT i⟩
  have hs := ha.slice 0 n (by omega)
  simp only [Int.mul_zero, Nat.zero_add] at hs
  exact hs.congr fun i hi => by rw [ints, hg i hi]

/-- The entries from `n` on. -/
theorem HitsOk.tail {m : mem} {c : Nat} {b : block} (h : HitsOk m c b) {n : Nat} (hn : n ≤ c) :
    ∃ T : Nat → Nat, (∀ i, T i < 2147483648) ∧
      ArrayAt m .Mint32 b (0 + csize .Mint32 * n) (fun i => .Vint (ir (T i))) (c - n) := by
  obtain ⟨T, hT, ha⟩ := h
  exact ⟨fun i => T (n + i), fun i => hT _, ha.slice n (c - n) (by omega)⟩

/-- The first `n` entries and the rest, together. -/
theorem HitsOk.join {m : mem} {c n : Nat} {b : block} {H : Array Nat}
    (hh : ArrayAt m .Mint32 b 0 (ints H) n) (hs : ∀ i < n, H[i]! < 2147483648) {T : Nat → Nat}
    (hT : ∀ i, T i < 2147483648)
    (ht : ArrayAt m .Mint32 b (0 + csize .Mint32 * n) (fun i => .Vint (ir (T i))) (c - n))
    (hn : n ≤ c) : HitsOk m c b := by
  have ha := hh.append ht
  rw [show n + (c - n) = c by omega] at ha
  refine ⟨fun i => if i < n then H[i]! else T (i - n), fun i => ?_, ha.congr fun i _ => ?_⟩
  · by_cases h : i < n
    · simp only [ite_eq_left h]; exact hs i h
    · simp only [ite_eq_right h]; exact hT _
  · by_cases h : i < n
    · simp only [ite_eq_left h, ints]
    · simp only [ite_eq_right h]

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

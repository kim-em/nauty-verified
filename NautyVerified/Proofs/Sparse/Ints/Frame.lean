import NautyVerified.Proofs.Sparse.Ints.Syntax
import NautyVerified.Proofs.Sparse.Sort.Satisfies

/-!
# The memory `sortints` works on

`Ctx`: the array `x` (block `bx`, element 0 at byte offset `base`, `N`
elements). The keys are the entries themselves; to state the C against
HexGraphIso's `Sort` functions, whose keys are `y[x[i]]`, `Ctx.Y` is an
identity table on `int`'s nonnegative range (a field, so that the kernel
never unfolds a concrete one such as `idY`), so `Y[a[i]] = a[i]`.
`Arr m C a`: memory `m` holds `a` in the array, every entry a nonnegative
`int`. The lemmas evaluate the expressions `sortints` reads and writes, for
cursors `Vptr bx (pt base k)`.
-/

namespace NautyVerified.Proofs.Sparse.Sort.Ints

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

/-- The identity table on `int`'s nonnegative range: the direct keys as an
indirection. -/
@[irreducible] def idY : Array Nat := Array.range 2147483648

omit binary64_certificate binary32_certificate in
theorem idY_size : idY.size = 2147483648 := by unfold idY; simp

omit binary64_certificate binary32_certificate in
theorem idY_get {i : Nat} (h : i < 2147483648) : idY[i]! = i := by
  unfold idY; simp [h]

/-- The block and size of a `sortints` call, and an identity table `Y` (in
the proofs only; `idY` is one) to read the direct keys as HexGraphIso's
indirect ones. -/
structure Ctx where
  bx : block
  base : Int
  N : Nat
  Y : Array Nat

/-- The side conditions every call meets: size in `int` range, a nonempty
array, `Y` the identity on `int`'s nonnegative range. -/
structure Ctx.Ok (C : Ctx) : Prop where
  nN : C.N < 2147483648
  pos : 0 < C.N
  ysize : C.Y.size = 2147483648
  yid : ∀ i < 2147483648, C.Y[i]! = i

omit binary64_certificate binary32_certificate in
theorem Ctx.Ok.nY {C : Ctx} (hC : C.Ok) : C.Y.size < 2147483649 := by
  rw [hC.ysize]; decide

omit binary64_certificate binary32_certificate in
theorem Ctx.Ok.ysmall {C : Ctx} (hC : C.Ok) : ∀ i < C.Y.size, C.Y[i]! < 2147483648 := by
  intro i hi; rw [hC.ysize] at hi; rw [hC.yid i hi]; exact hi

/-- Memory holds `a` in the array, every entry a nonnegative `int`. -/
structure Arr (m : mem) (C : Ctx) (a : Array Nat) : Prop where
  arr : ArrayAt m .Mint32 C.bx C.base (ints a) C.N
  size : a.size = C.N
  bnd : ∀ i < C.N, a[i]! < C.Y.size

/-- What keeps the right scan's cursor inside the array: the left cursor is
past the first element, or a later key is below the pivot. -/
def LowR (C : Ctx) (a : Array Nat) (b c v : Nat) : Prop :=
  1 ≤ b ∨ ∃ p, 1 ≤ p ∧ b ≤ p ∧ p < c ∧ C.Y[a[p]!]! < v

/-- The same at the start of a partition pass: the left scan will move past
the first element, or a later key is below the pivot. -/
def LowP (C : Ctx) (a : Array Nat) (b c v : Nat) : Prop :=
  1 ≤ b ∨ (b < c ∧ C.Y[a[b]!]! ≤ v) ∨ ∃ p, 1 ≤ p ∧ p < c ∧ C.Y[a[p]!]! < v

variable {xi : ExternalCalls} {ge : genv} {C : Ctx}

section
omit binary64_certificate binary32_certificate

theorem Arr.fits {m : mem} {a : Array Nat} (h : Arr m C a) : C.base + 4 * C.N < 2 ^ 64 :=
  h.arr.fits

theorem Arr.base0 {m : mem} {a : Array Nat} (h : Arr m C a) : 0 ≤ C.base := h.arr.base_nonneg

theorem Arr.small (hC : C.Ok) {m : mem} {a : Array Nat} (h : Arr m C a) {i : Nat} (hi : i < C.N) :
    a[i]! < 2147483648 := by
  have := h.bnd i hi; have := hC.nY; omega

end

/-- `p[e]` for a cursor `p` at element `k` and `e` holding `i`. -/
theorem eval_elem {e : env} {le : temp_env} {m : mem} {a : Array Nat} (h : Arr m C a)
    {p : ident} {k : Nat} (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k)))
    (ex : expr) (i : Nat) (hi : (i : Int) < 2147483648) (hki : k + i < C.N)
    (hex : Exec.evalExpr ge e le m ex = some (.Vint (ir i))) (hty : typeof ex = tint) :
    Exec.evalExpr ge e le m (ix p ex) = some (ints a (k + i)) := by
  simp only [ix, pv, Exec.evalExpr, hp, hex, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  rw [pt_add _ _ _ _ hi]
  exact load_array h.arr hki (unsigned_pt h.base0 (by have := h.fits; omega))

/-- `*p` for a cursor `p` at element `k`. -/
theorem eval_dr {e : env} {le : temp_env} {m : mem} {a : Array Nat} (h : Arr m C a)
    {p : ident} {k : Nat} (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k))) (hk : k < C.N) :
    Exec.evalExpr ge e le m (dr p) = some (ints a k) := by
  simp only [dr, pv, Exec.evalExpr, hp]
  simp only [typeof, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  exact load_array h.arr hk (unsigned_pt h.base0 (by have := h.fits; omega))

omit binary64_certificate binary32_certificate in
/-- The key of an entry is the entry. -/
theorem key_self (hC : C.Ok) {m : mem} {a : Array Nat} (h : Arr m C a) {k : Nat} (hk : k < C.N) :
    C.Y[a[k]!]! = a[k]! := by
  have := h.bnd k hk
  rw [hC.ysize] at this
  exact hC.yid _ this

/-- `*p`, the key of element `k`. -/
theorem eval_keyAt {e : env} {le : temp_env} {m : mem} {a : Array Nat} (hC : C.Ok) (h : Arr m C a)
    {p : ident} {k : Nat} (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k))) (hk : k < C.N) :
    Exec.evalExpr ge e le m (dr p) = some (ints C.Y a[k]!) := by
  rw [eval_dr h hp hk]
  simp only [ints, key_self hC h hk]

/-- `p[e]`, the key of element `k + i`. -/
theorem eval_keyIx {e : env} {le : temp_env} {m : mem} {a : Array Nat} (hC : C.Ok) (h : Arr m C a)
    {p : ident} {k : Nat} (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k)))
    (ex : expr) (i : Nat) (hi : (i : Int) < 2147483648) (hki : k + i < C.N)
    (hex : Exec.evalExpr ge e le m ex = some (.Vint (ir i))) (hty : typeof ex = tint) :
    Exec.evalExpr ge e le m (ix p ex) = some (ints C.Y a[k + i]!) := by
  rw [eval_elem h hp ex i hi hki hex hty]
  simp only [ints, key_self hC h hki]

/-- `*p = rhs`, for a cursor at element `k` and a value indexing `Y`. -/
theorem wp_store_dr {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (h : Arr m C a) (hC : C.Ok) {p : ident} {k : Nat}
    (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k))) (hk : k < C.N)
    (rhs : expr) (w : Nat) (hw : w < C.Y.size)
    (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir w))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Arr m' C (a.set! k w) → Unch m m' (· = C.bx) → Alloc.KeepA m m' →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (dr p) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array h.arr hk (.Vint (ir w)) rfl
  apply wp_assign_eval
  simp only [dr, pv, Exec.evalLvalue, Exec.evalExpr, hp, hrhs, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint32 m C.bx (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [unsigned_pt h.base0 (by have := h.fits; omega), hst]
  have hu : Unch m m' (· = C.bx) := Unch.store hst rfl
  refine hQ m' ⟨?_, by simp [h.size], bnd_set h.bnd hw⟩ hu
    (Alloc.KeepA.storeArr h.arr hst)
  rw [← ints_set' (by rw [h.size]; exact hk)]
  exact harr'

/-- `p[ex] = rhs`, for a cursor at element `k`, `ex` holding `i`. -/
theorem wp_store_ix {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (h : Arr m C a) (hC : C.Ok) {p : ident} {k : Nat}
    (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k)))
    (ex : expr) (i : Nat) (hi : (i : Int) < 2147483648) (hki : k + i < C.N)
    (hex : Exec.evalExpr ge e le m ex = some (.Vint (ir i))) (hty : typeof ex = tint)
    (rhs : expr) (w : Nat) (hw : w < C.Y.size)
    (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir w))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Arr m' C (a.set! (k + i) w) → Unch m m' (· = C.bx) → Alloc.KeepA m m' →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (ix p ex) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array h.arr hki (.Vint (ir w)) rfl
  apply wp_assign_eval
  simp only [ix, pv, Exec.evalLvalue, Exec.evalExpr, hp, hex, hty, hrhs, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint32 m C.bx (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [pt_add _ _ _ _ hi, unsigned_pt h.base0 (by have := h.fits; omega), hst]
  have hu : Unch m m' (· = C.bx) := Unch.store hst rfl
  refine hQ m' ⟨?_, by simp [h.size], bnd_set h.bnd hw⟩ hu
    (Alloc.KeepA.storeArr h.arr hst)
  rw [← ints_set' (by rw [h.size]; exact hki)]
  exact harr'

/-! ## Cursor arithmetic and comparison -/

theorem eval_pcmp {e : env} {le : temp_env} {m : mem} {a : Array Nat} (h : Arr m C a) (hC : C.Ok)
    {p q : ident} {k1 k2 : Nat}
    (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k1)))
    (hq : PTree.get q le = some (.Vptr C.bx (pt C.base k2))) (hk1 : k1 ≤ C.N) (hk2 : k2 ≤ C.N) :
    (Exec.evalExpr ge e le m (.Ebinop .Ole (pv p) (pv q) tint) =
      some (Val.of_bool (decide (k1 ≤ k2)))) ∧
    (Exec.evalExpr ge e le m (.Ebinop .Oge (pv p) (pv q) tint) =
      some (Val.of_bool (decide (k2 ≤ k1)))) ∧
    (Exec.evalExpr ge e le m (.Ebinop .Ogt (pv p) (pv q) tint) =
      some (Val.of_bool (decide (k2 < k1)))) := by
  have hf := h.fits
  have hb := h.base0
  simp only [pv, Exec.evalExpr, hp, hq]
  simp only [typeof, cop]
  rw [cmp_pt h.arr hC.pos hk1 hk2, cmp_pt h.arr hC.pos hk1 hk2, cmp_pt h.arr hC.pos hk1 hk2]
  simp only [Option.map_some]
  rw [cmpu_le_pt hb (by omega) (by omega), cmpu_ge_pt hb (by omega) (by omega),
    cmpu_gt_pt hb (by omega) (by omega)]
  exact ⟨rfl, rfl, rfl⟩

theorem eval_pdiff {e : env} {le : temp_env} {m : mem} (hC : C.Ok)
    {p q : ident} {k1 k2 : Nat}
    (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k1)))
    (hq : PTree.get q le = some (.Vptr C.bx (pt C.base k2))) (hk1 : k1 ≤ C.N) (hk2 : k2 ≤ C.N) :
    Exec.evalExpr ge e le m (.Ecast (.Ebinop .Osub (pv p) (pv q) tlong) tint) =
      some (.Vint (ir ((k1 : Int) - k2))) := by
  have := hC.nN
  simp only [pv, Exec.evalExpr, hp, hq]
  simp only [typeof, cop]
  rw [diff_pt C.base (by omega) (by omega)]

end NautyVerified.Proofs.Sparse.Sort.Ints

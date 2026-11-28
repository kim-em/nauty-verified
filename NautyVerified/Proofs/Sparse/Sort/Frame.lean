import NautyVerified.Proofs.Sparse.Sort.Ptr
import NautyVerified.Proofs.Sparse.Sort.Cop
import NautyVerified.Proofs.Alloc.KeepV

/-!
# The memory a sort works on

`Ctx`: the array `x` (block `bx`, element 0 at byte offset `base`, `N`
elements) and the keys `y` (block `bk` at `yofs`, holding `Y`). `Arr m C a`:
memory `m` holds `a` in the array and `Y` in the keys, every entry of `a`
indexes `Y`. The lemmas evaluate the expressions `sortindirect` reads and
writes, for cursors `Vptr bx (pt base k)`.
-/

namespace NautyVerified.Proofs.Sparse.Sort

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

/-- The blocks and fixed contents of a sort call. -/
structure Ctx where
  bx : block
  base : Int
  N : Nat
  bk : block
  yofs : ptrofs
  Y : Array Nat

/-- The side conditions every sort call meets: separate blocks, sizes and keys
in `int` range, a nonempty array. -/
structure Ctx.Ok (C : Ctx) : Prop where
  ne : C.bx ≠ C.bk
  nN : C.N < 2147483648
  nY : C.Y.size < 2147483648
  ysmall : ∀ i < C.Y.size, C.Y[i]! < 2147483648
  pos : 0 < C.N

/-- Memory holds `a` in the array and the keys `Y`; `a` indexes `Y`. -/
structure Arr (m : mem) (C : Ctx) (a : Array Nat) : Prop where
  arr : ArrayAt m .Mint32 C.bx C.base (ints a) C.N
  keys : ArrayAt m .Mint32 C.bk (intOfZ (Ptrofs.unsigned C.yofs)) (ints C.Y) C.Y.size
  size : a.size = C.N
  bnd : ∀ i < C.N, a[i]! < C.Y.size

variable {xi : ExternalCalls} {ge : genv} {C : Ctx}

section
omit binary64_certificate binary32_certificate

theorem Arr.fits {m : mem} {a : Array Nat} (h : Arr m C a) : C.base + 4 * C.N < 2 ^ 64 :=
  h.arr.fits

theorem Arr.base0 {m : mem} {a : Array Nat} (h : Arr m C a) : 0 ≤ C.base := h.arr.base_nonneg

theorem Arr.small (hC : C.Ok) {m : mem} {a : Array Nat} (h : Arr m C a) {i : Nat} (hi : i < C.N) :
    a[i]! < 2147483648 := by
  have := h.bnd i hi; have := hC.nY; omega

/-- A write of `w < |Y|` at `k < N`. -/
theorem bnd_set {a : Array Nat} {N M : Nat} (hb : ∀ i < N, a[i]! < M) {k w : Nat} (hw : w < M) :
    ∀ i < N, (a.set! k w)[i]! < M := by
  intro i hi
  by_cases hik : i = k
  · subst hik
    by_cases hs : i < a.size
    · rw [Array.getElem!_set!_self _ _ _ hs]; exact hw
    · rw [show a.set! i w = a by simp [Array.set!, Array.setIfInBounds, hs]]; exact hb i hi
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hik)]; exact hb i hi

theorem ints_set' {a : Array Nat} {k : Nat} (hk : k < a.size) (w : Nat) :
    upd (ints a) k (.Vint (ir (w : Int))) = ints (a.set! k w) := (ints_set hk w).symm

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

/-- `y[e]` for `e` holding an index `w` of the keys. -/
theorem eval_key {e : env} {le : temp_env} {m : mem} {a : Array Nat} (hC : C.Ok) (h : Arr m C a)
    (hy : PTree.get id.«y» le = some (.Vptr C.bk C.yofs))
    (ex : expr) (w : Nat) (hw : w < C.Y.size)
    (hex : Exec.evalExpr ge e le m ex = some (.Vint (ir w))) (hty : typeof ex = tint) :
    Exec.evalExpr ge e le m (ix id.«y» ex) = some (ints C.Y w) :=
  eval_at h.keys hC.nY id.«y» hy ex w hw hex hty

/-- `y[*p]`: the key of element `k`. -/
theorem eval_keyAt {e : env} {le : temp_env} {m : mem} {a : Array Nat} (hC : C.Ok) (h : Arr m C a)
    (hy : PTree.get id.«y» le = some (.Vptr C.bk C.yofs))
    {p : ident} {k : Nat} (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k))) (hk : k < C.N) :
    Exec.evalExpr ge e le m (ix id.«y» (dr p)) = some (ints C.Y a[k]!) :=
  eval_key hC h hy (dr p) a[k]! (h.bnd k hk) (eval_dr h hp hk) rfl

/-- `y[p[e]]`: the key of element `k + i`. -/
theorem eval_keyIx {e : env} {le : temp_env} {m : mem} {a : Array Nat} (hC : C.Ok) (h : Arr m C a)
    (hy : PTree.get id.«y» le = some (.Vptr C.bk C.yofs))
    {p : ident} {k : Nat} (hp : PTree.get p le = some (.Vptr C.bx (pt C.base k)))
    (ex : expr) (i : Nat) (hi : (i : Int) < 2147483648) (hki : k + i < C.N)
    (hex : Exec.evalExpr ge e le m ex = some (.Vint (ir i))) (hty : typeof ex = tint) :
    Exec.evalExpr ge e le m (ix id.«y» (ix p ex)) = some (ints C.Y a[k + i]!) :=
  eval_key hC h hy (ix p ex) a[k + i]! (h.bnd _ hki) (eval_elem h hp ex i hi hki hex hty) rfl

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
  refine hQ m' ⟨?_, h.keys.unch hu (Ne.symm hC.ne), by simp [h.size], bnd_set h.bnd hw⟩ hu
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
  refine hQ m' ⟨?_, h.keys.unch hu (Ne.symm hC.ne), by simp [h.size], bnd_set h.bnd hw⟩ hu
    (Alloc.KeepA.storeArr h.arr hst)
  rw [← ints_set' (by rw [h.size]; exact hki)]
  exact harr'

theorem eval_tv {e : env} {le : temp_env} {m : mem} {x : ident} {w : val}
    (h : PTree.get x le = some w) : Exec.evalExpr ge e le m (tv x) = some w := h

theorem eval_pv {e : env} {le : temp_env} {m : mem} {x : ident} {w : val}
    (h : PTree.get x le = some w) : Exec.evalExpr ge e le m (pv x) = some w := h

/-! ## Cursor arithmetic and comparison -/

theorem eval_padd {e : env} {le : temp_env} {m : mem} {p : ident} {b : block} {base : Int} {k : Nat}
    (hp : PTree.get p le = some (.Vptr b (pt base k)))
    (ex : expr) (i : Nat) (hi : (i : Int) < 2147483648)
    (hex : Exec.evalExpr ge e le m ex = some (.Vint (ir i))) (hty : typeof ex = tint) :
    Exec.evalExpr ge e le m (.Ebinop .Oadd (pv p) ex (tptr tint)) = some (.Vptr b (pt base (k + i))) := by
  simp only [pv, Exec.evalExpr, hp, hex, hty]
  simp only [typeof, cop]
  rw [pt_add _ _ _ _ hi]

theorem eval_psub {e : env} {le : temp_env} {m : mem} {p : ident} {b : block} {base : Int} {k : Nat}
    (ex : expr) (i : Nat) (hi : (i : Int) < 2147483648)
    (hp : PTree.get p le = some (.Vptr b (pt base (k + i))))
    (hex : Exec.evalExpr ge e le m ex = some (.Vint (ir i))) (hty : typeof ex = tint) :
    Exec.evalExpr ge e le m (.Ebinop .Osub (pv p) ex (tptr tint)) = some (.Vptr b (pt base k)) := by
  simp only [pv, Exec.evalExpr, hp, hex, hty]
  simp only [typeof, cop]
  rw [pt_sub _ _ _ _ hi]

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

end NautyVerified.Proofs.Sparse.Sort

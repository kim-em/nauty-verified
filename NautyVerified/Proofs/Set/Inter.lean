import NautyVerified.Proofs.Alloc.KeepV
import NautyVerified.Proofs.Set.Add
import NautyVerified.Logic.For

/-!
# `INTERSECT` over a set

`wp_andWord`: `p[i] = p[i] & q[i]` for `i` holding `k < M` replaces word `k`
of `p` by its conjunction with word `k` of `q`. `wp_interLoop`:
`for (i = 0; i < m; ++i) INTERSECT(p[i], q[i])` leaves `p` holding the
word-wise conjunction (`andW`), which represents the intersection.
-/

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec

variable {xi : ExternalCalls}

/-- `p[e]` for an `unsigned long *` temporary `p`. -/
abbrev word (p : Common.AST.ident) (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (pv p) e (tptr tulong)) tulong

/-- `p[i] = p[i] & q[i];` -/
abbrev andWord (p q i : Common.AST.ident) : statement :=
  sk (.Sassign (word p (.Etempvar i tint))
    (.Ebinop .Oand (word p (.Etempvar i tint)) (word q (.Etempvar i tint)) tulong))

/-- The word-wise conjunction. -/
def andW (wp wq : Nat → Lib.Integers.int64) (w : Nat) : Lib.Integers.int64 :=
  Int64.and (wp w) (wq w)

theorem setRep_andW {n M : Nat} {wp wq : Nat → Lib.Integers.int64}
    {s t : Hex.GraphIso.Nauty.VSet n} (hs : SetRep (fun w => bv64 (wp w)) M s)
    (ht : SetRep (fun w => bv64 (wq w)) M t) :
    SetRep (fun w => bv64 (andW wp wq w)) M (s.inter t) := by
  have h := setRep_inter hs ht
  simp only [andW, bv64_and]
  exact h

theorem wp_andWord {p q i : Common.AST.ident} {f : function} {Q : Post} {e : env} {le : temp_env}
    {m : mem} {bp : block} {pofs : ptrofs} {bq : block} {qofs : ptrofs}
    {wp wq : Nat → Lib.Integers.int64} {M k : Nat}
    (hparr : ArrayAt m .Mint64 bp (intOfZ (Ptrofs.unsigned pofs)) (longs wp) M)
    (hqarr : ArrayAt m .Mint64 bq (intOfZ (Ptrofs.unsigned qofs)) (longs wq) M)
    (hM : M < 2147483648) (hp : PTree.get p le = some (.Vptr bp pofs))
    (hq : PTree.get q le = some (.Vptr bq qofs)) (hk : k < M)
    (hi : PTree.get i le = some (.Vint (ir k)))
    (hQ : ∀ m', ArrayAt m' .Mint64 bp (intOfZ (Ptrofs.unsigned pofs))
        (longs (upd wp k (Int64.and (wp k) (wq k)))) M →
      Unch m m' (· = bp) → Alloc.KeepA m m' → Q.normal E0 e le m') :
    Wp xi ge f (andWord p q i) Q e le m := by
  have hep := eval_word (e := e) hparr hM p hp (.Etempvar i tint) k hk hi rfl
  have heq := eval_word (e := e) hqarr hM q hq (.Etempvar i tint) k hk hi rfl
  obtain ⟨m', hst, harr', -⟩ := store_array hparr hk (.Vlong (Int64.and (wp k) (wq k))) rfl
  wp_step; wp_step
  apply wp_assign_eval
  rw [Exec.evalExpr, hep, heq]
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, hi]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [addr_word hparr hk hM, hst]
  rw [longs_upd] at harr'
  exact hQ m' harr' (Unch.store hst rfl) (Alloc.KeepA.storeArr hparr hst)

/-- Words below `k` conjoined, the rest as in `wp`. -/
def andBelow (wp wq : Nat → Lib.Integers.int64) (k w : Nat) : Lib.Integers.int64 :=
  if w < k then andW wp wq w else wp w

theorem andBelow_succ (wp wq : Nat → Lib.Integers.int64) (k : Nat) :
    upd (andBelow wp wq k) k (Int64.and (andBelow wp wq k k) (wq k)) = andBelow wp wq (k + 1) := by
  funext w
  simp only [upd, andBelow, andW]
  by_cases h : w = k
  · subst h; simp
  · rw [ite_eq_right h]
    by_cases hw : w < k
    · rw [ite_eq_left hw, ite_eq_left (by omega)]
    · rw [ite_eq_right hw, ite_eq_right (by omega)]

theorem wp_interLoop {p q i mv : Common.AST.ident} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {bp : block} {pofs : ptrofs} {bq : block} {qofs : ptrofs}
    {wp wq : Nat → Lib.Integers.int64} {M : Nat}
    (hparr : ArrayAt m .Mint64 bp (intOfZ (Ptrofs.unsigned pofs)) (longs wp) M)
    (hqarr : ArrayAt m .Mint64 bq (intOfZ (Ptrofs.unsigned qofs)) (longs wq) M)
    (hne : bq ≠ bp) (hM : M < 2147483648) (hp : PTree.get p le = some (.Vptr bp pofs))
    (hq : PTree.get q le = some (.Vptr bq qofs)) (hm : PTree.get mv le = some (.Vint (ir M)))
    (hpi : p ≠ i) (hqi : q ≠ i) (hmi : mv ≠ i)
    (hQ : ∀ le' m', ArrayAt m' .Mint64 bp (intOfZ (Ptrofs.unsigned pofs)) (longs (andW wp wq)) M →
      Unch m m' (· = bp) → Alloc.KeepA m m' → (∀ k, k ≠ i → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m') :
    Wp xi ge f (forLoop i mv (andWord p q i)) Q e le m := by
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k ≤ M ∧ PTree.get i le' = some (.Vint (ir k)) ∧ (∀ k', k' ≠ i → PTree.get k' le' = PTree.get k' le) ∧
    ArrayAt m' .Mint64 bp (intOfZ (Ptrofs.unsigned pofs)) (longs (andBelow wp wq k)) M ∧
    Unch m m' (· = bp) ∧ Alloc.KeepA m m'
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k < M ∧ PTree.get i le' = some (.Vint (ir k)) ∧ (∀ k', k' ≠ i → PTree.get k' le' = PTree.get k' le) ∧
    ArrayAt m' .Mint64 bp (intOfZ (Ptrofs.unsigned pofs)) (longs (andBelow wp wq (k + 1))) M ∧
    Unch m m' (· = bp) ∧ Alloc.KeepA m m'
  refine wp_forLoop i mv _ M hM Inv Mid ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, ho, -, -, -⟩
    exact ⟨hk, hi, by rw [ho _ hmi, hm]⟩
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, fun k' hk' => temps_gso _ _ hk', ?_, Unch.refl _ _, Alloc.KeepA.refl _⟩
    exact hparr.congr fun j _ => by simp [longs, andBelow]
  · rintro k le' m' hk ⟨-, hi, ho, harr, hu, hkp⟩
    refine wp_andWord harr (hqarr.unch hu hne) hM (by rw [ho _ hpi, hp]) (by rw [ho _ hqi, hq]) hk hi ?_
    intro m'' harr' hu' hk'
    refine ⟨rfl, hk, hi, ho, ?_, hu.trans hu', hkp.trans hk'⟩
    rw [← andBelow_succ]
    exact harr'
  · rintro k le' m' ⟨hk, hi, ho, harr, hu, hkp⟩
    exact ⟨hi, by omega, temps_gss _ _ _, fun k' hk' => by rw [temps_gso _ _ hk', ho _ hk'], harr, hu,
      hkp⟩
  · rintro le' m' ⟨-, -, ho, harr, hu, hkp⟩
    exact hQ le' m' (harr.congr fun j hj => by simp [longs, andBelow, hj]) hu hkp ho

end NautyVerified.Proofs.Set

import NautyVerified.Proofs.Sparse.Sort.Scan

/-!
# The pivot

`wp_med3`: SimplExpr's lowering of `SORT_MEDIAN_OF_3(a, b, c)` into a
temporary leaves HexGraphIso's `Sort.median`. `wp_pivot`: the pivot block of
`sortindirect` sets `v` to `Sort.pivot a Y s nn` (median of three keys below
320 entries, median of three medians from 320) and changes no memory.
-/

namespace NautyVerified.Proofs.Sparse.Sort

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Spec.SortC
open Hex.GraphIso.Nauty.Sparse.Sort (median)

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {ge : genv} {C : Ctx}

omit binary64_certificate binary32_certificate in
theorem ir_divs {a b : Nat} (ha : a < 2147483648) (hb0 : 0 < b) (hb : b < 2147483648) :
    Lib.Integers.Int.divs (ir (a : Int)) (ir (b : Int)) = ir ((a / b : Nat) : Int) := by
  show WordCore.repr 32 (ZArith.BinInt.Z.quot (WordCore.signed _) (WordCore.signed _)) = _
  congr 1
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.quot, intOfZ_zOfInt]
  rw [intOfZ_signed (by decide), intOfZ_signed (by decide)]
  show Int.tdiv (bv32 (ir a)).toInt (bv32 (ir b)).toInt = _
  rw [toInt_ir ⟨by omega, by omega⟩, toInt_ir ⟨by omega, by omega⟩,
    Int.tdiv_eq_ediv_of_nonneg (by omega)]
  push_cast; rfl

omit binary64_certificate binary32_certificate in
theorem median_cases (a b c : Nat) :
    median a b c = if a ≤ b then (if b ≤ c then b else if c ≤ a then a else c)
      else if a ≤ c then a else if c ≤ b then b else c := rfl

/-- The temporaries other than `t` agree with `le`. -/
def Only (t : ident) (le le' : temp_env) : Prop := ∀ z, z ≠ t → PTree.get z le' = PTree.get z le

theorem wp_med3 {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} (t : ident)
    (A B Cx : expr) (av bv cv : Nat) (ha : av < 2147483648) (hb : bv < 2147483648)
    (hc : cv < 2147483648)
    (hA : ∀ le', Only t le le' → Exec.evalExpr ge e le' m A = some (.Vint (ir av)))
    (hB : ∀ le', Only t le le' → Exec.evalExpr ge e le' m B = some (.Vint (ir bv)))
    (hC : ∀ le', Only t le le' → Exec.evalExpr ge e le' m Cx = some (.Vint (ir cv)))
    (htA : typeof A = tint) (htB : typeof B = tint) (htC : typeof Cx = tint)
    (hQ : ∀ le', Only t le le' → PTree.get t le' = some (.Vint (ir (median av bv cv))) →
      Q.normal E0 e le' m) :
    Wp xi ge f (med3 t A B Cx) Q e le m := by
  have o0 : Only t le le := fun _ _ => rfl
  have oS : ∀ le' w, Only t le le' → Only t le (PTree.set t w le') := fun le' w h z hz => by
    rw [temps_gso _ _ hz]; exact h z hz
  -- `t = (int) X; t = (int) t;` and once more
  have fin1 : ∀ (X : expr) (x : Nat), (∀ le', Only t le le' → Exec.evalExpr ge e le' m X =
      some (.Vint (ir x))) → typeof X = tint → x = median av bv cv →
      ∀ (Q' : Post), (∀ le', Only t le le' → PTree.get t le' = some (.Vint (ir (median av bv cv))) →
        Q'.normal E0 e le' m) →
      Wp xi ge f (.Ssequence (sk (.Sset t (.Ecast X tint))) (castT t)) Q' e le m := by
    intro X x hX hXt hx Q' hQ'
    simp only [sk, castT]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, hX le o0, hXt]
    simp only [cop, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    refine hQ' _ (oS _ _ (oS _ _ o0)) ?_
    rw [temps_gss, hx]
  have fin2 : ∀ (X : expr) (x : Nat), (∀ le', Only t le le' → Exec.evalExpr ge e le' m X =
      some (.Vint (ir x))) → typeof X = tint → x = median av bv cv →
      Wp xi ge f (.Ssequence (.Ssequence (sk (.Sset t (.Ecast X tint))) (castT t)) (castT t))
        Q e le m := by
    intro X x hX hXt hx
    apply wp_seq
    refine fin1 X x hX hXt hx _ ?_
    intro le' ho ht
    simp only [seqPost, Post.after, castT]
    apply wp_set_eval
    simp only [Exec.evalExpr, ht, typeof, cop]
    refine hQ _ (oS _ _ ho) ?_
    rw [temps_gss]
  have cmp : ∀ (X Y : expr) (x y : Nat), x < 2147483648 → y < 2147483648 →
      Exec.evalExpr ge e le m X = some (.Vint (ir x)) → Exec.evalExpr ge e le m Y = some (.Vint (ir y)) →
      typeof X = tint → typeof Y = tint →
      Exec.evalExpr ge e le m (.Ebinop .Ole X Y tint) = some (Val.of_bool (decide (x ≤ y))) := by
    intro X Y x y hx hy hX hY hXt hYt
    simp only [Exec.evalExpr, hX, hY, hXt, hYt, cop, key_cmp _ _ hy hx]
    congr 2
    by_cases h : x ≤ y <;> simp [h] <;> omega
  have hA0 := hA le o0
  have hB0 := hB le o0
  have hC0 := hC le o0
  simp only [med3, sk]
  wp_step; wp_step
  apply wp_if_eval
  rw [cmp A B av bv ha hb hA0 hB0 htA htB]
  simp only [typeof, cop]
  by_cases hab : av ≤ bv
  · rw [ite_eq_left (by simpa using hab)]
    wp_step; wp_step
    apply wp_if_eval
    rw [cmp B Cx bv cv hb hc hB0 hC0 htB htC]
    simp only [typeof, cop]
    by_cases hbc : bv ≤ cv
    · rw [ite_eq_left (by simpa using hbc)]
      exact fin1 B bv hB htB (by simp [median_cases, hab, hbc]) Q hQ
    · rw [ite_eq_right (by simpa using hbc)]
      wp_step; wp_step
      apply wp_if_eval
      rw [cmp Cx A cv av hc ha hC0 hA0 htC htA]
      simp only [typeof, cop]
      by_cases hca : cv ≤ av
      · rw [ite_eq_left (by simpa using hca)]
        exact fin2 A av hA htA (by simp [median_cases, hab, hbc, hca])
      · rw [ite_eq_right (by simpa using hca)]
        exact fin2 Cx cv hC htC (by simp [median_cases, hab, hbc, hca])
  · rw [ite_eq_right (by simpa using hab)]
    wp_step; wp_step
    apply wp_if_eval
    rw [cmp A Cx av cv ha hc hA0 hC0 htA htC]
    simp only [typeof, cop]
    by_cases hac : av ≤ cv
    · rw [ite_eq_left (by simpa using hac)]
      exact fin1 A av hA htA (by simp [median_cases, hab, hac]) Q hQ
    · rw [ite_eq_right (by simpa using hac)]
      wp_step; wp_step
      apply wp_if_eval
      rw [cmp Cx B cv bv hc hb hC0 hB0 htC htB]
      simp only [typeof, cop]
      by_cases hcb : cv ≤ bv
      · rw [ite_eq_left (by simpa using hcb)]
        exact fin2 B bv hB htB (by simp [median_cases, hab, hac, hcb])
      · rw [ite_eq_right (by simpa using hcb)]
        exact fin2 Cx cv hC htC (by simp [median_cases, hab, hac, hcb])

/-- The temporaries the pivot block writes. -/
def OthV (le le' : temp_env) : Prop :=
  ∀ z, z ≠ id.«v» → z ≠ id.«v1» → z ≠ id.«v2» → z ≠ id.«v3» → z ≠ idOf 704 → z ≠ idOf 705 →
    z ≠ idOf 706 → z ≠ idOf 707 → z ≠ idOf 708 → PTree.get z le' = PTree.get z le

/-- The key `y[x0[e]]` for `e` holding `i`, in any temporaries keeping `y`, `x0`, `nn`. -/
theorem eval_pk {e : env} {le le' : temp_env} {m : mem} {a : Array Nat} (hC : C.Ok) (h : Arr m C a)
    {s nn : Nat} (hy : PTree.get id.«y» le = some (.Vptr C.bk C.yofs))
    (hx0 : PTree.get id.«x0» le = some (.Vptr C.bx (pt C.base s)))
    (hnn : PTree.get id.«nn» le = some (.Vint (ir nn)))
    (ho : PTree.get id.«y» le' = PTree.get id.«y» le ∧ PTree.get id.«x0» le' = PTree.get id.«x0» le ∧
      PTree.get id.«nn» le' = PTree.get id.«nn» le)
    (ex : expr) (i : Nat) (hsi : s + i < C.N)
    (hex : ∀ le', PTree.get id.«nn» le' = some (.Vint (ir nn)) →
      Exec.evalExpr ge e le' m ex = some (.Vint (ir i))) (hty : typeof ex = tint) :
    Exec.evalExpr ge e le' m (ix id.«y» (ix id.«x0» ex)) = some (.Vint (ir C.Y[a[s + i]!]!)) :=
  eval_keyIx hC h (by rw [ho.1]; exact hy) (by rw [ho.2.1]; exact hx0) ex i
    (by have := hC.nN; omega) hsi (hex le' (by rw [ho.2.2]; exact hnn)) hty

theorem wp_pivot {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (hC : C.Ok) (h : Arr m C a) {s nn : Nat}
    (hy : PTree.get id.«y» le = some (.Vptr C.bk C.yofs))
    (hx0 : PTree.get id.«x0» le = some (.Vptr C.bx (pt C.base s)))
    (hnn : PTree.get id.«nn» le = some (.Vint (ir nn))) (h3 : 3 ≤ nn) (hsn : s + nn ≤ C.N)
    (hQ : ∀ le', OthV le le' → PTree.get id.«v» le' = some (.Vint (ir (Hex.GraphIso.Nauty.Sparse.Sort.pivot a C.Y s nn))) →
      Q.normal E0 e le' m) :
    Wp xi ge f pivot Q e le m := by
  have hN := hC.nN
  let k := fun i => C.Y[a[s + i]!]!
  have hk : ∀ i, s + i < C.N → k i < 2147483648 := fun i hi => hC.ysmall _ (h.bnd _ hi)
  -- index expressions
  have i0 : ∀ le', PTree.get id.«nn» le' = some (.Vint (ir nn)) →
      Exec.evalExpr ge e le' m (ci 0 tint) = some (.Vint (ir ((0 : Nat) : Int))) := fun _ _ => rfl
  have i1 : ∀ le', PTree.get id.«nn» le' = some (.Vint (ir nn)) →
      Exec.evalExpr ge e le' m (ci 1 tint) = some (.Vint (ir ((1 : Nat) : Int))) := fun _ _ => rfl
  have i2 : ∀ le', PTree.get id.«nn» le' = some (.Vint (ir nn)) →
      Exec.evalExpr ge e le' m (ci 2 tint) = some (.Vint (ir ((2 : Nat) : Int))) := fun _ _ => rfl
  have isub : ∀ c : Nat, c ≤ nn → c < 2147483648 → ∀ le', PTree.get id.«nn» le' = some (.Vint (ir nn)) →
      Exec.evalExpr ge e le' m (.Ebinop .Osub (tv id.«nn») (ci c tint) tint) =
        some (.Vint (ir ((nn - c : Nat) : Int))) := by
    intro c hc hc' le' hn
    simp only [Exec.evalExpr, hn, typeof, cop, ir_sub]
    congr 3; omega
  have idiv : ∀ le', PTree.get id.«nn» le' = some (.Vint (ir nn)) →
      Exec.evalExpr ge e le' m (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint) =
        some (.Vint (ir ((nn / 2 : Nat) : Int))) := by
    intro le' hn
    simp only [Exec.evalExpr, hn, typeof, cop]
    have e1 : Lib.Integers.Int.eq (Lib.Integers.Int.repr (zOfInt 2)) Lib.Integers.Int.zero = false :=
      by decide
    have e2 : Lib.Integers.Int.eq (Lib.Integers.Int.repr (zOfInt 2)) Lib.Integers.Int.mone = false :=
      by decide
    rw [e1, e2, Bool.and_false, Bool.or_false]
    simp only [Bool.false_eq_true, ite_false]
    exact congrArg (fun z => some (val.Vint z)) (ir_divs (a := nn) (b := 2) (by omega) (by decide)
      (by decide))
  -- the temporaries every key read uses
  let K := fun (le' : temp_env) => PTree.get id.«y» le' = PTree.get id.«y» le ∧
    PTree.get id.«x0» le' = PTree.get id.«x0» le ∧ PTree.get id.«nn» le' = PTree.get id.«nn» le
  have kO : ∀ (t : ident) le1 le2, t ≠ id.«y» → t ≠ id.«x0» → t ≠ id.«nn» → K le1 → Only t le1 le2 →
      K le2 := by
    intro t le1 le2 h1 h2 h3 hk ho
    exact ⟨(ho _ (Ne.symm h1)).trans hk.1, (ho _ (Ne.symm h2)).trans hk.2.1,
      (ho _ (Ne.symm h3)).trans hk.2.2⟩
  have kS : ∀ (t : ident) le1 w, t ≠ id.«y» → t ≠ id.«x0» → t ≠ id.«nn» → K le1 →
      K (PTree.set t w le1) := by
    intro t le1 w h1 h2 h3 hk
    exact ⟨(temps_gso _ _ (Ne.symm h1)).trans hk.1, (temps_gso _ _ (Ne.symm h2)).trans hk.2.1,
      (temps_gso _ _ (Ne.symm h3)).trans hk.2.2⟩
  have key : ∀ (t : ident) le1, t ≠ id.«y» → t ≠ id.«x0» → t ≠ id.«nn» → K le1 → ∀ (ex : expr) (i : Nat),
      s + i < C.N → (∀ le', PTree.get id.«nn» le' = some (.Vint (ir nn)) →
        Exec.evalExpr ge e le' m ex = some (.Vint (ir i))) → typeof ex = tint →
      ∀ le', Only t le1 le' → Exec.evalExpr ge e le' m (ix id.«y» (ix id.«x0» ex)) =
        some (.Vint (ir (k i))) :=
    fun t le1 h1 h2 h3 hk ex i hi hex hty le' ho =>
      eval_pk hC h hy hx0 hnn (kO t le1 le' h1 h2 h3 hk ho) ex i hi hex hty
  have k0 : K le := ⟨rfl, rfl, rfl⟩
  apply wp_if_eval
  simp only [Exec.evalExpr, hnn, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 320) = ir ((320 : Nat) : Int) from rfl,
    key_cmp nn 320 (by omega) (by decide)]
  by_cases hsmall : nn < 320
  · rw [ite_eq_left (by simpa using hsmall)]
    apply wp_seq
    refine wp_med3 (idOf 704) _ _ _ (k 0) (k (nn / 2)) (k (nn - 1)) (hk _ (by omega))
      (hk _ (by omega)) (hk _ (by omega))
      (key _ le (by decide) (by decide) (by decide) k0 _ 0 (by omega) i0 rfl)
      (key _ le (by decide) (by decide) (by decide) k0 _ (nn / 2) (by omega) idiv rfl)
      (key _ le (by decide) (by decide) (by decide) k0 _ (nn - 1) (by omega) (isub 1 (by omega)
        (by decide)) rfl) rfl rfl rfl ?_
    intro le1 ho1 ht1
    simp only [seqPost, Post.after]
    apply wp_set_eval
    rw [eval_tv ht1]
    refine hQ _ ?_ ?_
    · intro z q1 q2 q3 q4 q5 q6 q7 q8 q9
      rw [temps_gso _ _ q1]; exact ho1 z q5
    · rw [temps_gss]
      unfold Hex.GraphIso.Nauty.Sparse.Sort.pivot
      simp only [hsmall, ite_true]
      rfl
  · rw [ite_eq_right (by simpa using hsmall)]
    have idm : ∀ le', PTree.get id.«nn» le' = some (.Vint (ir nn)) →
        Exec.evalExpr ge e le' m (.Ebinop .Osub (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint)
          (ci 1 tint) tint) = some (.Vint (ir ((nn / 2 - 1 : Nat) : Int))) := by
      intro le' hn
      rw [Exec.evalExpr, idiv le' hn]
      simp only [Exec.evalExpr, typeof, cop]
      rw [show Lib.Integers.Int.repr (zOfInt 1) = ir ((1 : Nat) : Int) from rfl, ir_sub]
      congr 3; omega
    have idp : ∀ le', PTree.get id.«nn» le' = some (.Vint (ir nn)) →
        Exec.evalExpr ge e le' m (.Ebinop .Oadd (.Ebinop .Odiv (tv id.«nn») (ci 2 tint) tint)
          (ci 1 tint) tint) = some (.Vint (ir ((nn / 2 + 1 : Nat) : Int))) := by
      intro le' hn
      rw [Exec.evalExpr, idiv le' hn]
      simp only [Exec.evalExpr, typeof, cop]
      rw [show Lib.Integers.Int.repr (zOfInt 1) = ir ((1 : Nat) : Int) from rfl, ir_add]
      congr 3
    let m1 := median (k 0) (k 1) (k 2)
    let m2 := median (k (nn / 2 - 1)) (k (nn / 2)) (k (nn / 2 + 1))
    let m3 := median (k (nn - 3)) (k (nn - 2)) (k (nn - 1))
    have hm : ∀ x y z : Nat, x < 2147483648 → y < 2147483648 → z < 2147483648 →
        median x y z < 2147483648 := by
      intro x y z hx hy hz
      rcases Hex.GraphIso.Nauty.Sparse.Sort.median_mem x y z with h | h | h <;> rw [h] <;> assumption
    apply wp_seq; apply wp_seq
    refine wp_med3 (idOf 705) _ _ _ (k 0) (k 1) (k 2) (hk _ (by omega)) (hk _ (by omega))
      (hk _ (by omega))
      (key _ le (by decide) (by decide) (by decide) k0 _ 0 (by omega) i0 rfl)
      (key _ le (by decide) (by decide) (by decide) k0 _ 1 (by omega) i1 rfl)
      (key _ le (by decide) (by decide) (by decide) k0 _ 2 (by omega) i2 rfl) rfl rfl rfl ?_
    intro le1 ho1 ht1
    simp only [seqPost, Post.after]
    apply wp_set_eval
    rw [eval_tv ht1]
    simp only [E0_append]
    have K1 : K (PTree.set id.«v1» (.Vint (ir m1)) le1) :=
      kS _ _ _ (by decide) (by decide) (by decide) (kO _ _ _ (by decide) (by decide) (by decide) k0 ho1)
    apply wp_seq; apply wp_seq
    refine wp_med3 (idOf 706) _ _ _ (k (nn / 2 - 1)) (k (nn / 2)) (k (nn / 2 + 1)) (hk _ (by omega))
      (hk _ (by omega)) (hk _ (by omega))
      (key _ _ (by decide) (by decide) (by decide) K1 _ (nn / 2 - 1) (by omega) idm rfl)
      (key _ _ (by decide) (by decide) (by decide) K1 _ (nn / 2) (by omega) idiv rfl)
      (key _ _ (by decide) (by decide) (by decide) K1 _ (nn / 2 + 1) (by omega) idp rfl) rfl rfl rfl ?_
    intro le2 ho2 ht2
    simp only [seqPost, Post.after]
    apply wp_set_eval
    rw [eval_tv ht2]
    simp only [E0_append]
    have K2 : K (PTree.set id.«v2» (.Vint (ir m2)) le2) :=
      kS _ _ _ (by decide) (by decide) (by decide) (kO _ _ _ (by decide) (by decide) (by decide) K1 ho2)
    apply wp_seq; apply wp_seq
    refine wp_med3 (idOf 707) _ _ _ (k (nn - 3)) (k (nn - 2)) (k (nn - 1)) (hk _ (by omega))
      (hk _ (by omega)) (hk _ (by omega))
      (key _ _ (by decide) (by decide) (by decide) K2 _ (nn - 3) (by omega)
        (isub 3 (by omega) (by decide)) rfl)
      (key _ _ (by decide) (by decide) (by decide) K2 _ (nn - 2) (by omega)
        (isub 2 (by omega) (by decide)) rfl)
      (key _ _ (by decide) (by decide) (by decide) K2 _ (nn - 1) (by omega)
        (isub 1 (by omega) (by decide)) rfl) rfl rfl rfl ?_
    intro le3 ho3 ht3
    simp only [seqPost, Post.after]
    apply wp_set_eval
    rw [eval_tv ht3]
    simp only [E0_append]
    let le3' := PTree.set id.«v3» (.Vint (ir m3)) le3
    have hv1 : PTree.get id.«v1» le3' = some (.Vint (ir m1)) := by
      show PTree.get _ (PTree.set _ _ _) = _
      rw [temps_gso, ho3 _ (by decide), temps_gso, ho2 _ (by decide), temps_gss]
    have hv2 : PTree.get id.«v2» le3' = some (.Vint (ir m2)) := by
      show PTree.get _ (PTree.set _ _ _) = _
      rw [temps_gso, ho3 _ (by decide), temps_gss]
    have hv3 : PTree.get id.«v3» le3' = some (.Vint (ir m3)) := temps_gss _ _ _
    apply wp_seq
    refine wp_med3 (idOf 708) (tv id.«v1») (tv id.«v2») (tv id.«v3») m1 m2 m3
      (hm _ _ _ (hk _ (by omega)) (hk _ (by omega)) (hk _ (by omega)))
      (hm _ _ _ (hk _ (by omega)) (hk _ (by omega)) (hk _ (by omega)))
      (hm _ _ _ (hk _ (by omega)) (hk _ (by omega)) (hk _ (by omega)))
      (fun le' ho => by rw [eval_tv]; rw [ho _ (by decide)]; exact hv1)
      (fun le' ho => by rw [eval_tv]; rw [ho _ (by decide)]; exact hv2)
      (fun le' ho => by rw [eval_tv]; rw [ho _ (by decide)]; exact hv3) rfl rfl rfl ?_
    intro le4 ho4 ht4
    simp only [seqPost, Post.after]
    apply wp_set_eval
    rw [eval_tv ht4]
    simp only [E0_append]
    refine hQ _ ?_ ?_
    · intro z q1 q2 q3 q4 q5 q6 q7 q8 q9
      rw [temps_gso _ _ q1, ho4 _ q9]
      show PTree.get z (PTree.set _ _ _) = _
      rw [temps_gso _ _ q4, ho3 _ q8, temps_gso _ _ q3, ho2 _ q7, temps_gso _ _ q2, ho1 _ q6]
    · rw [temps_gss]
      unfold Hex.GraphIso.Nauty.Sparse.Sort.pivot
      simp only [hsmall, ite_false]
      rfl

end NautyVerified.Proofs.Sparse.Sort

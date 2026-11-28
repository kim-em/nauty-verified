import NautyVerified.Proofs.Sparse.Ints.Frame
import NautyVerified.Spec.SparseInts

/-!
# The scans of the three-way partition

`wp_swapThen`: `SORT_SWAP1(*p, *q)` swaps elements `i` and `j`.
`wp_scanL`: the loop `while (xb <= xc && y[*xb] <= v) {...}` with `xa`, `xb`
at elements `aa`, `b` and `xc` at element `c - 1` ends as HexGraphIso's left
scan `iterF (bodyL Y v c)` from `(a, aa, b)`, for any fuel at least `c - b`.
`wp_scanR`: the same for `while (xc >= xb && y[*xc] >= v) {...}` with `xc`,
`xd` at elements `c - 1`, `d - 1` and the right scan `iterF (bodyR Y v b)`.
-/

namespace NautyVerified.Proofs.Sparse.Sort.Ints

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Spec.SortC

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {ge : genv} {C : Ctx}

/-- `SORT_SWAP1(*p, *q); r` for cursors at elements `i` and `j`. -/
theorem wp_swapThen {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (h : Arr m C a) (hC : C.Ok) {p q : ident} {i j : Nat}
    (hp : PTree.get p le = some (.Vptr C.bx (pt C.base i)))
    (hq : PTree.get q le = some (.Vptr C.bx (pt C.base j))) (hi : i < C.N) (hj : j < C.N)
    (hpt : p ≠ id.«tmp1») (hqt : q ≠ id.«tmp1») (r : statement)
    (hr : ∀ m', Arr m' C (a.swapIfInBounds i j) → Unch m m' (· = C.bx) → Alloc.KeepA m m' →
      Wp xi ge f r Q e (PTree.set id.«tmp1» (ints a i) le) m') :
    Wp xi ge f (swapThen p q r) Q e le m := by
  simp only [swapThen, sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_dr h hp hi]
  simp only [E0_append]
  have hp' : PTree.get p (PTree.set id.«tmp1» (ints a i) le) = some (.Vptr C.bx (pt C.base i)) := by
    rw [temps_gso _ _ hpt]; exact hp
  have hq' : PTree.get q (PTree.set id.«tmp1» (ints a i) le) = some (.Vptr C.bx (pt C.base j)) := by
    rw [temps_gso _ _ hqt]; exact hq
  wp_step; wp_step; wp_step
  refine wp_store_dr h hC hp' hi (dr q) a[j]! (h.bnd j hj) (eval_dr h hq' hj) rfl ?_
  intro m1 h1 hu1 hk1
  simp only [E0_append]
  wp_step; wp_step; wp_step
  refine wp_store_dr h1 hC hq' hj (tv id.«tmp1») a[i]! (h.bnd i hi) (temps_gss _ _ _) rfl ?_
  intro m2 h2 hu2 hk2
  simp only [E0_append]
  rw [swap_eq a i j (by rw [h.size]; exact hi) (by rw [h.size]; exact hj)] at h2
  exact hr m2 h2 (hu1.trans hu2) (hk1.trans hk2)

omit binary64_certificate binary32_certificate in
theorem swap_comm (a : Array Nat) (i j : Nat) : a.swapIfInBounds j i = a.swapIfInBounds i j := by
  unfold Array.swapIfInBounds
  by_cases hi : i < a.size <;> by_cases hj : j < a.size <;> simp [hi, hj, Array.swap_comm]

omit binary64_certificate binary32_certificate in
theorem put_eq (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (a.set! i a[j]!).set! j a[i]! = a.swapIfInBounds j i := by
  rw [swap_eq a i j hi hj]; exact swap_comm a j i

/-- `*p = *q; *q = v; r` for cursors at elements `i` and `j`, element `i`
holding `v`: the swap of `j` and `i`. -/
theorem wp_putV {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (h : Arr m C a) (hC : C.Ok) {p q : ident} {i j v : Nat}
    (hp : PTree.get p le = some (.Vptr C.bx (pt C.base i)))
    (hq : PTree.get q le = some (.Vptr C.bx (pt C.base j))) (hi : i < C.N) (hj : j < C.N)
    (hv : PTree.get id.«v» le = some (.Vint (ir v))) (hav : a[i]! = v) (r : statement)
    (hr : ∀ m', Arr m' C (a.swapIfInBounds j i) → Unch m m' (· = C.bx) → Alloc.KeepA m m' →
      Wp xi ge f r Q e le m') :
    Wp xi ge f (.Ssequence (sk (.Sassign (dr p) (dr q)))
      (.Ssequence (sk (.Sassign (dr q) (tv id.«v»))) r)) Q e le m := by
  simp only [sk]
  wp_step; wp_step; wp_step
  refine wp_store_dr h hC hp hi (dr q) a[j]! (h.bnd j hj) (eval_dr h hq hj) rfl ?_
  intro m1 h1 hu1 hk1
  simp only [E0_append]
  wp_step; wp_step; wp_step
  refine wp_store_dr h1 hC hq hj (tv id.«v») v (hav ▸ h.bnd i hi) hv rfl ?_
  intro m2 h2 hu2 hk2
  simp only [E0_append]
  rw [← hav, put_eq a i j (by rw [h.size]; exact hi) (by rw [h.size]; exact hj)] at h2
  exact hr m2 h2 (hu1.trans hu2) (hk1.trans hk2)

/-- The temporaries the left scan writes. -/
def OthL (le le' : temp_env) : Prop :=
  ∀ z, z ≠ id.«xa» → z ≠ id.«xb» → z ≠ id.«tmp1» → z ≠ idOf 711 → PTree.get z le' = PTree.get z le

theorem wp_scanL {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (hC : C.Ok) (h : Arr m C a) {v aa b c fuel : Nat}
    (hv : PTree.get id.«v» le = some (.Vint (ir v))) (hvs : v < 2147483648)
    (hxa : PTree.get id.«xa» le = some (.Vptr C.bx (pt C.base aa)))
    (hxb : PTree.get id.«xb» le = some (.Vptr C.bx (pt C.base b)))
    (hxc : PTree.get id.«xc» le = some (.Vptr C.bx (pt C.base (c - 1))))
    (h1 : 1 ≤ c) (hab : aa ≤ b) (hbc : b ≤ c + 1) (hbN : b ≤ C.N) (hcN : c ≤ C.N)
    (hfuel : c - b ≤ fuel)
    (hQ : ∀ le' m', let r := iterF (bodyL C.Y v c) fuel (a, aa, b)
      Arr m' C r.1 → PTree.get id.«xa» le' = some (.Vptr C.bx (pt C.base r.2.1)) →
      PTree.get id.«xb» le' = some (.Vptr C.bx (pt C.base r.2.2)) → OthL le le' →
      Unch m m' (· = C.bx) → Alloc.KeepA m m' → Q.normal E0 e le' m') :
    Wp xi ge f scanL Q e le m := by
  let B := bodyL C.Y v c
  let R := iterF B fuel (a, aa, b)
  let I := fun (n : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ a' aa' b', Arr m' C a' ∧ iterF B n (a', aa', b') = R ∧
      PTree.get id.«xa» le' = some (.Vptr C.bx (pt C.base aa')) ∧
      PTree.get id.«xb» le' = some (.Vptr C.bx (pt C.base b')) ∧
      aa' ≤ b' ∧ b' ≤ c + 1 ∧ b' ≤ C.N ∧ c - b' ≤ n ∧ OthL le le' ∧ Unch m m' (· = C.bx) ∧
      Alloc.KeepA m m'
  refine wp_loop (I := I) (J := fun n t e' le' m' => ∃ n', n' < n ∧ I n' t e' le' m') ?_ ?_
    (n := fuel) ⟨rfl, rfl, a, aa, b, h, rfl, hxa, hxb, hab, hbc, hbN, hfuel, fun _ _ _ _ _ => rfl,
      Unch.refl _ _, Alloc.KeepA.refl _⟩
  · rintro n t e' le' m' ⟨rfl, rfl, a', aa', b', h', hR, hxa', hxb', hab', hbc', hbN', hn, ho, hu,
      hk⟩
    have hv' : PTree.get id.«v» le' = some (.Vint (ir v)) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide)]; exact hv
    have hxc' : PTree.get id.«xc» le' = some (.Vptr C.bx (pt C.base (c - 1))) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide)]; exact hxc
    have hcmp := (eval_pcmp (ge := ge) (e := e) (m := m') h' hC hxb' hxc' (by omega) (by omega)).1
    simp only [scanL, sk]
    wp_step; wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [hcmp]
    simp only [typeof, cop]
    by_cases hlt : b' < c
    · have hbN : b' < C.N := by omega
      have hks := hC.ysmall _ (h'.bnd b' hbN)
      rw [ite_eq_left (by simp; omega)]
      wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, Exec.evalExpr, eval_keyAt hC h' hxb' hbN, eval_tv hv']
      simp only [ints, typeof, cop, key_cmp _ _ hvs hks, cast_of_bool]
      simp only [E0_append]
      wp_step
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      by_cases hle : C.Y[a'[b']!]! ≤ v
      · rw [ite_eq_left (by simp; omega)]
        apply wp_skip
        simp only [E0_append]
        -- the equality test
        have hxb2 : PTree.get id.«xb» (PTree.set (idOf 711) (Val.of_bool (!decide (v < C.Y[a'[b']!]!))) le') =
            some (.Vptr C.bx (pt C.base b')) := by rw [temps_gso]; exact hxb'
        have hxa2 : PTree.get id.«xa» (PTree.set (idOf 711) (Val.of_bool (!decide (v < C.Y[a'[b']!]!))) le') =
            some (.Vptr C.bx (pt C.base aa')) := by rw [temps_gso]; exact hxa'
        have hv2 : PTree.get id.«v» (PTree.set (idOf 711) (Val.of_bool (!decide (v < C.Y[a'[b']!]!))) le') =
            some (.Vint (ir v)) := by rw [temps_gso]; exact hv'
        wp_step; wp_step; wp_step
        apply wp_if_eval
        rw [Exec.evalExpr, eval_keyAt hC h' hxb2 hbN, eval_tv hv2]
        simp only [ints, typeof, cop, key_eq _ _ hks hvs]
        have hn1 : 1 ≤ n := by omega
        have hstep : ∀ st', B (a', aa', b') = .yield st' →
            iterF B n (a', aa', b') = iterF B (n - 1) st' := by
          intro st' hb
          obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
          simp only [iterF, hb, Nat.add_sub_cancel]
        by_cases heq : C.Y[a'[b']!]! = v
        · rw [ite_eq_left (by simp [heq])]
          refine wp_putV h' hC hxb2 hxa2 hbN (by omega) hv2 (by rw [← key_self hC h' hbN]; exact heq) _ ?_
          intro m2 h2 hu2 hk2
          wp_step; wp_step
          apply wp_set_eval
          rw [eval_padd (by rw [temps_gso]; exact hxa') (ci 1 tint) 1 (by decide) rfl rfl]
          simp only [E0_append]
          wp_step; wp_step
          apply wp_set_eval
          rw [eval_padd (by rw [temps_gso, temps_gso]; exact hxb') (ci 1 tint) 1
            (by decide) rfl rfl]
          refine ⟨n - 1, by omega, by simp, rfl, a'.swapIfInBounds aa' b', aa' + 1, b' + 1, h2, ?_, ?_,
            ?_, by omega, by omega, by omega, by omega, ?_, hu.trans hu2, hk.trans hk2⟩
          · rw [← hR, hstep (a'.swapIfInBounds aa' b', aa' + 1, b' + 1) (by simp [B, bodyL, show ¬ b' ≥ c by omega,
              show ¬ C.Y[a'[b']!]! > v by omega, heq])]
          · rw [temps_gso, temps_gss]
          · simp
          · intro z h1 h2 h3 h4
            simp only [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3, temps_gso _ _ h4]
            exact ho z h1 h2 h3 h4
        · rw [ite_eq_right (by simp [heq])]
          apply wp_skip
          simp only [E0_append]
          wp_step; wp_step
          apply wp_set_eval
          rw [eval_padd hxb2 (ci 1 tint) 1 (by decide) rfl rfl]
          refine ⟨n - 1, by omega, by simp, rfl, a', aa', b' + 1, h', ?_, ?_, ?_, by omega,
            by omega, by omega, by omega, ?_, hu, hk⟩
          · rw [← hR, hstep (a', aa', b' + 1) (by simp [B, bodyL, show ¬ b' ≥ c by omega,
              show ¬ C.Y[a'[b']!]! > v by omega, heq])]
          · rw [temps_gso]; exact hxa2
          · simp
          · intro z h1 h2 h3 h4
            simp only [temps_gso _ _ h2, temps_gso _ _ h4]
            exact ho z h1 h2 h3 h4
      · rw [ite_eq_right (by simp; omega)]
        apply wp_break
        simp only [E0_append]
        have hdone : iterF B n (a', aa', b') = (a', aa', b') := by
          cases n with
          | zero => rfl
          | succ n => simp only [iterF, B, bodyL]; rw [ite_eq_left (by simp; omega)]
        have hfin : iterF (bodyL C.Y v c) fuel (a, aa, b) = (a', aa', b') := hR.symm.trans hdone
        refine hQ _ m' ?_ ?_ ?_ ?_ hu hk
        · rw [hfin]; exact h'
        · rw [hfin, temps_gso]; exact hxa'
        · rw [hfin, temps_gso]; exact hxb'
        · intro z h1 h2 h3 h4; rw [temps_gso _ _ h4]; exact ho z h1 h2 h3 h4
    · rw [ite_eq_right (by simp; omega)]
      wp_step
      wp_step
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      rw [ite_eq_right (by decide)]
      apply wp_break
      simp only [E0_append]
      have hdone : iterF B n (a', aa', b') = (a', aa', b') := by
        cases n with
        | zero => rfl
        | succ n => simp only [iterF, B, bodyL]; rw [ite_eq_left (by simp; omega)]
      have hfin : iterF (bodyL C.Y v c) fuel (a, aa, b) = (a', aa', b') := hR.symm.trans hdone
      refine hQ _ m' ?_ ?_ ?_ ?_ hu hk
      · rw [hfin]; exact h'
      · rw [hfin, temps_gso]; exact hxa'
      · rw [hfin, temps_gso]; exact hxb'
      · intro z h1 h2 h3 h4; rw [temps_gso _ _ h4]; exact ho z h1 h2 h3 h4
  · rintro n t e' le' m' ⟨n', hn', hI⟩
    apply wp_skip
    exact ⟨n', hn', by simpa using hI⟩

/-- The temporaries the right scan writes. -/
def OthR (le le' : temp_env) : Prop :=
  ∀ z, z ≠ id.«xc» → z ≠ id.«xd» → z ≠ id.«tmp1» → z ≠ idOf 712 → PTree.get z le' = PTree.get z le

theorem wp_scanR {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (hC : C.Ok) (h : Arr m C a) {v b c d fuel : Nat}
    (hv : PTree.get id.«v» le = some (.Vint (ir v))) (hvs : v < 2147483648)
    (hxb : PTree.get id.«xb» le = some (.Vptr C.bx (pt C.base b)))
    (hxc : PTree.get id.«xc» le = some (.Vptr C.bx (pt C.base (c - 1))))
    (hxd : PTree.get id.«xd» le = some (.Vptr C.bx (pt C.base (d - 1))))
    (h1 : LowR C a b c v) (hc1 : 1 ≤ c) (hbc : b ≤ c + 1) (hbN : b ≤ C.N) (hcd : c ≤ d) (hdN : d ≤ C.N)
    (hfuel : c - b ≤ fuel)
    (hQ : ∀ le' m', let r := iterF (bodyR C.Y v b) fuel (a, c, d)
      (1 ≤ b ∨ 2 ≤ r.2.1) → Arr m' C r.1 → PTree.get id.«xc» le' = some (.Vptr C.bx (pt C.base (r.2.1 - 1))) →
      PTree.get id.«xd» le' = some (.Vptr C.bx (pt C.base (r.2.2 - 1))) → OthR le le' →
      Unch m m' (· = C.bx) → Alloc.KeepA m m' → Q.normal E0 e le' m') :
    Wp xi ge f scanR Q e le m := by
  let B := bodyR C.Y v b
  let R := iterF B fuel (a, c, d)
  let I := fun (n : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ a' c' d', Arr m' C a' ∧ iterF B n (a', c', d') = R ∧
      PTree.get id.«xc» le' = some (.Vptr C.bx (pt C.base (c' - 1))) ∧
      PTree.get id.«xd» le' = some (.Vptr C.bx (pt C.base (d' - 1))) ∧
      b ≤ c' + 1 ∧ 1 ≤ c' ∧
      (1 ≤ b ∨ ∃ p, 1 ≤ p ∧ b ≤ p ∧ p < c' ∧ C.Y[a'[p]!]! < v) ∧ c' ≤ d' ∧ d' ≤ d ∧ c' - b ≤ n ∧ OthR le le' ∧ Unch m m' (· = C.bx) ∧
      Alloc.KeepA m m'
  refine wp_loop (I := I) (J := fun n t e' le' m' => ∃ n', n' < n ∧ I n' t e' le' m') ?_ ?_
    (n := fuel) ⟨rfl, rfl, a, c, d, h, rfl, hxc, hxd, hbc, hc1, h1, hcd, Nat.le_refl _, hfuel,
      fun _ _ _ _ _ => rfl, Unch.refl _ _, Alloc.KeepA.refl _⟩
  · rintro n t e' le' m' ⟨rfl, rfl, a', c', d', h', hR, hxc', hxd', hbc', hc1', hlow, hcd', hdd, hn,
      ho, hu, hk⟩
    have hfin2 : 1 ≤ b ∨ 2 ≤ c' := by
      rcases hlow with h | ⟨p, hp1, -, hp, -⟩ <;> omega
    have hv' : PTree.get id.«v» le' = some (.Vint (ir v)) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide)]; exact hv
    have hxb' : PTree.get id.«xb» le' = some (.Vptr C.bx (pt C.base b)) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide)]; exact hxb
    have hcmp := (eval_pcmp (ge := ge) (e := e) (m := m') h' hC hxc' hxb' (by omega) (by omega)).2.1
    simp only [scanR, sk]
    wp_step; wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [hcmp]
    simp only [typeof, cop]
    by_cases hlt : b < c'
    · have hcN : c' - 1 < C.N := by omega
      have hks := hC.ysmall _ (h'.bnd (c' - 1) hcN)
      rw [ite_eq_left (by simp; omega)]
      wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, Exec.evalExpr, eval_keyAt hC h' hxc' hcN, eval_tv hv']
      simp only [ints, typeof, cop, key_cmp _ _ hks hvs, cast_of_bool]
      simp only [E0_append]
      wp_step
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      by_cases hle : v ≤ C.Y[a'[c' - 1]!]!
      · rw [ite_eq_left (by simp; omega)]
        apply wp_skip
        simp only [E0_append]
        have hlow' : 1 ≤ b ∨ ∃ p, 1 ≤ p ∧ b ≤ p ∧ p < c' - 1 ∧ C.Y[a'[p]!]! < v := by
          rcases hlow with h | ⟨p, hp1, hbp, hp, hk⟩
          · exact .inl h
          · refine .inr ⟨p, hp1, hbp, ?_, hk⟩
            have : p ≠ c' - 1 := fun e => by rw [e] at hk; omega
            omega
        have hc'1 : 1 ≤ c' - 1 := by rcases hlow' with h | ⟨p, hp1, -, hp, -⟩ <;> omega
        have hxc2 : PTree.get id.«xc» (PTree.set (idOf 712)
            (Val.of_bool (!decide (C.Y[a'[c' - 1]!]! < v))) le') =
            some (.Vptr C.bx (pt C.base (c' - 1))) := by rw [temps_gso]; exact hxc'
        have hxd2 : PTree.get id.«xd» (PTree.set (idOf 712)
            (Val.of_bool (!decide (C.Y[a'[c' - 1]!]! < v))) le') =
            some (.Vptr C.bx (pt C.base (d' - 1))) := by rw [temps_gso]; exact hxd'
        have hv2 : PTree.get id.«v» (PTree.set (idOf 712)
            (Val.of_bool (!decide (C.Y[a'[c' - 1]!]! < v))) le') = some (.Vint (ir v)) := by
          rw [temps_gso]; exact hv'
        wp_step; wp_step; wp_step
        apply wp_if_eval
        rw [Exec.evalExpr, eval_keyAt hC h' hxc2 hcN, eval_tv hv2]
        simp only [ints, typeof, cop, key_eq _ _ hks hvs]
        have hn1 : 1 ≤ n := by omega
        have hstep : ∀ st', B (a', c', d') = .yield st' →
            iterF B n (a', c', d') = iterF B (n - 1) st' := by
          intro st' hb
          obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
          simp only [iterF, hb, Nat.add_sub_cancel]
        have hc1 : c' - 1 = (c' - 2) + 1 := by clear hlow hlow'; omega
        by_cases heq : C.Y[a'[c' - 1]!]! = v
        · rw [ite_eq_left (by simp [heq])]
          refine wp_putV h' hC hxc2 hxd2 hcN (by omega) hv2
            (by rw [← key_self hC h' hcN]; exact heq) _ ?_
          intro m2 h2 hu2 hk2
          rw [swap_comm] at h2
          wp_step; wp_step
          apply wp_set_eval
          have hd1 : d' - 1 = (d' - 2) + 1 := by omega
          rw [eval_psub (k := d' - 2) (ci 1 tint) 1 (by decide)
            (by rw [temps_gso, ← hd1]; exact hxd') rfl rfl]
          simp only [E0_append]
          wp_step; wp_step
          apply wp_set_eval
          rw [eval_psub (k := c' - 2) (ci 1 tint) 1 (by decide)
            (by rw [temps_gso, temps_gso, ← hc1]; exact hxc') rfl rfl]
          refine ⟨n - 1, by omega, by simp, rfl, a'.swapIfInBounds (c' - 1) (d' - 1), c' - 1, d' - 1,
            h2, ?_, ?_, ?_, by omega, by omega, ?_, by omega, by omega, by omega, ?_, hu.trans hu2,
            hk.trans hk2⟩
          · rw [← hR, hstep (a'.swapIfInBounds (c' - 1) (d' - 1), c' - 1, d' - 1)
              (by simp [B, bodyR, show ¬ c' ≤ b by omega, show ¬ C.Y[a'[c' - 1]!]! < v by omega, heq])]
          · rw [temps_gss, show c' - 1 - 1 = c' - 2 by omega]
          · rw [temps_gso, temps_gss, show d' - 1 - 1 = d' - 2 by omega]
          · rcases hlow' with h | ⟨p, hp1, hbp, hp, hk⟩
            · exact .inl h
            · exact .inr ⟨p, hp1, hbp, hp, by rw [swap_get_ne _ (by omega) (by omega)]; exact hk⟩
          · intro z h1 h2 h3 h4
            simp only [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3, temps_gso _ _ h4]
            exact ho z h1 h2 h3 h4
        · rw [ite_eq_right (by simp [heq])]
          apply wp_skip
          simp only [E0_append]
          wp_step; wp_step
          apply wp_set_eval
          rw [eval_psub (k := c' - 2) (ci 1 tint) 1 (by decide) (by rw [← hc1]; exact hxc2) rfl rfl]
          refine ⟨n - 1, by omega, by simp, rfl, a', c' - 1, d', h', ?_, ?_, ?_, by omega,
            by omega, ?_, by omega, by omega, by omega, ?_, hu, hk⟩
          · rw [← hR, hstep (a', c' - 1, d')
              (by simp [B, bodyR, show ¬ c' ≤ b by omega, show ¬ C.Y[a'[c' - 1]!]! < v by omega, heq])]
          · rw [temps_gss, show c' - 1 - 1 = c' - 2 by omega]
          · rw [temps_gso]; exact hxd2
          · exact hlow'
          · intro z h1 h2 h3 h4
            simp only [temps_gso _ _ h1, temps_gso _ _ h4]
            exact ho z h1 h2 h3 h4
      · rw [ite_eq_right (by simp; omega)]
        apply wp_break
        simp only [E0_append]
        have hdone : iterF B n (a', c', d') = (a', c', d') := by
          cases n with
          | zero => rfl
          | succ n => simp only [iterF, B, bodyR]; rw [ite_eq_left (by simp; omega)]
        have hfin : iterF (bodyR C.Y v b) fuel (a, c, d) = (a', c', d') := hR.symm.trans hdone
        refine hQ _ m' ?_ ?_ ?_ ?_ ?_ hu hk
        · rw [hfin]; exact hfin2
        · rw [hfin]; exact h'
        · rw [hfin, temps_gso]; exact hxc'
        · rw [hfin, temps_gso]; exact hxd'
        · intro z h1 h2 h3 h4; rw [temps_gso _ _ h4]; exact ho z h1 h2 h3 h4
    · rw [ite_eq_right (by simp; omega)]
      wp_step
      wp_step
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      rw [ite_eq_right (by decide)]
      apply wp_break
      simp only [E0_append]
      have hdone : iterF B n (a', c', d') = (a', c', d') := by
        cases n with
        | zero => rfl
        | succ n => simp only [iterF, B, bodyR]; rw [ite_eq_left (by simp; omega)]
      have hfin : iterF (bodyR C.Y v b) fuel (a, c, d) = (a', c', d') := hR.symm.trans hdone
      refine hQ _ m' ?_ ?_ ?_ ?_ ?_ hu hk
      · rw [hfin]; exact hfin2
      · rw [hfin]; exact h'
      · rw [hfin, temps_gso]; exact hxc'
      · rw [hfin, temps_gso]; exact hxd'
      · intro z h1 h2 h3 h4; rw [temps_gso _ _ h4]; exact ho z h1 h2 h3 h4
  · rintro n t e' le' m' ⟨n', hn', hI⟩
    apply wp_skip
    exact ⟨n', hn', by simpa using hI⟩

end NautyVerified.Proofs.Sparse.Sort.Ints

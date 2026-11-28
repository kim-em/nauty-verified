import NautyVerified.Proofs.Sparse.Sort.Scan

/-!
# The partition loop

`wp_partLoop`: `for (;;) { scanL; scanR; if (xb > xc) break; SWAP(*xb,*xc); ++xb; --xc; }`
with `xa`, `xb` at elements `aa`, `b` and `xc`, `xd` at `c - 1`, `d - 1` ends
as HexGraphIso's partition passes `iterF (bodyP Y v len)` from
`(a, aa, b, c, d)`: each pass removes at least two elements from `[b, c)`,
so `len + 1` passes suffice for `c - b ≤ len`.
-/

namespace NautyVerified.Proofs.Sparse.Sort

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

/-- The temporaries the partition loop writes. -/
def OthP (le le' : temp_env) : Prop :=
  ∀ z, z ≠ id.«xa» → z ≠ id.«xb» → z ≠ id.«xc» → z ≠ id.«xd» → z ≠ id.«tmp1» → z ≠ idOf 711 →
    z ≠ idOf 712 → PTree.get z le' = PTree.get z le

/-- The cursor state of the partition: the array and `xa`, `xb`, `xc + 1`, `xd + 1`. -/
def Cur (le : temp_env) (C : Ctx) (aa b c d : Nat) : Prop :=
  PTree.get id.«xa» le = some (.Vptr C.bx (pt C.base aa)) ∧
  PTree.get id.«xb» le = some (.Vptr C.bx (pt C.base b)) ∧
  PTree.get id.«xc» le = some (.Vptr C.bx (pt C.base (c - 1))) ∧
  PTree.get id.«xd» le = some (.Vptr C.bx (pt C.base (d - 1)))

theorem wp_partLoop {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (hC : C.Ok) (h : Arr m C a) {v len aa b c d fuel : Nat}
    (hy : PTree.get id.«y» le = some (.Vptr C.bk C.yofs))
    (hv : PTree.get id.«v» le = some (.Vint (ir v))) (hvs : v < 2147483648)
    (hcur : Cur le C aa b c d)
    (h1 : 1 ≤ aa) (hab : aa ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hdN : d ≤ C.N)
    (hlen : c - b ≤ len) (hfuel : c - b ≤ 2 * fuel)
    (hQ : ∀ le' m', let r := iterF (bodyP C.Y v len) fuel (a, aa, b, c, d)
      Arr m' C r.1 → Cur le' C r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 → OthP le le' →
      Unch m m' (· = C.bx) → Alloc.KeepA m m' → Q.normal E0 e le' m') :
    Wp xi ge f partLoop Q e le m := by
  let B := bodyP C.Y v len
  let R := iterF B fuel (a, aa, b, c, d)
  let I := fun (n : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ a' aa' b' c' d', Arr m' C a' ∧ iterF B n (a', aa', b', c', d') = R ∧ Cur le' C aa' b' c' d' ∧
      aa ≤ aa' ∧ aa' ≤ b' ∧ b' ≤ c' + 1 ∧ 1 ≤ c' ∧ c' ≤ d' ∧ b' ≤ d' ∧ d' ≤ d ∧ c' - b' ≤ len ∧
      c' - b' ≤ 2 * n ∧
      OthP le le' ∧ Unch m m' (· = C.bx) ∧ Alloc.KeepA m m'
  refine wp_loop (I := I) (J := fun n t e' le' m' => ∃ n', n' < n ∧ I n' t e' le' m') ?_ ?_
    (n := fuel) ⟨rfl, rfl, a, aa, b, c, d, h, rfl, hcur, Nat.le_refl _, hab, by omega, by omega,
      hcd, by omega, Nat.le_refl _, hlen, hfuel, fun _ _ _ _ _ _ _ _ => rfl, Unch.refl _ _, Alloc.KeepA.refl _⟩
  · rintro n t e' le' m' ⟨rfl, rfl, a', aa', b', c', d', h', hR, ⟨hxa, hxb, hxc, hxd⟩, haa, hab',
      hbc', hc1', hcd', hbd', hdd, hl, hn, ho, hu, hk⟩
    have get_o : ∀ z, z ≠ id.«xa» → z ≠ id.«xb» → z ≠ id.«xc» → z ≠ id.«xd» → z ≠ id.«tmp1» →
        z ≠ idOf 711 → z ≠ idOf 712 → PTree.get z le' = PTree.get z le := ho
    have hy' : PTree.get id.«y» le' = some (.Vptr C.bk C.yofs) := by
      rw [get_o _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hy
    have hv' : PTree.get id.«v» le' = some (.Vint (ir v)) := by
      rw [get_o _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hv
    wp_step; wp_step; wp_step; wp_step; wp_step
    refine wp_scanL hC h' hy' hv' hvs hxa hxb hxc hc1' hab' hbc' (by omega) (by omega) hl ?_
    intro le1 m1
    dsimp only
    intro h1' hxa1 hxb1 ho1 hu1 hk1
    simp only [E0_append]
    have hL := scanL_inv C.Y v c' len a' aa' b' hab' hbc'
    generalize hl1 : iterF (bodyL C.Y v c') len (a', aa', b') = l at *
    obtain ⟨a1, aa1, b1⟩ := l
    simp only at hL h1' hxa1 hxb1
    have hy1 : PTree.get id.«y» le1 = some (.Vptr C.bk C.yofs) := by
      rw [ho1 _ (by decide) (by decide) (by decide) (by decide)]; exact hy'
    have hv1 : PTree.get id.«v» le1 = some (.Vint (ir v)) := by
      rw [ho1 _ (by decide) (by decide) (by decide) (by decide)]; exact hv'
    have hxc1 : PTree.get id.«xc» le1 = some (.Vptr C.bx (pt C.base (c' - 1))) := by
      rw [ho1 _ (by decide) (by decide) (by decide) (by decide)]; exact hxc
    have hxd1 : PTree.get id.«xd» le1 = some (.Vptr C.bx (pt C.base (d' - 1))) := by
      rw [ho1 _ (by decide) (by decide) (by decide) (by decide)]; exact hxd
    wp_step
    refine wp_scanR (fuel := len) hC h1' hy1 hv1 hvs hxb1 hxc1 hxd1 (by omega) hc1' (by omega)
      (by omega) hcd' (by omega) (by omega) ?_
    intro le2 m2
    dsimp only
    intro h2' hxc2 hxd2 ho2 hu2 hk2
    simp only [E0_append]
    have hRi := scanR_inv C.Y v b1 len a1 c' d' (by omega) hcd'
    generalize hr1 : iterF (bodyR C.Y v b1) len (a1, c', d') = r at *
    obtain ⟨a2, c2, d2⟩ := r
    simp only at hRi h2' hxc2 hxd2
    have hxa2 : PTree.get id.«xa» le2 = some (.Vptr C.bx (pt C.base aa1)) := by
      rw [ho2 _ (by decide) (by decide) (by decide) (by decide)]; exact hxa1
    have hxb2 : PTree.get id.«xb» le2 = some (.Vptr C.bx (pt C.base b1)) := by
      rw [ho2 _ (by decide) (by decide) (by decide) (by decide)]; exact hxb1
    have hP : B (a', aa', b', c', d') = if b1 ≥ c2 then .done (a2, aa1, b1, c2, d2)
        else .yield (a2.swapIfInBounds b1 (c2 - 1), aa1, b1 + 1, c2 - 1, d2) := by
      simp only [B, bodyP, hl1, hr1]
    have ho12 : OthP le le2 := by
      intro z q1 q2 q3 q4 q5 q6 q7
      rw [ho2 z q3 q4 q5 q7, ho1 z q1 q2 q5 q6, ho z q1 q2 q3 q4 q5 q6 q7]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [(eval_pcmp (ge := ge) (e := e) (m := m2) h2' hC hxb2 hxc2 (by omega) (by omega)).2.2]
    simp only [typeof, cop]
    by_cases hstop : b1 ≥ c2
    · rw [ite_eq_left (by simp; omega)]
      apply wp_break
      simp only [E0_append]
      have hfin : R = (a2, aa1, b1, c2, d2) := by
        rw [← hR]
        cases n with
        | succ n' => simp only [iterF, hP, hstop, ite_true]
        | zero =>
          have e1 := scanL_stop C.Y v c' a' aa' b' (by omega) len
          rw [hl1] at e1
          cases e1
          have e2 := scanR_stop C.Y v b' a' c' d' (by omega) len
          rw [hr1] at e2
          cases e2
          rfl
      refine hQ le2 m2 ?_ ?_ ho12 (hu.trans (hu1.trans hu2)) (hk.trans (hk1.trans hk2))
      · show Arr m2 C R.1; rw [hfin]; exact h2'
      · show Cur le2 C R.2.1 R.2.2.1 R.2.2.2.1 R.2.2.2.2
        rw [hfin]; exact ⟨hxa2, hxb2, hxc2, hxd2⟩
    · rw [ite_eq_right (by simp; omega)]
      apply wp_skip
      simp only [E0_append]
      refine wp_swapThen h2' hC hxb2 hxc2 (by omega) (by omega) (by decide) (by decide) _ ?_
      intro m3 h3 hu3 hk3
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_padd (by rw [temps_gso]; exact hxb2) (ci 1 tint) 1 (by decide) rfl rfl]
      simp only [E0_append]
      wp_step; wp_step
      apply wp_set_eval
      have hc2 : c2 - 1 = (c2 - 2) + 1 := by omega
      rw [eval_psub (k := c2 - 2) (ci 1 tint) 1 (by decide)
        (by rw [temps_gso, temps_gso, ← hc2]; exact hxc2) rfl rfl]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      refine ⟨n', by omega, by simp, rfl, a2.swapIfInBounds b1 (c2 - 1), aa1, b1 + 1, c2 - 1, d2,
        h3, ?_, ⟨?_, ?_, ?_, ?_⟩, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega, ?_, hu.trans (hu1.trans (hu2.trans hu3)),
        hk.trans (hk1.trans (hk2.trans hk3))⟩
      · rw [← hR]; simp only [iterF, hP, hstop, ite_false]
      · rw [temps_gso, temps_gso, temps_gso]; exact hxa2
      · rw [temps_gso, temps_gss]
      · rw [temps_gss, show c2 - 1 - 1 = c2 - 2 by omega]
      · rw [temps_gso, temps_gso, temps_gso]; exact hxd2
      · intro z q1 q2 q3 q4 q5 q6 q7
        rw [temps_gso _ _ q3, temps_gso _ _ q2, temps_gso _ _ q5]
        exact ho12 z q1 q2 q3 q4 q5 q6 q7
  · rintro n t e' le' m' ⟨n', hn', hI⟩
    apply wp_skip
    exact ⟨n', hn', by simpa using hI⟩

end NautyVerified.Proofs.Sparse.Sort

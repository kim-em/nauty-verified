import NautyVerified.Proofs.Sparse.Sort.Scan
import NautyVerified.Logic.ForFrom

/-!
# The insertion sort for short segments

`wp_shiftLoop`: `for (j = i; y[x0[j-1]] > tmp2; ) { x0[j] = x0[j-1]; if (--j == 0) break; }`
moves the hole as HexGraphIso's `shift`. `wp_insertion`: the loop over
`i = 1 .. nn - 1` leaves `insertion a Y s nn` (`Sort.insertion`, through
`insertion_eq`), for `x0` at element `s`.
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

omit binary64_certificate binary32_certificate in
theorem shift_le (y : Array Nat) (s key : Nat) :
    ∀ (j : Nat) (x : Array Nat), (shift y s key j x).2 ≤ j ∧ (shift y s key j x).1.size = x.size
  | 0, _ => ⟨Nat.le_refl _, rfl⟩
  | j + 1, x => by
    simp only [shift]
    split
    · exact ⟨Nat.le_refl _, rfl⟩
    · have := shift_le y s key j (x.set! (s + j + 1) x[s + j]!)
      simp at this ⊢; omega

theorem wp_shiftLoop {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (hC : C.Ok) (h : Arr m C a) {s key j : Nat}
    (hy : PTree.get id.«y» le = some (.Vptr C.bk C.yofs))
    (hx0 : PTree.get id.«x0» le = some (.Vptr C.bx (pt C.base s)))
    (ht2 : PTree.get id.«tmp2» le = some (.Vint (ir key))) (hks : key < 2147483648)
    (hj : PTree.get id.«j» le = some (.Vint (ir j))) (hj1 : 1 ≤ j) (hsj : s + j < C.N)
    (hQ : ∀ le' m', let r := shift C.Y s key j a
      Arr m' C r.1 → PTree.get id.«j» le' = some (.Vint (ir r.2)) →
      (∀ z, z ≠ id.«j» → z ≠ idOf 703 → PTree.get z le' = PTree.get z le) →
      Unch m m' (· = C.bx) → Alloc.KeepA m m' → Q.normal E0 e le' m') :
    Wp xi ge f shiftLoop Q e le m := by
  let R := shift C.Y s key j a
  let I := fun (n : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ a', Arr m' C a' ∧ 1 ≤ n ∧ n ≤ j ∧ shift C.Y s key n a' = R ∧
      PTree.get id.«j» le' = some (.Vint (ir n)) ∧
      (∀ z, z ≠ id.«j» → z ≠ idOf 703 → PTree.get z le' = PTree.get z le) ∧
      Unch m m' (· = C.bx) ∧ Alloc.KeepA m m'
  have := hC.nN
  refine wp_loop (I := I) (J := fun n t e' le' m' => ∃ n', n' < n ∧ I n' t e' le' m') ?_ ?_
    (n := j) ⟨rfl, rfl, a, h, hj1, Nat.le_refl _, rfl, hj, fun _ _ _ => rfl, Unch.refl _ _,
      Alloc.KeepA.refl _⟩
  · rintro n t e' le' m' ⟨rfl, rfl, a', h', hn1, hnj, hR, hjn, ho, hu, hk⟩
    have hy' : PTree.get id.«y» le' = some (.Vptr C.bk C.yofs) := by
      rw [ho _ (by decide) (by decide)]; exact hy
    have hx0' : PTree.get id.«x0» le' = some (.Vptr C.bx (pt C.base s)) := by
      rw [ho _ (by decide) (by decide)]; exact hx0
    have ht2' : PTree.get id.«tmp2» le' = some (.Vint (ir key)) := by
      rw [ho _ (by decide) (by decide)]; exact ht2
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hjm : Exec.evalExpr ge e le' m' (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) =
        some (.Vint (ir (n' : Int))) := by
      simp only [Exec.evalExpr, hjn, typeof, cop, ir_sub]
      congr 3; push_cast; omega
    have hsn : s + n' < C.N := by omega
    have hks' := hC.ysmall _ (h'.bnd (s + n') hsn)
    simp only [shiftLoop, sk]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, eval_keyIx hC h' hy' hx0' _ n' (by omega) hsn hjm rfl, eval_tv ht2']
    simp only [ints, typeof, cop, key_cmp _ _ hks hks']
    by_cases hgt : key < C.Y[a'[s + n']!]!
    · rw [ite_eq_left (by simpa using hgt)]
      apply wp_skip
      simp only [E0_append]
      wp_step; wp_step; wp_step
      refine wp_store_ix h' hC hx0' (tv id.«j») (n' + 1) (by omega) (by omega)
        (eval_tv hjn) rfl _ a'[s + n']! (h'.bnd _ hsn)
        (eval_elem h' hx0' _ n' (by omega) hsn hjm rfl) rfl ?_
      intro m1 h1 hu1 hk1
      simp only [E0_append]
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hjn, typeof, cop, ir_sub]
      simp only [E0_append]
      wp_step
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp only [E0_append]
      have hval : ir ((n' + 1 : Nat) - 1 : Int) = ir (n' : Int) := by congr 1; push_cast; omega
      have hstep : shift C.Y s key (n' + 1) a' = shift C.Y s key n' (a'.set! (s + n' + 1) a'[s + n']!) := by
        simp only [shift, show ¬ C.Y[a'[s + n']!]! ≤ key by omega, ite_false]
      apply wp_if_eval
      simp only [Exec.evalExpr]
      rw [temps_gso, temps_gss]
      simp only [typeof, cop, hval]
      rw [show s + (n' + 1) = s + n' + 1 by omega] at h1
      by_cases hz : n' = 0
      · subst hz
        rw [ite_eq_left (by decide)]
        apply wp_break
        simp only [E0_append]
        have hfin : R = (a'.set! (s + 0 + 1) a'[s + 0]!, 0) := by rw [← hR, hstep]; rfl
        refine hQ _ m1 ?_ ?_ ?_ (hu.trans hu1) (hk.trans hk1)
        · show Arr m1 C R.1; rw [hfin]; exact h1
        · show _ = some (val.Vint (ir (R.2 : Int))); rw [hfin, temps_gss]
        · intro z h1 h2
          rw [temps_gso _ _ h1, temps_gso _ _ h2]; exact ho z h1 h2
      · rw [ite_eq_right (by
          rw [ir_eq ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]; simpa using hz)]
        apply wp_skip
        simp only [E0_append]
        refine ⟨n', by omega, by simp, rfl, _, h1, by omega, by omega, by rw [← hR, hstep], ?_, ?_,
          hu.trans hu1, hk.trans hk1⟩
        · rw [temps_gss]
        · intro z h1 h2
          rw [temps_gso _ _ h1, temps_gso _ _ h2]; exact ho z h1 h2
    · rw [ite_eq_right (by simpa using hgt)]
      apply wp_break
      simp only [E0_append]
      have hfin : R = (a', n' + 1) := by
        rw [← hR]; simp only [shift, show C.Y[a'[s + n']!]! ≤ key by omega, ite_true]
      refine hQ _ m' ?_ ?_ ho hu hk
      · show Arr m' C R.1; rw [hfin]; exact h'
      · show _ = some (val.Vint (ir (R.2 : Int))); rw [hfin]; exact hjn
  · rintro n t e' le' m' ⟨n', hn', hI⟩
    apply wp_skip
    exact ⟨n', hn', by simpa using hI⟩

/-- The body of the insertion sort's outer loop. -/
abbrev insBody : statement :=
  .Ssequence (sk (.Sset id.«tmp1» (ix id.«x0» (tv id.«i»))))
    (.Ssequence (sk (.Sset id.«tmp2» (ix id.«y» (tv id.«tmp1»))))
      (.Ssequence (.Ssequence (sk (.Sset id.«j» (tv id.«i»))) shiftLoop)
        (sk (.Sassign (ix id.«x0» (tv id.«j»)) (tv id.«tmp1»)))))

/-- The temporaries the insertion sort writes. -/
def OthI (le le' : temp_env) : Prop :=
  ∀ z, z ≠ id.«i» → z ≠ id.«tmp1» → z ≠ id.«tmp2» → z ≠ id.«j» → z ≠ idOf 703 →
    PTree.get z le' = PTree.get z le

theorem wp_insertion {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (hC : C.Ok) (h : Arr m C a) {s nn : Nat}
    (hy : PTree.get id.«y» le = some (.Vptr C.bk C.yofs))
    (hx0 : PTree.get id.«x0» le = some (.Vptr C.bx (pt C.base s)))
    (hnn : PTree.get id.«nn» le = some (.Vint (ir nn))) (hnn1 : 1 ≤ nn) (hsn : s + nn ≤ C.N)
    (hQ : ∀ le' m', Arr m' C (Hex.GraphIso.Nauty.Sparse.Sort.insertion a C.Y s nn) → OthI le le' →
      Unch m m' (· = C.bx) → Alloc.KeepA m m' → Q.normal E0 e le' m') :
    Wp xi ge f (forLoopFrom 1 id.«i» id.«nn» insBody) Q e le m := by
  have hN := hC.nN
  let A := fun k => (List.range' 1 (k - 1)).foldl (insStep C.Y s) a
  refine wp_forLoopFrom id.«i» id.«nn» insBody 1 nn hnn1 (by omega)
    (fun k le' m' => Arr m' C (A k) ∧ PTree.get id.«i» le' = some (.Vint (ir k)) ∧ 1 ≤ k ∧ k ≤ nn ∧
      OthI le le' ∧ Unch m m' (· = C.bx) ∧ Alloc.KeepA m m')
    (fun k le' m' => Arr m' C (A (k + 1)) ∧ PTree.get id.«i» le' = some (.Vint (ir k)) ∧
      1 ≤ k ∧ k < nn ∧ OthI le le' ∧ Unch m m' (· = C.bx) ∧ Alloc.KeepA m m') ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨-, hi, hk1, hkn, ho, -, -⟩
    refine ⟨hk1, hkn, hi, ?_⟩
    rw [ho _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hnn
  · refine ⟨h, temps_gss _ _ _, Nat.le_refl _, hnn1, ?_, Unch.refl _ _, Alloc.KeepA.refl _⟩
    intro z h1 _ _ _ _; rw [temps_gso _ _ h1]
  · rintro k le' m' hk1 hkn ⟨h', hi, -, -, ho, hu, hk⟩
    have hy' : PTree.get id.«y» le' = some (.Vptr C.bk C.yofs) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hy
    have hx0' : PTree.get id.«x0» le' = some (.Vptr C.bx (pt C.base s)) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx0
    have hsk : s + k < C.N := by omega
    simp only [insBody, sk]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_elem h' hx0' _ k (by omega) hsk (eval_tv hi) rfl]
    simp only [E0_append]
    let w := (A k)[s + k]!
    have hw : w < C.Y.size := h'.bnd _ hsk
    have hws := hC.ysmall _ hw
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_key hC h' (by rw [temps_gso]; exact hy') (tv id.«tmp1») w hw (by
      rw [eval_tv (temps_gss _ _ _)]; rfl) rfl]
    simp only [ints, E0_append]
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_tv (by rw [temps_gso, temps_gso]; exact hi)]
    simp only [E0_append]
    refine wp_shiftLoop (j := k) hC h' (by rw [temps_gso, temps_gso, temps_gso]; exact hy')
      (by rw [temps_gso, temps_gso, temps_gso]; exact hx0') (by rw [temps_gso, temps_gss]) hws
      (temps_gss _ _ _) hk1 hsk ?_
    intro le2 m2
    dsimp only
    intro h2 hj2 ho2 hu2 hk2
    simp only [E0_append]
    have hsh := shift_le C.Y s C.Y[w]! k (A k)
    wp_step; wp_step
    have hx02 : PTree.get id.«x0» le2 = some (.Vptr C.bx (pt C.base s)) := by
      rw [ho2 _ (by decide) (by decide), temps_gso, temps_gso, temps_gso]; exact hx0'
    have ht12 : PTree.get id.«tmp1» le2 = some (.Vint (ir w)) := by
      rw [ho2 _ (by decide) (by decide), temps_gso, temps_gso, temps_gss]
    refine wp_store_ix h2 hC hx02 (tv id.«j») _ (by omega) (by omega) (eval_tv hj2) rfl
      (tv id.«tmp1») w hw (eval_tv ht12) rfl ?_
    intro m3 h3 hu3 hk3
    refine ⟨rfl, ?_, ?_, hk1, hkn, ?_, hu.trans (hu2.trans hu3), hk.trans (hk2.trans hk3)⟩
    · have : A (k + 1) = insStep C.Y s (A k) k := by
        show (List.range' 1 (k + 1 - 1)).foldl _ _ = _
        rw [show k + 1 - 1 = (k - 1) + 1 by omega, List.range'_concat, List.foldl_append,
          show 1 + 1 * (k - 1) = k by omega]
        rfl
      rw [this]; exact h3
    · rw [ho2 _ (by decide) (by decide), temps_gso, temps_gso, temps_gso]; exact hi
    · intro z q1 q2 q3 q4 q5
      rw [ho2 _ q4 q5, temps_gso _ _ q4, temps_gso _ _ q3, temps_gso _ _ q2]
      exact ho z q1 q2 q3 q4 q5
  · rintro k le' m' ⟨h', hi, hk1, hkn, ho, hu, hk⟩
    refine ⟨hi, h', temps_gss _ _ _, by omega, by omega, ?_, hu, hk⟩
    intro z q1 q2 q3 q4 q5
    rw [temps_gso _ _ q1]; exact ho z q1 q2 q3 q4 q5
  · rintro le' m' ⟨h', -, -, -, ho, hu, hk⟩
    refine hQ le' m' ?_ ho hu hk
    rw [insertion_eq]; exact h'

end NautyVerified.Proofs.Sparse.Sort

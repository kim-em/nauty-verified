import NautyVerified.Proofs.Sparse.Sort.Part

/-!
# After the partition loop

`wp_swapLoop`: `for (; s > 0; --s) { SWAP(*xl, *xh); ++xl; ++xh; }` is
HexGraphIso's `swapRun`. `wp_finish`: the code between the partition loop and
the pushes (`a`, `ba`, the left block swap, `d`, `dc`, the right block swap)
leaves `partFinish` of the scans' final state, with `ba` and `dc` the sizes
of the two fragments still to sort.
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
theorem swapRun_succ (p q k : Nat) (x : Array Nat) :
    swapRun p q (k + 1) x = (swapRun p q k x).swapIfInBounds (p + k) (q + k) := by
  simp only [swapRun, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Nat.zero_add, Nat.one_mul]

/-- The temporaries a block swap writes. -/
def OthS (le le' : temp_env) : Prop :=
  ∀ z, z ≠ id.«xl» → z ≠ id.«xh» → z ≠ id.«s» → z ≠ id.«tmp1» → PTree.get z le' = PTree.get z le

theorem wp_swapLoop {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (hC : C.Ok) (h : Arr m C a) {p q k : Nat}
    (hxl : PTree.get id.«xl» le = some (.Vptr C.bx (pt C.base p)))
    (hxh : PTree.get id.«xh» le = some (.Vptr C.bx (pt C.base q)))
    (hs : PTree.get id.«s» le = some (.Vint (ir k))) (hp : p + k ≤ C.N) (hq : q + k ≤ C.N)
    (hQ : ∀ le' m', Arr m' C (swapRun p q k a) → OthS le le' → Unch m m' (· = C.bx) →
      Alloc.KeepA m m' → Q.normal E0 e le' m') :
    Wp xi ge f swapLoop Q e le m := by
  have := hC.nN
  let I := fun (n : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ i, i + n = k ∧ Arr m' C (swapRun p q i a) ∧
      PTree.get id.«xl» le' = some (.Vptr C.bx (pt C.base (p + i))) ∧
      PTree.get id.«xh» le' = some (.Vptr C.bx (pt C.base (q + i))) ∧
      PTree.get id.«s» le' = some (.Vint (ir n)) ∧ OthS le le' ∧ Unch m m' (· = C.bx) ∧
      Alloc.KeepA m m'
  let J := fun (n : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ i, i + n = k ∧ 0 < n ∧ Arr m' C (swapRun p q (i + 1) a) ∧
      PTree.get id.«xl» le' = some (.Vptr C.bx (pt C.base (p + (i + 1)))) ∧
      PTree.get id.«xh» le' = some (.Vptr C.bx (pt C.base (q + (i + 1)))) ∧
      PTree.get id.«s» le' = some (.Vint (ir n)) ∧ OthS le le' ∧ Unch m m' (· = C.bx) ∧
      Alloc.KeepA m m'
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := k)
    ⟨rfl, rfl, 0, by omega, h, hxl, hxh, hs, fun _ _ _ _ _ => rfl, Unch.refl _ _,
      Alloc.KeepA.refl _⟩
  · rintro n t e' le' m' ⟨rfl, rfl, i, hin, h', hl, hh, hsn, ho, hu, hk⟩
    simp only [swapLoop, sk]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hsn, typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 0) = ir ((0 : Nat) : Int) from rfl,
      key_cmp 0 n (by decide) (by omega)]
    by_cases hn : 0 < n
    · rw [ite_eq_left (by simpa using hn)]
      apply wp_skip
      simp only [E0_append]
      refine wp_swapThen h' hC hl hh (by omega) (by omega) (by decide) (by decide) _ ?_
      intro m1 h1 hu1 hk1
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_padd (by rw [temps_gso]; exact hl) (ci 1 tint) 1 (by decide) rfl rfl]
      simp only [E0_append]
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_padd (by rw [temps_gso, temps_gso]; exact hh) (ci 1 tint) 1 (by decide) rfl rfl]
      refine ⟨by simp, rfl, i, hin, hn, ?_, ?_, ?_, ?_, ?_, hu.trans hu1, hk.trans hk1⟩
      · rw [swapRun_succ]; exact h1
      · rw [temps_gso, temps_gss, Nat.add_assoc]
      · rw [temps_gss, Nat.add_assoc]
      · rw [temps_gso, temps_gso, temps_gso]; exact hsn
      · intro z q1 q2 q3 q4
        rw [temps_gso _ _ q2, temps_gso _ _ q1, temps_gso _ _ q4]; exact ho z q1 q2 q3 q4
    · rw [ite_eq_right (by simpa using hn)]
      apply wp_break
      simp only [E0_append]
      have : i = k := by omega
      subst this
      exact hQ le' m' h' ho hu hk
  · rintro n t e' le' m' ⟨rfl, rfl, i, hin, hn, h', hl, hh, hsn, ho, hu, hk⟩
    simp only [sk]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hsn, typeof, cop, ir_sub]
    refine ⟨n - 1, by omega, by simp, rfl, i + 1, by omega, h', by rw [temps_gso]; exact hl,
      by rw [temps_gso]; exact hh, ?_, ?_, hu, hk⟩
    · rw [temps_gss]; congr 3; omega
    · intro z q1 q2 q3 q4
      rw [temps_gso _ _ q3]; exact ho z q1 q2 q3 q4

/-- The code from the partition loop to the pushes, then `rest`. -/
abbrev finish (rest : statement) : statement :=
  .Ssequence (sk (.Sset id.«a» (.Ecast (.Ebinop .Osub (pv id.«xa») (pv id.«x0») tlong) tint)))
    (.Ssequence (sk (.Sset id.«ba» (.Ecast (.Ebinop .Osub (pv id.«xb») (pv id.«xa») tlong) tint)))
      (.Ssequence (sk (.Sifthenelse (.Ebinop .Ogt (tv id.«ba») (tv id.«a») tint)
          (sk (.Sset id.«s» (tv id.«a»))) (sk (.Sset id.«s» (tv id.«ba»)))))
        (.Ssequence (.Ssequence (.Ssequence (sk (.Sset id.«xl» (pv id.«x0»)))
            (.Sset id.«xh» (.Ebinop .Osub (pv id.«xb») (tv id.«s») (tptr tint)))) swapLoop)
          (.Ssequence (sk (.Sset id.«d» (.Ecast (.Ebinop .Osub (pv id.«xd») (pv id.«x0») tlong) tint)))
            (.Ssequence
              (sk (.Sset id.«dc» (.Ecast (.Ebinop .Osub (pv id.«xd») (pv id.«xc») tlong) tint)))
              (.Ssequence
                (sk (.Sifthenelse (.Ebinop .Ogt (tv id.«dc»)
                    (.Ebinop .Osub (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint) (tv id.«d») tint) tint)
                  (sk (.Sset id.«s»
                    (.Ebinop .Osub (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint) (tv id.«d») tint)))
                  (sk (.Sset id.«s» (tv id.«dc»)))))
                (.Ssequence (.Ssequence (.Ssequence (sk (.Sset id.«xl» (pv id.«xb»)))
                    (.Sset id.«xh» (.Ebinop .Oadd (pv id.«x0») (.Ebinop .Osub (tv id.«nn») (tv id.«s») tint)
                      (tptr tint)))) swapLoop)
                  rest)))))))

/-- The temporaries `finish` writes. -/
def OthF (le le' : temp_env) : Prop :=
  ∀ z, z ≠ id.«a» → z ≠ id.«ba» → z ≠ id.«s» → z ≠ id.«xl» → z ≠ id.«xh» → z ≠ id.«d» →
    z ≠ id.«dc» → z ≠ id.«tmp1» → PTree.get z le' = PTree.get z le

theorem wp_finish {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {a : Array Nat}
    (hC : C.Ok) (h : Arr m C a) {s0 nn aa b c d : Nat} (rest : statement)
    (hx0 : PTree.get id.«x0» le = some (.Vptr C.bx (pt C.base s0)))
    (hnn : PTree.get id.«nn» le = some (.Vint (ir nn))) (hcur : Cur le C aa b c d)
    (hs0 : s0 ≤ aa) (hab : aa ≤ b) (hbc : b ≤ c + 1) (hsc : s0 ≤ c) (hc1 : 1 ≤ c) (hcd : c ≤ d)
    (hbd : b ≤ d) (hdn : d ≤ s0 + nn) (hN : s0 + nn ≤ C.N)
    (hQ : ∀ le' m', let r := partFinish s0 nn (a, aa, b, c, d)
      Arr m' C r.1 → PTree.get id.«ba» le' = some (.Vint (ir r.2.1)) →
      PTree.get id.«dc» le' = some (.Vint (ir r.2.2)) → OthF le le' → Unch m m' (· = C.bx) →
      Alloc.KeepA m m' → Wp xi ge f rest Q e le' m') :
    Wp xi ge f (finish rest) Q e le m := by
  have hNN := hC.nN
  obtain ⟨hxa, hxb, hxc, hxd⟩ := hcur
  let left := min (aa - s0) (b - aa)
  let right := min (d - c) (s0 + nn - d)
  simp only [finish, sk]
  -- a = xa - x0, ba = xb - xa
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_pdiff hC hxa hx0 (by omega) (by omega), show (aa : Int) - s0 = ((aa - s0 : Nat) : Int) by
    omega]
  simp only [E0_append]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_pdiff hC (by rw [temps_gso]; exact hxb) (by rw [temps_gso]; exact hxa) (by omega) (by omega),
    show (b : Int) - aa = ((b - aa : Nat) : Int) by omega]
  simp only [E0_append]
  -- s = min (a, ba)
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr]
  rw [temps_gss, temps_gso, temps_gss]
  simp only [typeof, cop]
  rw [key_cmp (aa - s0) (b - aa) (by omega) (by omega)]
  -- the left block swap, then the rest, from the value of `s`
  have after1 : ∀ le1, PTree.get id.«s» le1 = some (.Vint (ir left)) →
      (∀ z, z ≠ id.«s» → PTree.get z le1 = PTree.get z
        (PTree.set id.«ba» (.Vint (ir ((b - aa : Nat) : Int)))
          (PTree.set id.«a» (.Vint (ir ((aa - s0 : Nat) : Int))) le))) →
      Wp xi ge f (.Ssequence (.Ssequence (.Ssequence (sk (.Sset id.«xl» (pv id.«x0»)))
            (.Sset id.«xh» (.Ebinop .Osub (pv id.«xb») (tv id.«s») (tptr tint)))) swapLoop)
          (.Ssequence (sk (.Sset id.«d» (.Ecast (.Ebinop .Osub (pv id.«xd») (pv id.«x0») tlong) tint)))
            (.Ssequence
              (sk (.Sset id.«dc» (.Ecast (.Ebinop .Osub (pv id.«xd») (pv id.«xc») tlong) tint)))
              (.Ssequence
                (sk (.Sifthenelse (.Ebinop .Ogt (tv id.«dc»)
                    (.Ebinop .Osub (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint) (tv id.«d») tint) tint)
                  (sk (.Sset id.«s»
                    (.Ebinop .Osub (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint) (tv id.«d») tint)))
                  (sk (.Sset id.«s» (tv id.«dc»)))))
                (.Ssequence (.Ssequence (.Ssequence (sk (.Sset id.«xl» (pv id.«xb»)))
                    (.Sset id.«xh» (.Ebinop .Oadd (pv id.«x0») (.Ebinop .Osub (tv id.«nn») (tv id.«s») tint)
                      (tptr tint)))) swapLoop)
                  rest))))) Q e le1 m := by
    intro le1 hs1 ho1
    have g : ∀ z, z ≠ id.«s» → z ≠ id.«ba» → z ≠ id.«a» → PTree.get z le1 = PTree.get z le :=
      fun z q1 q2 q3 => by rw [ho1 z q1, temps_gso _ _ q2, temps_gso _ _ q3]
    have hx01 : PTree.get id.«x0» le1 = some (.Vptr C.bx (pt C.base s0)) := by
      rw [g _ (by decide) (by decide) (by decide)]; exact hx0
    have hxb1 : PTree.get id.«xb» le1 = some (.Vptr C.bx (pt C.base b)) := by
      rw [g _ (by decide) (by decide) (by decide)]; exact hxb
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_pv hx01]
    simp only [E0_append]
    apply wp_set_eval
    rw [eval_psub (k := b - left) _ left (by omega)
      (by rw [temps_gso, show b - left + left = b by omega]; exact hxb1)
      (by rw [eval_tv (by rw [temps_gso]; exact hs1)]) rfl]
    refine wp_swapLoop hC h (by rw [temps_gso, temps_gss]) (temps_gss _ _ _)
      (by rw [temps_gso, temps_gso]; exact hs1) (p := s0) (q := b - left) (k := left)
      (by omega) (by omega) ?_
    intro le2 m2 h2 ho2 hu2 hk2
    simp only [E0_append]
    have g2 : ∀ z, z ≠ id.«xl» → z ≠ id.«xh» → z ≠ id.«s» → z ≠ id.«tmp1» → z ≠ id.«ba» →
        z ≠ id.«a» → PTree.get z le2 = PTree.get z le := fun z q1 q2 q3 q4 q5 q6 => by
      rw [ho2 z q1 q2 q3 q4, temps_gso _ _ q2, temps_gso _ _ q1, g z q3 q5 q6]
    have hx02 : PTree.get id.«x0» le2 = some (.Vptr C.bx (pt C.base s0)) := by
      rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx0
    have hxb2 : PTree.get id.«xb» le2 = some (.Vptr C.bx (pt C.base b)) := by
      rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hxb
    have hxc2 : PTree.get id.«xc» le2 = some (.Vptr C.bx (pt C.base (c - 1))) := by
      rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hxc
    have hxd2 : PTree.get id.«xd» le2 = some (.Vptr C.bx (pt C.base (d - 1))) := by
      rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hxd
    have hnn2 : PTree.get id.«nn» le2 = some (.Vint (ir nn)) := by
      rw [g2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hnn
    have hba2 : PTree.get id.«ba» le2 = some (.Vint (ir ((b - aa : Nat) : Int))) := by
      rw [ho2 _ (by decide) (by decide) (by decide) (by decide), temps_gso, temps_gso, ho1 _ (by decide),
        temps_gss]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_pdiff hC hxd2 hx02 (by omega) (by omega)]
    simp only [E0_append]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_pdiff hC (by rw [temps_gso]; exact hxd2) (by rw [temps_gso]; exact hxc2) (by omega)
      (by omega), show ((d - 1 : Nat) : Int) - ((c - 1 : Nat) : Int) = ((d - c : Nat) : Int) by omega]
    simp only [E0_append]
    let le3 := PTree.set id.«dc» (.Vint (ir ((d - c : Nat) : Int)))
      (PTree.set id.«d» (.Vint (ir (((d - 1 : Nat) : Int) - s0))) le2)
    have hR : Exec.evalExpr ge e le3 m2
        (.Ebinop .Osub (.Ebinop .Osub (tv id.«nn») (ci 1 tint) tint) (tv id.«d») tint) =
        some (.Vint (ir ((s0 + nn - d : Nat) : Int))) := by
      simp only [Exec.evalExpr, le3]
      rw [temps_gso, temps_gso, hnn2, temps_gso, temps_gss]
      simp only [typeof, cop, ir_sub]
      congr 3; omega
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hR, eval_tv (temps_gss _ _ _)]
    simp only [typeof, cop]
    rw [key_cmp (s0 + nn - d) (d - c) (by omega) (by omega)]
    have after2 : ∀ le4, PTree.get id.«s» le4 = some (.Vint (ir right)) →
        (∀ z, z ≠ id.«s» → PTree.get z le4 = PTree.get z le3) →
        Wp xi ge f (.Ssequence (.Ssequence (.Ssequence (sk (.Sset id.«xl» (pv id.«xb»)))
            (.Sset id.«xh» (.Ebinop .Oadd (pv id.«x0») (.Ebinop .Osub (tv id.«nn») (tv id.«s») tint)
              (tptr tint)))) swapLoop) rest) Q e le4 m2 := by
      intro le4 hs4 ho4
      have g4 : ∀ z, z ≠ id.«s» → z ≠ id.«dc» → z ≠ id.«d» → PTree.get z le4 = PTree.get z le2 :=
        fun z q1 q2 q3 => by rw [ho4 z q1, temps_gso _ _ q2, temps_gso _ _ q3]
      have hxb4 : PTree.get id.«xb» le4 = some (.Vptr C.bx (pt C.base b)) := by
        rw [g4 _ (by decide) (by decide) (by decide)]; exact hxb2
      have hx04 : PTree.get id.«x0» le4 = some (.Vptr C.bx (pt C.base s0)) := by
        rw [g4 _ (by decide) (by decide) (by decide)]; exact hx02
      have hnn4 : PTree.get id.«nn» le4 = some (.Vint (ir nn)) := by
        rw [g4 _ (by decide) (by decide) (by decide)]; exact hnn2
      wp_step; wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_pv hxb4]
      simp only [E0_append]
      apply wp_set_eval
      have hdiff : Exec.evalExpr ge e (PTree.set id.«xl» (.Vptr C.bx (pt C.base b)) le4) m2
          (.Ebinop .Osub (tv id.«nn») (tv id.«s») tint) = some (.Vint (ir ((nn - right : Nat) : Int))) := by
        simp only [Exec.evalExpr]
        rw [temps_gso, hnn4, temps_gso, hs4]
        simp only [typeof, cop, ir_sub]
        congr 3; omega
      rw [eval_padd (by rw [temps_gso]; exact hx04) _ (nn - right) (by omega) hdiff rfl]
      simp only [E0_append]
      refine wp_swapLoop hC h2 (by rw [temps_gso, temps_gss]) (temps_gss _ _ _)
        (by rw [temps_gso, temps_gso]; exact hs4) (p := b) (q := s0 + (nn - right)) (k := right)
        (by omega) (by omega) ?_
      intro le5 m5 h5 ho5 hu5 hk5
      simp only [E0_append]
      have g5 : ∀ z, z ≠ id.«xl» → z ≠ id.«xh» → z ≠ id.«s» → z ≠ id.«tmp1» → z ≠ id.«dc» →
          z ≠ id.«d» → PTree.get z le5 = PTree.get z le2 := fun z q1 q2 q3 q4 q5 q6 => by
        rw [ho5 z q1 q2 q3 q4, temps_gso _ _ q2, temps_gso _ _ q1, g4 z q3 q5 q6]
      refine hQ le5 m5 ?_ ?_ ?_ ?_ (hu2.trans hu5) (hk2.trans hk5)
      · show Arr m5 C (partFinish s0 nn (a, aa, b, c, d)).1
        simp only [partFinish]
        rw [show s0 + nn - right = s0 + (nn - right) by omega]
        exact h5
      · rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hba2
      · rw [ho5 _ (by decide) (by decide) (by decide) (by decide), temps_gso, temps_gso,
          ho4 _ (by decide), temps_gss]
        rfl
      · intro z q1 q2 q3 q4 q5 q6 q7 q8
        rw [g5 z q4 q5 q3 q8 q7 q6, g2 z q4 q5 q3 q8 q2 q1]
    have hbase3 : ∀ v, ∀ z, z ≠ id.«s» → PTree.get z (PTree.set id.«s» v le3) = PTree.get z le3 :=
      fun v z hz => temps_gso _ _ hz
    by_cases hlt3 : s0 + nn - d < d - c
    · rw [ite_eq_left (by simpa using hlt3)]
      wp_step; wp_step
      apply wp_set_eval
      rw [hR]
      simp only [E0_append]
      exact after2 _ (by rw [temps_gss]; congr 3; omega) (hbase3 _)
    · rw [ite_eq_right (by simpa using hlt3)]
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_tv (temps_gss _ _ _)]
      simp only [E0_append]
      exact after2 _ (by rw [temps_gss]; congr 3; omega) (hbase3 _)
  have hbase : ∀ v, ∀ z, z ≠ id.«s» → PTree.get z (PTree.set id.«s» v
      (PTree.set id.«ba» (.Vint (ir ((b - aa : Nat) : Int)))
        (PTree.set id.«a» (.Vint (ir ((aa - s0 : Nat) : Int))) le))) = PTree.get z
      (PTree.set id.«ba» (.Vint (ir ((b - aa : Nat) : Int)))
        (PTree.set id.«a» (.Vint (ir ((aa - s0 : Nat) : Int))) le)) :=
    fun v z hz => temps_gso _ _ hz
  by_cases hlt : aa - s0 < b - aa
  · rw [ite_eq_left (by simpa using hlt)]
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_tv (by rw [temps_gso]; exact temps_gss _ _ _)]
    simp only [E0_append]
    exact after1 _ (by rw [temps_gss]; congr 3; omega) (hbase _)
  · rw [ite_eq_right (by simpa using hlt)]
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_tv (temps_gss _ _ _)]
    simp only [E0_append]
    exact after1 _ (by rw [temps_gss]; congr 3; omega) (hbase _)

end NautyVerified.Proofs.Sparse.Sort

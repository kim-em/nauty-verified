import NautyVerified.Proofs.Sparse.Bestcell.Joins
import NautyVerified.Proofs.Sparse.Sort.Pivot
import NautyVerified.Spec.Processnode

/-!
# `bestcell_sg` meets its specification

`bestcell_satisfies`: nausparse.c's `bestcell_sg` meets `bestcellSpec`. The
four `DYNALLOC1`s (`wp_dynW`), `work1b = work1 + n/2`, the cell scan
(`wp_cellLoop`), `if (nnt == 0) return n;`, the zero loop (`wp_zero`), the
counts (`wp_joins`) and the final loop (`wp_argLoop`, HexGraphIso's `choose`
through `choose_arg`), then `return START[j]` with `size_t j`. The scan keeps
at most `n/2` cells (`Good.half`), so `START` and `SIZE` stay apart inside
`work1`.
-/

namespace NautyVerified.Proofs.Sparse.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse NautyVerified.Program
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat cast_l_i)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

/-- The final loop's state after cells `1 .. q-1`. -/
def argAt (cnt : Nat → Nat) (q : Nat) : Nat × Nat :=
  (List.range' 1 (q - 1)).foldl (argStep cnt) (0, cnt 0)

theorem argAt_succ (cnt : Nat → Nat) {q : Nat} (hq : 1 ≤ q) :
    argAt cnt (q + 1) = argStep cnt (argAt cnt q) q := by
  simp only [argAt]
  rw [show q + 1 - 1 = (q - 1) + 1 by omega, List.range'_1_concat, List.foldl_append, List.foldl_cons,
    List.foldl_nil, show 1 + (q - 1) = q by omega]

theorem argAt_spec (cnt : Nat → Nat) : ∀ q, 1 ≤ q → (argAt cnt q).1 < q ∧
    (argAt cnt q).2 = cnt (argAt cnt q).1
  | 0, h => absurd h (by omega)
  | 1, _ => ⟨by simp [argAt], by simp [argAt]⟩
  | q + 2, _ => by
    rw [argAt_succ cnt (by omega)]
    obtain ⟨h1, h2⟩ := argAt_spec cnt (q + 1) (by omega)
    simp only [argStep]
    split
    · exact ⟨by omega, rfl⟩
    · exact ⟨by omega, h2⟩

/-- `for (i = 1; i < nnt; ++i) if (COUNT[i] > maxcnt) { j = i; maxcnt = COUNT[i]; }` -/
theorem wp_argLoop {Q : Logic.Post} {m : mem} {le : temp_env} {W4 : Nat → val} {bw : block}
    {cnt : Nat → Nat} {K n : Nat}
    (hw : Mem.load .Mint64 m (wp 3) (zOfInt 0) = some (.Vptr bw Ptrofs.zero))
    (hw4 : ArrayAt m .Mint32 bw 0 W4 n) (hn : n < 2147483648)
    (hW4 : ∀ k < K, W4 k = .Vint (ir (cnt k : Int))) (hc : ∀ k < K, cnt k ≤ n)
    (hK1 : 1 ≤ K) (hKn : K ≤ n) (hnnt : PTree.get id.nnt le = some (.Vint (ir K)))
    (hj : PTree.get id.j le = some (.Vlong (lr 0)))
    (hmx : PTree.get id.maxcnt le = some (.Vint (ir (cnt 0 : Int))))
    (hQ : ∀ le', PTree.get id.j le' = some (.Vlong (lr ((argAt cnt K).1 : Int))) →
      (∀ x, x ≠ id.i → x ≠ id.j → x ≠ id.maxcnt → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m) :
    Wp xi sge F argLoop Q empty_env le m := by
  let At := fun (q r : Nat) (le' : temp_env) =>
    PTree.get id.i le' = some (.Vint (ir q)) ∧
    PTree.get id.j le' = some (.Vlong (lr ((argAt cnt r).1 : Int))) ∧
    PTree.get id.maxcnt le' = some (.Vint (ir ((argAt cnt r).2 : Int))) ∧
    ∀ x, x ≠ id.i → x ≠ id.j → x ≠ id.maxcnt → PTree.get x le' = PTree.get x le
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  refine wp_loop (I := fun v t e' le' m' => t = E0 ∧ e' = empty_env ∧ m' = m ∧ ∃ q, 1 ≤ q ∧ q ≤ K ∧
      v = K - q ∧ At q q le')
    (J := fun v t e' le' m' => t = E0 ∧ e' = empty_env ∧ m' = m ∧ ∃ q, 1 ≤ q ∧ q < K ∧
      v = K - q ∧ At q (q + 1) le') ?_ ?_ (n := K - 1)
    ⟨rfl, rfl, rfl, 1, Nat.le_refl _, hK1, rfl, temps_gss _ _ _,
      by rw [temps_gso _ _ (by decide)]; exact hj, by rw [temps_gso _ _ (by decide)]; exact hmx,
      fun x a _ _ => temps_gso _ _ a⟩
  · rintro v t e' le' m' ⟨rfl, rfl, hm, q, hq1, hqK, rfl, hi, hjq, hmq, ho⟩
    subst m'
    have hnnt' : PTree.get id.nnt le' = some (.Vint (ir K)) := by
      rw [ho _ (by decide) (by decide) (by decide)]; exact hnnt
    obtain ⟨hs1, hs2⟩ := argAt_spec cnt q hq1
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hi, hnnt', typeof, cop]
    rw [ir_lt (a := (q : Int)) (b := (K : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hqk : q < K
    · rw [ite_eq_left (by simpa using hqk)]
      apply wp_skip
      have hv := eval_idx (pe := .Evar id.work4 (tptr tint)) (ofs := Ptrofs.zero) (e := empty_env)
        (le := le') hw4 hn (eval_gvar (k := 3) find_work4 hw) rfl rfl rfl (tv id.i) q (by omega) hi rfl
      rw [hW4 q hqk] at hv
      have hcq := hc q hqk
      have hcb := hc _ (show (argAt cnt q).1 < K by omega)
      rw [← hs2] at hcb
      wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hv, show Exec.evalExpr sge empty_env le' m (tv id.maxcnt) = _ from hmq]
      simp only [typeof, cop]
      rw [ir_lt (a := ((argAt cnt q).2 : Int)) (b := (cnt q : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
      have hS := argAt_succ cnt hq1
      by_cases hgt : (argAt cnt q).2 < cnt q
      · rw [ite_eq_left (by simpa using hgt)]
        have hS' : argAt cnt (q + 1) = (q, cnt q) := by rw [hS]; simp only [argStep]; rw [ite_eq_left hgt]
        wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, hi, typeof, cop]
        rw [cast_int_long_ir (a := (q : Int)) ⟨by omega, by omega⟩]
        wp_step; wp_step
        apply wp_set_eval
        rw [eval_idx (pe := .Evar id.work4 (tptr tint)) (ofs := Ptrofs.zero) (e := empty_env)
          hw4 hn (eval_gvar (k := 3) find_work4 hw) rfl rfl rfl (tv id.i) q (by omega)
          (by simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide)]; exact hi) rfl, hW4 q hqk]
        refine ⟨by simp, rfl, rfl, q, hq1, hqk, rfl, ?_, ?_, ?_, fun x a b c => ?_⟩
        · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hi
        · rw [temps_gso _ _ (by decide), temps_gss, hS']
        · rw [temps_gss, hS']
        · rw [temps_gso _ _ c, temps_gso _ _ b, ho x a b c]
      · rw [ite_eq_right (by simpa using hgt)]
        have hS' : argAt cnt (q + 1) = argAt cnt q := by rw [hS]; simp only [argStep]; rw [ite_eq_right hgt]
        apply wp_skip
        exact ⟨by simp, rfl, rfl, q, hq1, hqk, rfl, hi, by rw [hS']; exact hjq, by rw [hS']; exact hmq, ho⟩
    · rw [ite_eq_right (by simpa using hqk)]
      apply wp_break
      have : q = K := by omega
      subst this
      exact hQ le' hjq ho
  · rintro v t e' le' m' ⟨rfl, rfl, hm, q, hq1, hqK, rfl, hi, hjq, hmq, ho⟩
    subst m'
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hi, typeof, cop, ir_add]
    refine ⟨K - (q + 1), by omega, by simp, by simp, by simp, q + 1, by omega, by omega, rfl, ?_,
      by rw [temps_gso _ _ (by decide)]; exact hjq, by rw [temps_gso _ _ (by decide)]; exact hmq,
      fun x a b c => by rw [temps_gso _ _ a, ho x a b c]⟩
    rw [temps_gss]; push_cast; rfl

def entryTemps (bsg : block) (sofs : ptrofs) (bl : block) (lofs : ptrofs) (bp : block)
    (pofs : ptrofs) (level tcLevel M n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set sparse.id.m (.Vint (ir M))
    (PTree.set sparse.id.tc_level (.Vint (ir tcLevel)) (PTree.set id.level (.Vint (ir level))
      (PTree.set id.ptn (.Vptr bp pofs) (PTree.set id.lab (.Vptr bl lofs)
        (PTree.set id.g (.Vptr bsg sofs) (create_undef_temps F.fn_temps)))))))

theorem fset_cases {α : Type} (f : Fin 4 → α) (x0 x1 x2 x3 : α) :
    fset (fset (fset (fset f 0 x0) 1 x1) 2 x2) 3 x3 0 = x0 ∧
    fset (fset (fset (fset f 0 x0) 1 x1) 2 x2) 3 x3 1 = x1 ∧
    fset (fset (fset (fset f 0 x0) 1 x1) 2 x2) 3 x3 2 = x2 ∧
    fset (fset (fset (fset f 0 x0) 1 x1) 2 x2) 3 x3 3 = x3 := by
  simp [fset]

theorem fin4_all {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ k, P k
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

theorem bestcell_satisfies {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs)
    (bv : block) (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (bl : block)
    (lofs : ptrofs) (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat)
    (level tcLevel M : Nat) (c : Fin 4 → Nat) (b : Fin 4 → block) :
    Satisfies xi sge (.Internal F)
      (bestcellSpec G bsg sofs bv vo bd dofs be eo bl lofs lab bp pofs ptn level tcLevel M c b) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bsg sofs bl lofs bp pofs level tcLevel M n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bsg sofs bl lofs bp pofs level tcLevel M n, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hpre⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [sparse.fn.«nausparse:bestcell_sg».fn_body_eq, body_eq]
    simp only [body]
    have hn0 := hpre.n0
    have hnlt := hpre.nlt
    let E := entryTemps bsg sofs bl lofs bp pofs level tcLevel M n
    wp_step
    refine Testcanlab.wp_vde (p := id.g) (by simp (config := {decide := true}) only [E, entryTemps,
      temps_gso, temps_gss]) (by decide) (by decide) hpre.graph.v hpre.graph.d hpre.graph.e ?_
    let le0 := PTree.set id.e (.Vptr be eo) (PTree.set id.d (.Vptr bd dofs) (PTree.set id.v (.Vptr bv vo) E))
    have hn0' : PTree.get id.n le0 = some (.Vint (ir n)) := by
      simp (config := {decide := true}) only [le0, E, entryTemps, temps_gso, temps_gss]
    wp_step
    refine wp_dynW 0 find_work1Sz find_work1 hpre.works hn0' hnlt ?_
    intro le1 m1 cap1 b1 hW1 hc1 ho1 hu1 hf1 hz1 hg1 ht1
    have hn1 : PTree.get id.n le1 = some (.Vint (ir n)) := by
      rw [ht1 _ (by decide) (by decide)]; exact hn0'
    wp_step
    refine wp_dynW 1 find_work2Sz find_work2 hW1 hn1 hnlt ?_
    intro le2 m2 cap2 b2 hW2 hc2 ho2 hu2 hf2 hz2 hg2 ht2
    have hn2 : PTree.get id.n le2 = some (.Vint (ir n)) := by
      rw [ht2 _ (by decide) (by decide)]; exact hn1
    wp_step
    refine wp_dynW 2 find_work3Sz find_work3 hW2 hn2 hnlt ?_
    intro le3 m3 cap3 b3 hW3 hc3 ho3 hu3 hf3 hz3 hg3 ht3
    have hn3 : PTree.get id.n le3 = some (.Vint (ir n)) := by
      rw [ht3 _ (by decide) (by decide)]; exact hn2
    wp_step
    refine wp_dynW 3 find_work4Sz find_work4 hW3 hn3 hnlt ?_
    intro le4 m4 cap4 b4 hW4 hc4 ho4 hu4 hf4 hz4 hg4 ht4
    -- the four pairs
    obtain ⟨C, hCd⟩ : ∃ C, C = fset (fset (fset (fset c 0 cap1) 1 cap2) 2 cap3) 3 cap4 := ⟨_, rfl⟩
    obtain ⟨B, hBd⟩ : ∃ B, B = fset (fset (fset (fset b 0 b1) 1 b2) 2 b3) 3 b4 := ⟨_, rfl⟩
    rw [← hCd, ← hBd] at hW4 ho4
    have hg : ∀ z, Mem.valid_block m z → Mem.valid_block m4 z := fun z h => hg4 _ (hg3 _ (hg2 _ (hg1 _ h)))
    have hO : Orig m c b C B :=
      ((ho1.trans ho2 hg1).trans ho3 (fun z h => hg2 _ (hg1 _ h))).trans ho4
        (fun z h => hg3 _ (hg2 _ (hg1 _ h)))
    have hU : Unch m m4 (worksSet m c b) :=
      ((hu1.trans (hu2.mono (worksSet_mono ho1 hg1))).trans
        (hu3.mono (worksSet_mono (ho1.trans ho2 hg1) (fun z h => hg2 _ (hg1 _ h))))).trans
        (hu4.mono (worksSet_mono ((ho1.trans ho2 hg1).trans ho3 (fun z h => hg2 _ (hg1 _ h)))
          (fun z h => hg3 _ (hg2 _ (hg1 _ h)))))
    have hCn : ∀ k, n ≤ C k := by
      obtain ⟨e0, e1, e2, e3⟩ := fset_cases c cap1 cap2 cap3 cap4
      refine fin4_all ?_ ?_ ?_ ?_
      · rw [hCd, e0]; omega
      · rw [hCd, e1]; omega
      · rw [hCd, e2]; omega
      · rw [hCd, e3]; omega
    have hC0 : ∀ k, 0 < C k := fun k => by have := hCn k; omega
    have hH4 : HitsOk m (c 2) (b 2) → HitsOk m4 (C 2) (B 2) := fun hH => by
      have h1 := hits_other hpre.works (k := 0) (by decide) hf1 hH
      have h2 := hits_other hW1 (k := 1) (by decide) hf2 (by simpa [fset] using h1)
      have h3 := hits_new hW3 (by omega) (by simpa [fset] using h2) hz3
      have h4 := hits_other hW3 (k := 3) (by decide) hf4 (by simpa [fset] using h3)
      rw [hCd, hBd]; simpa [fset] using h4
    have hle4 : ∀ x, x ≠ idOf 703 → x ≠ idOf 704 → x ≠ idOf 705 → x ≠ idOf 706 → x ≠ idOf 707 →
        x ≠ idOf 708 → x ≠ idOf 709 → x ≠ idOf 710 → PTree.get x le4 = PTree.get x le0 :=
      fun x a1 a2 a3 a4 a5 a6 a7 a8 => by
        rw [ht4 _ a7 a8, ht3 _ a5 a6, ht2 _ a3 a4, ht1 _ a1 a2]
    have hn4 : PTree.get id.n le4 = some (.Vint (ir n)) := by
      rw [hle4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hn0'
    have hptr : ∀ k, Mem.load .Mint64 m4 (wp k) (zOfInt 0) = some (.Vptr (B k) Ptrofs.zero) :=
      fun k => (hW4.dyn k).ptr (hC0 k)
    have hcall : ∀ z ∈ [bv, bd, be, bl, bp], Apart m c b z := fun z hz =>
      hpre.caller z (List.mem_cons_of_mem _ hz)
    dsimp only
    simp only [E0_append]
    -- `work1b = work1 + n/2;`
    have ediv : Exec.evalExpr sge empty_env le4 m4 (.Ebinop .Odiv (tv id.n) (ci 2 tint) tint) =
        some (.Vint (ir ((n / 2 : Nat) : Int))) := by
      simp only [Exec.evalExpr, hn4, typeof, cop]
      have e1 : Lib.Integers.Int.eq (Lib.Integers.Int.repr (zOfInt 2)) Lib.Integers.Int.zero = false :=
        by decide
      have e2 : Lib.Integers.Int.eq (Lib.Integers.Int.repr (zOfInt 2)) Lib.Integers.Int.mone = false :=
        by decide
      rw [e1, e2, Bool.and_false, Bool.or_false]
      simp only [Bool.false_eq_true, ite_false]
      exact congrArg (fun z => some (val.Vint z)) (Sort.ir_divs (a := n) (b := 2) (by omega) (by decide)
        (by decide))
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, eval_gvar (k := 0) find_work1 (hptr 0), ediv]
    simp only [typeof, cop]
    obtain ⟨o1b, ho1b⟩ : ∃ o, o = Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr
        (Cfrontend.Ctypes.sizeof sge.genv_cenv tint)) (Ptrofs.of_ints (ir ((n / 2 : Nat) : Int)))) :=
      ⟨_, rfl⟩
    rw [← ho1b]
    have ho1b' : intOfZ (Ptrofs.unsigned o1b) = 0 + csize .Mint32 * ((n / 2 : Nat) : Int) := by
      rw [ho1b, addr_elem Ptrofs.zero (Cfrontend.Ctypes.sizeof sge.genv_cenv tint) .Mint32 rfl
        (base := 0) rfl (i := n / 2) (by omega) (by simp only [show csize .Mint32 = 4 from rfl]; omega), intOfZ_zOfInt]
    -- `i = nnt = 0;`
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gso _ _ (show id.t0 ≠ id.nnt by decide), temps_gss, E0_append]
    let le5 := PTree.set id.i (.Vint (ir 0)) (PTree.set id.nnt (.Vint (ir 0))
      (PTree.set id.t0 (.Vint (ir 0)) (PTree.set id.work1b (.Vptr (B 0) o1b) le4)))
    show Wp xi sge F _ _ empty_env le5 m4
    have g5 : ∀ x, Args x → x ≠ id.work1b → PTree.get x le5 = PTree.get x le0 := by
      intro x hx hw
      have h1 : x ≠ id.i ∧ x ≠ id.nnt ∧ x ≠ id.t0 ∧ x ≠ idOf 703 ∧ x ≠ idOf 704 ∧ x ≠ idOf 705 ∧
          x ≠ idOf 706 ∧ x ≠ idOf 707 ∧ x ≠ idOf 708 ∧ x ≠ idOf 709 ∧ x ≠ idOf 710 := by
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd rfl hw | decide
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h1
      simp only [le5]
      rw [temps_gso _ _ a1, temps_gso _ _ a2, temps_gso _ _ a3, temps_gso _ _ hw,
        hle4 _ a4 a5 a6 a7 a8 a9 a10 a11]
    have nA : ∀ z ∈ [bv, bd, be, bl, bp], ¬ worksSet m c b z := fun z hz =>
      (hcall z hz).not_mem
    have hF : Frame m4 le5 G bv vo bd dofs be eo bl lofs lab bp pofs ptn level B o1b :=
      { hlab := by
          rw [g5 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [le0, E, entryTemps, temps_gso, temps_gss]
        hptn := by
          rw [g5 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [le0, E, entryTemps, temps_gso, temps_gss]
        hlev := by
          rw [g5 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [le0, E, entryTemps, temps_gso, temps_gss]
        hn := by rw [g5 _ (by decide) (by decide)]; exact hn0'
        hv := by
          rw [g5 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [le0, temps_gso, temps_gss]
        hd := by
          rw [g5 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [le0, temps_gso, temps_gss]
        he := by
          rw [g5 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [le0, temps_gss]
        h1b := by
          simp only [le5]
          rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]
        o1b := ho1b'
        varr := hpre.graph.varr.unch hU (nA bv (by simp))
        darr := hpre.graph.darr.unch hU (nA bd (by simp))
        earr := hpre.graph.earr.unch hU (nA be (by simp))
        larr := hpre.larr.unch hU (nA bl (by simp))
        lsmall := hpre.lsmall
        linj := Spec.surj_inj (f := fun j => lab[j]!) hpre.lsmall fun v hv => by
          obtain ⟨j, hj, he⟩ := hpre.lonto v hv
          exact ⟨j, hj, he⟩
        lonto := hpre.lonto
        parr := hpre.parr.unch hU (nA bp (by simp))
        psize := hpre.psize
        psmall := hpre.psmall
        plast := hpre.plast
        levlt := hpre.levlt
        wptr := hptr
        wdist := fun k k' h => hW4.distinct k k' h (hC0 k) (hC0 k')
        wapart := fun k z hz => by
          rcases List.mem_append.1 hz with hz | hz
          · have hA := hcall z hz
            rcases hO k with ⟨e1, e2⟩ | hnv
            · rw [e2]; exact fun h => hA.blk k (e1 ▸ hC0 k) h.symm
            · exact fun h => hnv (h ▸ hA.valid)
          · exact fun h => hW4.apart k (hC0 k) (h ▸ hz)
        n0 := hn0
        nlt := hnlt }
    obtain ⟨W1, hw1⟩ := Alloc.malloced_array ((hW4.dyn 0).mal (hC0 0)) .Mint32 4 rfl rfl n
      (Nat.mul_le_mul_left 4 (hCn 0))
    obtain ⟨W2, hw2⟩ := Alloc.malloced_array ((hW4.dyn 1).mal (hC0 1)) .Mint32 4 rfl rfl n
      (Nat.mul_le_mul_left 4 (hCn 1))
    obtain ⟨W3, hw3⟩ := Alloc.malloced_array ((hW4.dyn 2).mal (hC0 2)) .Mint32 4 rfl rfl n
      (Nat.mul_le_mul_left 4 (hCn 2))
    obtain ⟨W4, hw4⟩ := Alloc.malloced_array ((hW4.dyn 3).mal (hC0 3)) .Mint32 4 rfl rfl n
      (Nat.mul_le_mul_left 4 (hCn 3))
    have post : ∀ mF, Mod m4 mF B → (∀ z, Mem.valid_block m4 z → Mem.valid_block mF z) →
        (HitsOk m (c 2) (b 2) → HitsOk mF (C 2) (B 2)) → Post m mF c b := fun mF hmod hgF hH => by
      have nB : ∀ z ∈ wglobs, ¬ ∃ k, z = B k := fun z hz ⟨k, he⟩ => hW4.apart k (hC0 k) (he ▸ hz)
      exact ⟨C, B, ⟨fun k => (hW4.dyn k).keep hmod.1 (nB _ (wp_mem k)) (nB _ (ws_mem k))
          (fun _ => hmod.2 k), hW4.apart, hW4.distinct⟩, hO,
        hU.trans (hmod.1.mono (worksSet_of hO hC0)), fun z h => hgF _ (hg _ h), hH⟩
    -- the cell scan
    wp_step
    refine wp_cellLoop hF hw1 hw2 (temps_gss _ _ _)
      (by simp only [le5]; rw [temps_gso _ _ (by decide), temps_gss]) ?_
    intro le6 m6 W1' W2' hw1' hw2' hS1 hW2' hnnt6 hgood hmod6 h016 hg6 ho6
    have hH6 : HitsOk m (c 2) (b 2) → HitsOk m6 (C 2) (B 2) := fun hH =>
      (hH4 hH).unch h016 (by rintro (e | e); exact hF.wdist 2 0 (by decide) e; exact hF.wdist 2 1 (by decide) e)
    have hF6 := (hF.unch hmod6.1).temps (le' := le6) fun x hx => ho6 x (args_not_scan x hx)
    have harr : ∀ mF, Mod m4 mF B → ∀ k, ∃ vals, ArrayAt mF .Mint32 (B k) 0 vals n := by
      intro mF hmod k
      have nB : ∀ z ∈ wglobs, ¬ ∃ k, z = B k := fun z hz ⟨k, he⟩ => hW4.apart k (hC0 k) (he ▸ hz)
      have hD := (hW4.dyn k).keep hmod.1 (nB _ (wp_mem k)) (nB _ (ws_mem k)) (fun _ => hmod.2 k)
      exact Alloc.malloced_array (hD.mal (hC0 k)) .Mint32 4 rfl rfl n (Nat.mul_le_mul_left 4 (hCn k))
    have hgK := hgood.half
    have hfK := hgood.fle
    dsimp only
    -- `if (nnt == 0) return n;`
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hnnt6, typeof, cop]
    rw [ir_eq (a := ((cells n lab ptn level).starts.size : Int)) (b := 0) ⟨by omega, by omega⟩
      ⟨by decide, by decide⟩]
    by_cases hK0 : (cells n lab ptn level).starts.size = 0
    · rw [ite_eq_left (by simp [hK0])]
      wp_step; wp_step
      apply wp_return_some_eval
      simp only [Exec.evalExpr, hF6.hn, typeof, cop, sparse.fn.«nausparse:bestcell_sg».fn_return_eq,
        Isautom.free_empty]
      refine ⟨rfl, ?_, post m6 hmod6 hg6 hH6⟩
      rw [bestcell_eq, ite_eq_left (by simp [Array.isEmpty, hK0])]
    rw [ite_eq_right (by simpa using hK0)]
    apply wp_skip
    -- `HITS[i] = COUNT[i] = 0;`
    obtain ⟨W3a, hw3a⟩ := harr m6 hmod6 2
    obtain ⟨W4a, hw4a⟩ := harr m6 hmod6 3
    wp_step
    refine wp_zero hF6 hw3a hw4a hnnt6 (by omega) ?_
    intro le7 m7 W3z W4z hw3z hw4z hz hu7 hout7 hk72 hk73 hg7 ho7
    have hF7 := (hF6.unch (hu7.mono fun _ hz => hz.elim (fun e => ⟨2, e⟩) (fun e => ⟨3, e⟩))).temps
      (le' := le7) fun x hx => ho7 x
        (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hmod7 := hF6.mod23 hu7 hk72 hk73
    have hnnt7 : PTree.get id.nnt le7 = some (.Vint (ir ((cells n lab ptn level).starts.size : Int))) := by
      rw [ho7 _ (by decide) (by decide)]; exact hnnt6
    -- the counts
    wp_step
    refine wp_joins hF7 hgood (hw1'.unch hu7 (hF6.not23 0 (.inl rfl))) hS1
      (hw2'.unch hu7 (hF6.not23 1 (.inr rfl))) hW2' hw3z hw4z hz hnnt7 ?_
    intro le8 m8 W4c hw4c hc8 hu8 ⟨W3f, hw3f, hz3f⟩ hout8 hk82 hk83 hg8 ho8
    have hH8 : HitsOk m (c 2) (b 2) → HitsOk m8 (C 2) (B 2) := fun hH => by
      obtain ⟨T, hT, ha⟩ := hH6 hH
      have ho : Outside m6 m8 (B 2) (0 + csize .Mint32 * ((0 : Nat) : Int))
          (0 + csize .Mint32 * (((0 + (cells n lab ptn level).starts.size : Nat)) : Int)) := by
        simpa using hout7.trans hout8
      have hs := hw3f.slice 0 (cells n lab ptn level).starts.size (by omega)
      have hf := ha.outside 0 _ hs ho
      refine ⟨fun i => if i < (cells n lab ptn level).starts.size then 0 else T i, fun i => ?_,
        hf.congr fun i _ => ?_⟩
      · by_cases h : i < (cells n lab ptn level).starts.size
        · simp only [ite_eq_left h]; decide
        · simp only [ite_eq_right h]; exact hT i
      · by_cases h : i < (cells n lab ptn level).starts.size
        · simp only [Nat.zero_le, true_and, Nat.zero_add, h, ite_true, Nat.sub_zero]
          exact hz3f i h
        · simp only [Nat.zero_le, true_and, Nat.zero_add, h, ite_false]
    have hF8 := (hF7.unch (hu8.mono fun _ hz => hz.elim (fun e => ⟨2, e⟩) (fun e => ⟨3, e⟩))).temps
      (le' := le8) fun x hx => ho8 x (args_not_j x hx)
    have hmod8 := hF7.mod23 hu8 hk82 hk83
    have hw1c := (hw1'.unch hu7 (hF6.not23 0 (.inl rfl))).unch hu8 (hF7.not23 0 (.inl rfl))
    have hnnt8 : PTree.get id.nnt le8 = some (.Vint (ir ((cells n lab ptn level).starts.size : Int))) := by
      rw [ho8 _ (by decide)]; exact hnnt7
    let K := (cells n lab ptn level).starts.size
    let cnt := countAt (Graph.ofGraph G) lab (cells n lab ptn level)
    have hcnt : ∀ k < K, cnt k ≤ n := by
      intro k hk
      let P := ((List.range k).foldl (pick (Graph.ofGraph G) lab (cells n lab ptn level))
        (Array.replicate K 0, 0, 0)).1
      have hP := zero_pick (Graph.ofGraph G) lab (cells n lab ptn level) (List.range k)
        (Array.replicate K 0, 0, 0) (zero_init K)
      have hst := hgood.startLt k hk
      have hu := hF.lsmall _ hst
      have hJ := (joins_zero (Graph.ofGraph G) (cells n lab ptn level).nntcell
        (cells n lab ptn level).sizes (h := P) hP.2 lab[(cells n lab ptn level).starts[k]!]!).2.2
      have hD := degree_lt G hu
      simp only [row, List.length_range'] at hJ
      exact Nat.le_trans hJ hD
    dsimp only
    -- `j = 0; maxcnt = COUNT[0];`
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop]
    rw [cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_idx (pe := .Evar id.work4 (tptr tint)) (ofs := Ptrofs.zero) (e := empty_env) hw4c (by omega)
      (eval_gvar (k := 3) find_work4 (hF8.wptr 3)) rfl rfl rfl (ci 0 tint) 0 (by omega) rfl rfl,
      hc8 0 (by omega)]
    simp only [E0_append]
    -- the final loop
    wp_step
    refine wp_argLoop (cnt := cnt) (K := K) (hF8.wptr 3) hw4c (by omega) hc8 hcnt (by omega) (by omega)
      (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hnnt8)
      (by rw [temps_gso _ _ (by decide), temps_gss]) (temps_gss _ _ _) ?_
    intro le9 hj9 ho9
    obtain ⟨hb1, -⟩ := argAt_spec cnt K (by omega)
    -- `return START[j];`
    wp_step; wp_step
    apply wp_return_some_eval
    rw [Exec.evalExpr, eval_idx_l (pe := .Evar id.work1 (tptr tint)) (ofs := Ptrofs.zero) (e := empty_env)
      hw1c (by omega) (eval_gvar (k := 0) find_work1 (hF8.wptr 0)) rfl rfl rfl (tl id.j) _ (by omega) hj9 rfl,
      (hS1 _ (by omega)).1]
    simp only [typeof, cop, sparse.fn.«nausparse:bestcell_sg».fn_return_eq, Isautom.free_empty]
    refine ⟨rfl, ?_, post m8 ((hmod6.trans hmod7).trans hmod8) (fun z h => hg8 _ (hg7 _ (hg6 _ h))) hH8⟩
    rw [bestcell_eq, ite_eq_right (by simpa [Array.isEmpty] using hK0)]
    have hch := choose_arg (Graph.ofGraph G) lab (cells n lab ptn level) K (by omega)
    simp only [choose]
    rw [hch]
    rfl

end NautyVerified.Proofs.Sparse.Bestcell

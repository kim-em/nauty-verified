import NautyVerified.Proofs.Sparse.Refine.Count.Inner

/-!
# One count split

`minima_bounds`: after the first run, the three-way insertion leaves its
second key below `n + 2` and its second run's end inside the cell.
`wp_inner`: `innerG` computes `finish` after its two hashes. `countPass`:
the count split of one cell (`cellD`, `cellN`) computes `splitCounts`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk isElement addElementB delElementB)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The insertion's invariant at `j`, for the bounds. -/
def MinB (lab hits : Array Nat) (N first begin j : Nat) (st : Nat × Nat × Nat × Nat × Array Nat) : Prop :=
  begin ≤ j ∧ st.2.2.2.1 ≤ j ∧ st.2.1 ≤ st.2.2.2.1 ∧ first + 1 ≤ st.2.1 ∧ st.1 < N + 2 ∧
    st.2.2.1 ≤ N + 2 ∧ (begin < j → st.2.2.1 < N + 2) ∧ (begin = j → st.1 = hits[lab[first]!]!) ∧
    ∀ q, j ≤ q → st.2.2.2.2[q]! = lab[q]!

theorem minB_step {lab hits : Array Nat} {N first begin j : Nat} {st : Nat × Nat × Nat × Nat × Array Nat}
    (h : MinB lab hits N first begin j st) (hk : hits[lab[j]!]! < N + 2)
    (hne : begin = j → hits[lab[j]!]! ≠ hits[lab[first]!]!) :
    MinB lab hits N first begin (j + 1) (minStep hits first st j) := by
  obtain ⟨w1, v2, w2, v3, l⟩ := st
  obtain ⟨hb, h3, h23, h12, hw1, hw2, hw2', hw1', hl⟩ := h
  simp only at hb h3 h23 h12 hw1 hw2 hw2' hw1' hl
  have hlj : l[j]! = lab[j]! := hl j (Nat.le_refl _)
  have hk' : hits[l[j]!]! < N + 2 := by rw [hlj]; exact hk
  have hout : ∀ (a : Array Nat) (x y : Nat), x ≤ j → (∀ q, j + 1 ≤ q → a[q]! = lab[q]!) →
      ∀ q, j + 1 ≤ q → (a.set! x y)[q]! = lab[q]! := fun a x y hx ha q hq => by
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]; exact ha q hq
  have hl1 : ∀ q, j + 1 ≤ q → l[q]! = lab[q]! := fun q hq => hl q (by omega)
  unfold minStep
  simp only
  split
  · rename_i he
    have he' : hits[l[j]!]! = w1 := by simpa using he
    refine ⟨by omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, hw1, hw2,
      fun hbj => ?_, fun hbj => absurd hbj (by omega), ?_⟩
    · by_cases hbj' : begin = j
      · exact absurd (hw1' hbj' ▸ hlj ▸ he') (hne hbj')
      · exact hw2' (by omega)
    · exact hout _ _ _ (by omega) (hout _ _ _ (by omega) (hout _ _ _ (by omega) hl1))
  · split
    · rename_i _ he
      have he' : hits[l[j]!]! = w2 := by simpa using he
      refine ⟨by omega, by dsimp only; omega, by dsimp only; omega, h12, hw1, hw2,
        fun _ => by dsimp only; omega, fun hbj => absurd hbj (by omega), ?_⟩
      exact hout _ _ _ (by omega) (hout _ _ _ (by omega) hl1)
    · split
      · rename_i _ _ hlt
        refine ⟨by omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, fun _ => by dsimp only; omega, fun hbj => absurd hbj (by omega), ?_⟩
        exact hout _ _ _ (by omega) (hout _ _ _ (by omega) (hout _ _ _ (by omega) hl1))
      · split
        · rename_i _ _ _ hlt
          refine ⟨by omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, hw1,
            by dsimp only; omega, fun _ => by dsimp only; omega, fun hbj => absurd hbj (by omega), ?_⟩
          exact hout _ _ _ (by omega) (hout _ _ _ (by omega) hl1)
        · rename_i h1 h2 h3 h4
          have h2' : ¬ hits[l[j]!]! = w2 := by simpa using h2
          have h4' : ¬ hits[l[j]!]! < w2 := h4
          refine ⟨by omega, by dsimp only; omega, h23, h12, hw1, hw2, fun _ => by dsimp only; omega,
            fun hbj => absurd hbj (by omega), hl1⟩

theorem minB_fold {lab hits : Array Nat} {N first begin last : Nat}
    (hk : ∀ q, first ≤ q → q < last → hits[lab[q]!]! < N + 2) (hf : first < begin)
    (hne : hits[lab[begin]!]! ≠ hits[lab[first]!]!) :
    ∀ (k j : Nat) (st : Nat × Nat × Nat × Nat × Array Nat), MinB lab hits N first begin j st →
      j + k ≤ last → MinB lab hits N first begin (j + k) ((List.range' j k).foldl (minStep hits first) st)
  | 0, j, st, h, _ => h
  | k + 1, j, st, h, hl => by
    rw [List.range'_succ, List.foldl_cons, show j + (k + 1) = (j + 1) + k by omega]
    exact minB_fold hk hf hne k (j + 1) _ (minB_step h (hk j (by have := h.1; omega) (by omega))
      (fun e => e ▸ hne)) (by omega)

/-- After the first run the second key is a real key and the second run ends
inside the cell. -/
theorem minima_bounds {lab hits : Array Nat} {N first begin last : Nat} (hb1 : first + 1 ≤ begin)
    (hb2 : begin < last)
    (hk : ∀ q, first ≤ q → q < last → hits[lab[q]!]! < N + 2)
    (hne : hits[lab[begin]!]! ≠ hits[lab[first]!]!) :
    (Hex.GraphIso.Nauty.Sparse.CountSort.minima lab hits (N + 2) first last begin).2.2.2.1 ≤ last ∧
      (Hex.GraphIso.Nauty.Sparse.CountSort.minima lab hits (N + 2) first last begin).2.2.1 < N + 2 := by
  rw [minima_eq]
  have h0 : MinB lab hits N first begin begin (hits[lab[first]!]!, begin, N + 2, begin, lab) :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, hb1, hk first (Nat.le_refl _) (by omega),
      Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _), fun _ => rfl, fun _ _ => rfl⟩
  have h := minB_fold hk (by omega) hne (last - begin) begin _ h0 (by omega)
  rw [show begin + (last - begin) = last by omega] at h
  exact ⟨h.2.1, h.2.2.2.2.2.2.1 hb2⟩

end NautyVerified.Proofs.Sparse.Refine.Count

namespace NautyVerified.Proofs.Sparse.Refine.Count

open Hex.GraphIso.Nauty.Sparse (RefineSt)
open NautyVerified.Spec.SortC (iterF)

theorem iterF_runBody_spec (lab hits : Array Nat) (w1 : Nat) : ∀ (f v : Nat),
    v ≤ iterF (runBody lab hits w1) f v ∧ iterF (runBody lab hits w1) f v ≤ v + f ∧
      (iterF (runBody lab hits w1) f v = v + f ∨ hits[lab[iterF (runBody lab hits w1) f v]!]! ≠ w1)
  | 0, v => ⟨Nat.le_refl _, by simp [iterF], .inl (by simp [iterF])⟩
  | f + 1, v => by
    simp only [iterF, runBody]
    by_cases h : (hits[lab[v]!]! != w1) = true
    · simp only [h, ite_true]
      exact ⟨Nat.le_refl _, by omega, .inr (by simpa using h)⟩
    · simp only [h, Bool.false_eq_true, ite_false]
      obtain ⟨h1, h2, h3⟩ := iterF_runBody_spec lab hits w1 f (v + 1)
      exact ⟨by omega, by omega, h3.imp_left (fun e => by omega)⟩

/-- The first run ends after `first` and within the cell, at a different key unless at the end. -/
theorem firstRun_bounds (lab hits : Array Nat) {first last : Nat} (h : first + 1 ≤ last) :
    first + 1 ≤ Hex.GraphIso.Nauty.Sparse.CountSort.firstRun lab hits first last ∧
      Hex.GraphIso.Nauty.Sparse.CountSort.firstRun lab hits first last ≤ last ∧
      (Hex.GraphIso.Nauty.Sparse.CountSort.firstRun lab hits first last = last ∨
        hits[lab[Hex.GraphIso.Nauty.Sparse.CountSort.firstRun lab hits first last]!]! ≠
          hits[lab[first]!]!) := by
  rw [firstRun_eq]
  obtain ⟨h1, h2, h3⟩ := iterF_runBody_spec lab hits hits[lab[first]!]! (last - (first + 1)) (first + 1)
  exact ⟨h1, by omega, h3.imp_left (fun e => by omega)⟩

end NautyVerified.Proofs.Sparse.Refine.Count

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk isElement addElementB delElementB)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem innerG_eq (d : Bool) (t1 t2 t3 t4 t5 tv0 tv1 : ident) :
    innerG d t1 t2 t3 t4 t5 (fragG d tv0 (runLoopG tv1)) =
      .Sifthenelse (.Ebinop .One (tv id.«j») (tv id.«v2») tint)
        (installS (sk (.Sifthenelse (.Ebinop .Oeq (tv id.«j») (tv id.«v3») tint) (twoS t1 t2 t3)
          (restS d t4 t5 tv0 tv1)))) .Sskip := by
  cases d <;> rfl

/-- The temporaries `innerG` assigns, besides `longcode` and `nactive`. -/
def innerTemps (t1 t2 t3 t4 t5 tv0 tv1 : ident) : List ident :=
  [id.«k», t1, t2, t3, t4, t5, id.«bigpos», id.«bigsize»] ++ fragTemps tv0 tv1

/-- `finish` after its two hashes. -/
def finRes (level first last : Nat) (d : Bool) (u : RefineSt n) (v2 v3 : Nat) : RefineSt n :=
  if last == v2 then u else tail level first last d (install2 level first u v2 v3) v2 v3

theorem install2_fields (level first : Nat) (u : RefineSt n) (v2 v3 : Nat) :
    (install2 level first u v2 v3).lab = u.lab ∧ (install2 level first u v2 v3).hits = u.hits ∧
      (install2 level first u v2 v3).queue = u.queue ∧
      (install2 level first u v2 v3).cellstart.size = u.cellstart.size ∧
      (install2 level first u v2 v3).ptn.size = u.ptn.size ∧
      (install2 level first u v2 v3).longcode = u.longcode := by
  refine ⟨rfl, rfl, rfl, ?_, by simp [install2], rfl⟩
  simp only [install2]
  split <;> split <;> simp only [startsLit_eq, foldl_set_size, Array.size_set!]

end NautyVerified.Proofs.Sparse.Refine.Count

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk isElement addElementB delElementB)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem wp_inner {Q : Post} {le : temp_env} {m : mem} {d : Bool} {t1 t2 t3 t4 t5 tv0 tv1 : ident}
    (h1 : TT t1) (h2 : TT t2) (h3 : TT t3) (h4 : TT t4) (h5 : TT t5) (htv : FragT tv0 tv1)
    (hv1t : id.«v1» ∉ fragTemps tv0 tv1) (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S)
    (ht : Tmp le L t) {first v2 v3 last : Nat} (h12 : first + 1 ≤ v2) (h23 : v2 ≤ v3) (h3l : v3 ≤ last)
    (hl : last ≤ n) (hlab : ∀ q < n, t.lab[q]! < n) (hsz : t.lab.size = n)
    (hcs : t.cellstart.size = n) (hps : t.ptn.size = n) (hc : t.longcode < 2 ^ 62)
    (hhits : ∀ v < n, S.w3[v]! = t.hits[v]!) (hqe : ∀ i < t.queue.size, t.queue[i]! < n)
    (hfin : (finRes L.level first last d t v2 v3).queue.size ≤ n)
    (hfl : ∀ q < n, (finRes L.level first last d t v2 v3).lab[q]! < n)
    (hv1 : PTree.get id.«v1» le = some (.Vint (ir first)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir v2)))
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir v3)))
    (hj : PTree.get id.«j» le = some (.Vint (ir last)))
    (hQ : ∀ le' m' S', After2 L G S m le (innerTemps t1 t2 t3 t4 t5 tv0 tv1)
      (finRes L.level first last d t v2 v3) le' m' S' →
      (finRes L.level first last d t v2 v3).longcode < 2 ^ 62 → Q.normal E0 empty_env le' m') :
    Wp xi sge F (innerG d t1 t2 t3 t4 t5 (fragG d tv0 (runLoopG tv1))) Q empty_env le m := by
  have hnl := hok.nlt
  rw [innerG_eq]
  apply wp_if_eval
  rw [eval_cmp hj hv2]
  simp only [typeof, cop]
  rw [ir_eq (a := (last : Int)) (b := (v2 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  have hnot : ∀ x, x ∉ innerTemps t1 t2 t3 t4 t5 tv0 tv1 → x ≠ id.«k» ∧ x ∉ [t1, t2, t3] ∧
      x ∉ [t4, t5, id.«bigpos», id.«bigsize»] ++ fragTemps tv0 tv1 := fun x hx => by
    simp only [innerTemps, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx ⊢
    exact ⟨hx.1.1, ⟨hx.1.2.1, hx.1.2.2.1, hx.1.2.2.2.1⟩, ⟨hx.1.2.2.2.2.1, hx.1.2.2.2.2.2.1,
      hx.1.2.2.2.2.2.2.1, hx.1.2.2.2.2.2.2.2⟩, hx.2⟩
  by_cases hlv : last = v2
  · rw [show decide ((last : Int) = v2) = true from decide_eq_true (by omega)]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    apply wp_skip
    have hfr : finRes L.level first last d t v2 v3 = t := by simp [finRes, hlv]
    rw [hfr] at hQ
    exact hQ le m S ⟨hm, hr, ht, Frame.refl _ _, Keeps.refl _, fun _ _ _ _ => rfl⟩ hc
  · rw [show decide ((last : Int) = v2) = false from decide_eq_false (by omega)]
    simp only [Bool.not_false, ite_true]
    have hfr : finRes L.level first last d t v2 v3 =
        tail L.level first last d (install2 L.level first t v2 v3) v2 v3 := by simp [finRes, hlv]
    rw [hfr] at hQ hfin hfl
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := install2_fields L.level first t v2 v3
    refine wp_install hok hm hr ht h12 h23 (by omega) hlab hcs hps hv1 hv2 hv3 ?_
    intro le1 m1 S1 hm1 hr1 ht1 hf1 hk1 ho1
    have hv1' : PTree.get id.«v1» le1 = some (.Vint (ir first)) := by rw [ho1 _ (by decide)]; exact hv1
    have hv2' : PTree.get id.«v2» le1 = some (.Vint (ir v2)) := by rw [ho1 _ (by decide)]; exact hv2
    have hv3' : PTree.get id.«v3» le1 = some (.Vint (ir v3)) := by rw [ho1 _ (by decide)]; exact hv3
    have hj' : PTree.get id.«j» le1 = some (.Vint (ir last)) := by rw [ho1 _ (by decide)]; exact hj
    wp_step; wp_step
    apply wp_if_eval
    rw [eval_cmp hj' hv3']
    simp only [typeof, cop]
    rw [ir_eq (a := (last : Int)) (b := (v3 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases h3v : last = v3
    · rw [show decide ((last : Int) = v3) = true from decide_eq_true (by omega)]
      simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
      have htail : tail L.level first last d (install2 L.level first t v2 v3) v2 v3 =
          if v2 - first ≤ v3 - v2 && !(install2 L.level first t v2 v3).active.mem first then
            (install2 L.level first t v2 v3).push first else (install2 L.level first t v2 v3).push v2 := by
        simp [tail, h3v]
      rw [htail] at hQ hfin
      have hq : (install2 L.level first t v2 v3).queue.size < n := by
        split at hfin <;> simp only [RefineSt.push, Array.size_push] at hfin <;> omega
      refine wp_two h1 h2 h3 hok hm1 hr1 ht1 h12 h23 (by omega) (by omega) hv1' hv2' hv3' hq ?_
      rintro le' m' S' ⟨hm', hr', ht', hf', hk', ho'⟩
      refine hQ le' m' S' ⟨hm', hr', ht', hf1.trans hf', hk1.trans hk', fun x hx h1 h2 => ?_⟩ (by
        split <;> (show (install2 L.level first t v2 v3).longcode < _; rw [i6]; exact hc))
      rw [ho' x (hnot x hx).2.1 h1 h2, ho1 x (hnot x hx).1]
    · rw [show decide ((last : Int) = v3) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [Val.of_bool, cop, ite_false]
      rw [tail_rest _ _ _ _ _ _ _ h3v] at hQ hfin hfl
      refine wp_rest h4 h5 htv hok hm1 hv1t hr1 ht1 h12 h23 (by omega) hl (by rw [i1]; exact hlab)
        (by rw [i1]; exact hsz) (by rw [i4]; exact hcs) (by rw [i5]; exact hps) (by rw [i6]; exact hc)
        (fun v hv => by rw [hk1.w3, i2]; exact hhits v hv) (by rw [i3]; exact hqe) hfin hfl hv1' hv2' hv3' hj' ?_
      rintro le' m' S' ⟨hm', hr', ht', hf', hk', ho'⟩ hc'
      exact hQ le' m' S' ⟨hm', hr', ht', hf1.trans hf', hk1.trans hk', fun x hx h1 h2 => by
        rw [ho' x (hnot x hx).2.2 h1 h2, ho1 x (hnot x hx).1]⟩ hc'

end NautyVerified.Proofs.Sparse.Refine.Count

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk isElement addElementB delElementB)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph splitCounts)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The `continue` after a one-fragment cell. -/
abbrev contG : Bool → statement
  | true => .Ssequence (sk (.Sset id.«v1» (tv id.«v2»))) .Scontinue
  | false => .Scontinue

/-- The installation, with its two hashes. -/
abbrev installG (d : Bool) (inner : statement) : statement :=
  .Ssequence (sk (mash (tv (if d then id.«w2» else id.«w1»))))
    (.Ssequence (sk (mash (tv id.«v2»))) (optEnd d (sk inner) (sk (.Sset id.«v1» (tv id.«j»)))))

/-- One count split, for both passes. -/
abbrev cellG (d : Bool) (tr tm tc : ident) (inner : statement) : statement :=
  .Ssequence (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint)))
    (.Ssequence (runG tr)
      (.Ssequence
        (sk (.Sifthenelse
          (.Ebinop .Ole (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint)) (tv id.«level») tint)
          (contG d)
          .Sskip))
        (.Ssequence (sk (.Sset id.«w2» (ci 2000000002 tint)))
          (.Ssequence
            (.Ssequence
              (.Ssequence (sk (.Sset tc (.Ecast (tv id.«v2») tint))) (.Sset id.«j» (tv tc)))
              (.Sset id.«v3» (tv tc)))
            (.Ssequence (minG tm) (installG d inner))))))

theorem cellD_eq : cellD = cellG true (idOf 716) (idOf 718) (idOf 717)
    (innerG true (idOf 721) (idOf 719) (idOf 720) (idOf 722) (idOf 725)
      (fragG true (idOf 723) (runLoopG (idOf 724)))) := rfl

theorem cellN_eq : cellN = cellG false (idOf 753) (idOf 755) (idOf 754)
    (innerG false (idOf 758) (idOf 756) (idOf 757) (idOf 759) (idOf 762)
      (fragG false (idOf 760) (runLoopG (idOf 761)))) := rfl

end NautyVerified.Proofs.Sparse.Refine.Count

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk isElement addElementB delElementB)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph splitCounts)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The temporary names of one count split. -/
structure CellT (d : Bool) (tr tm tc t1 t2 t3 t4 t5 tv0 tv1 : ident) : Prop where
  h1 : TT t1
  h2 : TT t2
  h3 : TT t3
  h4 : TT t4
  h5 : TT t5
  hfrag : FragT tv0 tv1
  hv1f : id.«v1» ∉ fragTemps tv0 tv1
  htr : tr ∉ args ∧ tr ≠ id.longcode ∧ tr ≠ id.nactive ∧ tr ≠ id.«v2» ∧ tr ≠ id.«w1»
  htr1 : tr ≠ id.«v1»
  htm : MinT tm
  htc : tc ∉ args ∧ tc ≠ id.longcode ∧ tc ≠ id.nactive ∧
    tc ∉ [id.«v1», id.«v2», id.«w1», id.«w2», id.«j», id.«v3»]
  hsub : ∀ x, x ∈ [id.«v1», id.«v2», id.«v3», id.«w2», id.«j», tr, tc] ++ minTemps tm ++
    innerTemps t1 t2 t3 t4 t5 tv0 tv1 → x ∈ cellTemps

theorem wp_cellG {d : Bool} {tr tm tc t1 t2 t3 t4 t5 tv0 tv1 : ident}
    (hT : CellT d tr tm tc t1 t2 t3 t4 t5 tv0 tv1) {n : Nat} {L : Loc} {G : Hex.SparseGraph n}
    {Q : Post} {le : temp_env} {m : mem} {s : RefineSt n} {S : Scr} {first : Nat}
    (hok : Ok n L) (hm : Mem m L G s S) (hr : Rep L s S) (ht : Tmp le L (s.hash first))
    (hv : s.Valid L.level) (hb : Budget L.level s) (hc : s.longcode < 2 ^ 62)
    (hh : ∀ v < n, S.w3[v]! = s.hits[v]!)
    (hcell : IsCell s.ptn L.level first (s.cellend[first]! + 1 - first)) (hlt : first < s.cellend[first]!)
    (hce : s.cellend[first]! < n)
    (hkey : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (hv1 : PTree.get id.«v1» le = some (.Vint (ir first)))
    (hw1 : PTree.get id.«w1» le = some (.Vint (ir s.hits[s.lab[first]!]!)))
    (hQ : ∀ le' m' S', After L G (splitCounts L.level first d s) cellTemps le m le' m' S' →
      S'.w3 = S.w3 → S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 → S'.st2 = S.st2 → S'.mk2 = S.mk2 →
      (d = true → PTree.get id.«v1» le' = some (.Vint (ir (s.cellend[first]! + 1)))) →
      (if Hex.GraphIso.Nauty.Sparse.CountSort.firstRun s.lab s.hits first (s.cellend[first]! + 1) =
          s.cellend[first]! + 1 then Q.cont else Q.normal) E0 empty_env le' m') :
    Wp xi sge F (cellG d tr tm tc (innerG d t1 t2 t3 t4 t5 (fragG d tv0 (runLoopG tv1)))) Q
      empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  obtain ⟨last, hlast⟩ : ∃ last, s.cellend[first]! + 1 = last := ⟨_, rfl⟩
  rw [hlast] at hcell hQ
  have hlq : last ≤ n := by omega
  have hkey' : ∀ q, first ≤ q → q < last → s.hits[s.lab[q]!]! < n + 2 :=
    fun q h1 h2 => hkey q h1 (by omega)
  let s0 := s.hash first
  have hm0 : Mem m L G s0 S := hm.congr rfl rfl rfl rfl
  have hr0 : Rep L s0 S := { hr with }
  have hlabn : ∀ q < n, s.lab[q]! < n := fun q hq => Hex.GraphIso.Nauty.Sparse.perm_bound hv.lab hq
  have hsz : s.lab.size = n := by simpa using hv.lab.length_eq
  have hlen : first + (last - first) = last := by omega
  have hk : Keys n L s0 S first (last - first) :=
    ⟨hcell, by omega, hlabn, hh, fun q h1 h2 => hkey' q h1 (by omega)⟩
  have hc0 : s0.longcode < 2 ^ 62 :=
    Nat.lt_of_lt_of_le (NautyVerified.Proofs.Refine.mash_lt _ _) (by decide)
  have hsub := hT.hsub
  have hin : ∀ x, x ∈ [id.«v1», id.«v2», id.«v3», id.«w2», id.«j», tr, tc] ++ minTemps tm ++
      innerTemps t1 t2 t3 t4 t5 tv0 tv1 → ∀ y, y ∉ cellTemps → y ≠ x :=
    fun x hx y hy e => hy (e ▸ hsub x hx)
  -- `v2 = v1 + 1`
  apply wp_seq
  wp_step; wp_step
  apply wp_set_eval
  rw [eval_inc hv1]
  simp only [seqPost, after_E0, E0_append]
  have ht1 := ht.set (x := id.«v2») (.Vint (ir ((first + 1 : Nat) : Int))) (by decide)
  apply wp_seq
  refine wp_run (t := s0) hT.htr hok hm0 hr0 ht1 hk (by rw [temps_gss]; simp)
    (by rw [temps_gso _ _ (by decide)]; exact hw1) ?_
  intro le2 hv22 ho2
  simp only [seqPost, after_E0, E0_append]
  rw [hlen] at hv22
  replace hv22 : PTree.get id.«v2» le2 = some (.Vint (ir
      (Hex.GraphIso.Nauty.Sparse.CountSort.firstRun s.lab s.hits first last))) := hv22
  obtain ⟨hu1, hu2, hu3⟩ := firstRun_bounds s.lab s.hits (show first + 1 ≤ last by omega)
  generalize hu : Hex.GraphIso.Nauty.Sparse.CountSort.firstRun s.lab s.hits first last = u at hv22 hu1 hu2 hu3 hQ
  have ht2 : Tmp le2 L s0 := ht1.frame (ws := [id.«v2», tr]) ho2 (by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact ⟨hT.htr.1, hT.htr.2.1, hT.htr.2.2.1⟩)
  have ho2' : ∀ x, x ≠ id.«v2» → x ≠ tr → PTree.get x le2 = PTree.get x le := fun x a b => by
    rw [ho2 x (by simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]; exact ⟨a, b⟩),
      temps_gso _ _ a]
  have hcut : ∀ x, x ∉ cellTemps → x ≠ id.«v2» ∧ x ≠ tr ∧ x ≠ id.«v1» ∧ x ≠ id.«w2» ∧ x ≠ tc ∧
      x ≠ id.«j» ∧ x ≠ id.«v3» := fun x hx =>
    ⟨hin _ (by simp) x hx, hin _ (by simp) x hx, hin _ (by simp) x hx, hin _ (by simp) x hx,
      hin _ (by simp) x hx, hin _ (by simp) x hx, hin _ (by simp) x hx⟩
  -- the `continue` test
  apply wp_seq
  wp_step; wp_step
  apply wp_if_eval
  rw [eval_binop (eval_ptn hok hm0 ht2 (eval_dec (by omega) hv22) rfl (by omega))
    (show Exec.evalExpr sge empty_env le2 m (tv id.«level») = _ from ht2.level)]
  simp only [typeof, cop]
  have hpl := hr0.ptnSmall (u - 1) (by omega)
  rw [ir_lt (a := (L.level : Int)) (b := (s0.ptn[u - 1]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  have hgt : s0.ptn[u - 1]! > L.level ↔ u - 1 + 1 < first + (last - first) :=
    cell_gt hcell (q := u - 1) (by omega) (by omega)
  rw [hlen] at hgt
  by_cases hul : u = last
  · subst hul
    rw [show decide ((L.level : Int) < (s0.ptn[u - 1]! : Int)) = false from
      decide_eq_false (by have := hgt.1; omega)]
    simp (config := {decide := true}) only [cop, ite_true, ite_false, Bool.not_false]
    have hsc : splitCounts L.level first d s = s.hash first := by
      rw [splitCounts_split, hlast, hu]; simp
    rw [hsc] at hQ
    simp only [ite_true] at hQ
    have hA : ∀ le', Tmp le' L s0 → (∀ x, x ∉ cellTemps → PTree.get x le' = PTree.get x le) →
        After L G (s.hash first) cellTemps le m le' m S :=
      fun le' ht' ho' => ⟨hm0, hr0, Frame.refl _ _, ht', hc0, fun x hx _ _ _ => ho' x hx⟩
    cases d
    · apply wp_continue
      exact hQ le2 m S (hA le2 ht2 fun x hx => ho2' x (hcut x hx).1 (hcut x hx).2.1) rfl rfl rfl rfl rfl rfl
        (fun h => absurd h (by decide))
    · wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hv22]
      apply wp_continue
      refine hQ _ m S (hA _ (ht2.set (x := id.«v1») _ (by decide)) fun x hx => ?_) rfl rfl rfl rfl rfl rfl
        (fun _ => by rw [temps_gss, ← hlast]; simp)
      rw [temps_gso _ _ (hcut x hx).2.2.1, ho2' x (hcut x hx).1 (hcut x hx).2.1]
  · rw [show decide ((L.level : Int) < (s0.ptn[u - 1]! : Int)) = true from
      decide_eq_true (by have := hgt.2 (by omega); omega)]
    simp (config := {decide := true}) only [cop, ite_false, ite_true]
    apply wp_skip
    have hne : s.hits[s.lab[u]!]! ≠ s.hits[s.lab[first]!]! := hu3.resolve_left hul
    have hmb := minima_bounds (N := n) (lab := s.lab) (hits := s.hits) hu1 (by omega) hkey' hne
    apply wp_seq
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, seqPost, after_E0, E0_append]
    let le3 := PTree.set id.«w2» (.Vint (Lib.Integers.Int.repr (zOfInt 2000000002))) le2
    have ht3 : Tmp le3 L s0 := ht2.set (x := id.«w2») _ (by decide)
    have hv23 : PTree.get id.«v2» le3 = some (.Vint (ir u)) := by
      rw [temps_gso _ _ (by decide)]; exact hv22
    apply wp_seq; apply wp_seq; apply wp_seq
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof]
    rw [temps_gso _ _ (show id.«v2» ≠ id.«w2» by decide), hv22]
    dsimp only
    rw [show Cfrontend.Cop.sem_cast (.Vint (ir u)) tint tint m = some (.Vint (ir u)) from rfl]
    simp only [seqPost, after_E0, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, seqPost, after_E0, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gso _ _ (show tc ≠ id.«j» from fun e => hT.htc.2.2.2 (by rw [e]; simp)),
      temps_gss, seqPost, after_E0, E0_append]
    let le5 := PTree.set id.«v3» (.Vint (ir u)) (PTree.set id.«j» (.Vint (ir u))
      (PTree.set tc (.Vint (ir u)) le3))
    have htc := hT.htc
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at htc
    have ho5 : ∀ x, x ≠ id.«v3» → x ≠ id.«j» → x ≠ tc → x ≠ id.«w2» →
        PTree.get x le5 = PTree.get x le2 := fun x a b c e => by
      rw [temps_gso _ _ a, temps_gso _ _ b, temps_gso _ _ c, temps_gso _ _ e]
    have ht5 : Tmp le5 L s0 :=
      ((ht3.set (x := tc) _ ⟨htc.1, htc.2.1, htc.2.2.1⟩).set (x := id.«j») _ (by decide)).set
        (x := id.«v3») _ (by decide)
    have hv15 : PTree.get id.«v1» le5 = some (.Vint (ir first)) := by
      rw [ho5 _ (by decide) (by decide) (Ne.symm htc.2.2.2.1) (by decide),
        ho2' _ (by decide) (Ne.symm hT.htr1)]; exact hv1
    have hw15 : PTree.get id.«w1» le5 = some (.Vint (ir s0.hits[s0.lab[first]!]!)) := by
      rw [ho5 _ (by decide) (by decide) (Ne.symm htc.2.2.2.2.2.1) (by decide),
        ho2' _ (by decide) (Ne.symm hT.htr.2.2.2.2)]; exact hw1
    have hv25 : PTree.get id.«v2» le5 = some (.Vint (ir u)) := by
      rw [ho5 _ (by decide) (by decide) (Ne.symm htc.2.2.2.2.1) (by decide)]; exact hv22
    have hw25 : PTree.get id.«w2» le5 = some (.Vint (ir 2000000002)) := by
      rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide),
        temps_gso _ _ (Ne.symm htc.2.2.2.2.2.2.1), temps_gss]
    apply wp_seq
    refine wp_min (t := s0) hT.htm hok hm0 hr0 ht5 hk hsz (begin := u) hu1 (by omega) hv15
      (by rw [temps_gso _ _ (by decide), temps_gss]) hv25 (temps_gss _ _ _) hw15 hw25 ?_
    intro le6 m6 hmin0
    simp only [seqPost, after_E0, E0_append]
    have hmin : MinAt L G s0 S first last tm le5 le6 m m6 last
        (Hex.GraphIso.Nauty.Sparse.CountSort.minima s.lab s.hits (n + 2) first last u) := by
      rw [hlen] at hmin0; exact hmin0
    generalize hst : Hex.GraphIso.Nauty.Sparse.CountSort.minima s.lab s.hits (n + 2) first last u = st
      at hmin hmb
    obtain ⟨W1, V2, W2, V3, lab'⟩ := st
    obtain ⟨hmb1, hmb2⟩ := hmb
    simp only at hmb1 hmb2
    have hlo := hmin.v2lo
    have hvv := hmin.v2v3
    have hW1 := hmin.w1
    simp only at hlo hvv hW1
    let t6 : RefineSt n := { s0 with lab := lab' }
    have ht6 : Tmp le6 L t6 := (ht5.frame hmin.temps (minTemps_ok hT.htm)).congr rfl rfl
    have hw6 : PTree.get (if d then id.«w2» else id.«w1») le6 =
        some (.Vint (ir ((if d then W2 else W1 : Nat) : Int))) := by
      cases d
      · exact hmin.tw1
      · have := hmin.tw2; simp only at this; rw [cw_of_lt hmb2] at this; exact this
    apply wp_seq
    wp_step; wp_step
    refine wp_mash (i := if d then W2 else W1) ht6.longcode hc0
      (show Exec.evalExpr sge empty_env le6 m6 (tv _) = _ from hw6) rfl
      (by cases d <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> omega) ?_
    simp only [seqPost, after_E0, E0_append]
    have ht7 := ht6.hash (if d then W2 else W1)
    have hv27 : PTree.get id.«v2» (PTree.set id.longcode
        (.Vlong (lr (Hex.GraphIso.Nauty.mash t6.longcode (if d then W2 else W1) : Nat))) le6) =
        some (.Vint (ir V2)) := by rw [temps_gso _ _ (by decide)]; exact hmin.tv2
    apply wp_seq
    wp_step; wp_step
    refine wp_mash ht7.longcode (Nat.lt_of_lt_of_le (NautyVerified.Proofs.Refine.mash_lt _ _) (by decide))
      (show Exec.evalExpr sge empty_env _ m6 (tv id.«v2») = _ from hv27) rfl (by omega) ?_
    simp only [seqPost, after_E0, E0_append]
    let t8 : RefineSt n := (t6.hash (if d then W2 else W1)).hash V2
    let le8 := PTree.set id.longcode (.Vlong (lr (Hex.GraphIso.Nauty.mash
      (t6.hash (if d then W2 else W1)).longcode V2 : Nat))) (PTree.set id.longcode
        (.Vlong (lr (Hex.GraphIso.Nauty.mash t6.longcode (if d then W2 else W1) : Nat))) le6)
    have ht8 : Tmp le8 L t8 := ht7.hash V2
    have ho8 : ∀ x, x ≠ id.longcode → PTree.get x le8 = PTree.get x le6 := fun x hx => by
      rw [temps_gso _ _ hx, temps_gso _ _ hx]
    have hsc : splitCounts L.level first d s = finRes L.level first last d t8 V2 V3 := by
      rw [splitCounts_split, hlast, hu, hst]
      simp only [show (u == last) = false from by simpa using hul, Bool.false_eq_true, ite_false]
      rw [finish_split]
      rfl
    have hvc := hv.counts first d (by rw [hlast]; exact hcell) hce hkey
    rw [hsc] at hvc hQ
    simp only [show ¬ (u = last) from hul, ite_false] at hQ
    have hlab8 : ∀ q < n, lab'[q]! < n := fun q hq => by
      by_cases hw : first ≤ q ∧ q < last
      · obtain ⟨q', -, hq2, e⟩ := hmin.win.inn q hw.1 hw.2
        rw [e]; exact hlabn q' (by omega)
      · rw [hmin.win.out q (by omega)]; exact hlabn q hq
    have hj6 : PTree.get id.«j» le8 = some (.Vint (ir last)) := by rw [ho8 _ (by decide)]; exact hmin.tj
    have hI : ∀ Q' : Post, (∀ le' m' S', After2 L G S m6 le8 (innerTemps t1 t2 t3 t4 t5 tv0 tv1)
        (finRes L.level first last d t8 V2 V3) le' m' S' → (finRes L.level first last d t8 V2 V3).longcode < 2 ^ 62 →
        Q'.normal E0 empty_env le' m') →
        Wp xi sge F (innerG d t1 t2 t3 t4 t5 (fragG d tv0 (runLoopG tv1))) Q' empty_env le8 m6 :=
      fun Q' hQ' => wp_inner (t := t8) hT.h1 hT.h2 hT.h3 hT.h4 hT.h5 hT.hfrag hT.hv1f hok
        (hmin.mem.congr rfl rfl rfl rfl) { hr0 with } ht8 hlo hvv hmb1 hlq hlab8 (hmin.win.size.trans hsz)
        hv.scratch.starts_size hv.size (Nat.lt_of_lt_of_le (NautyVerified.Proofs.Refine.mash_lt _ _) (by decide))
        hh (fun i hi => (hv.queue_cell hi).1) (queue_size_le hvc.1.queue.set)
        (fun q hq => Hex.GraphIso.Nauty.Sparse.perm_bound hvc.1.lab hq)
        (by rw [ho8 _ (by decide), hmin.temps _ (v1_not hT.htm)]; exact hv15)
        (by rw [ho8 _ (by decide)]; exact hmin.tv2) (by rw [ho8 _ (by decide)]; exact hmin.tv3) hj6 hQ'
    have hfin : ∀ le' m' S', After2 L G S m6 le8 (innerTemps t1 t2 t3 t4 t5 tv0 tv1)
        (finRes L.level first last d t8 V2 V3) le' m' S' → (finRes L.level first last d t8 V2 V3).longcode < 2 ^ 62 →
        After L G (finRes L.level first last d t8 V2 V3) cellTemps le m le' m' S' ∧ Keeps S S' :=
      fun le' m' S' ⟨hm', hr', ht', hf', hk', ho'⟩ hc' => ⟨⟨hm', hr', hmin.frame.trans hf', ht', hc',
        fun x hx _ h1 h2 => by
          rw [ho' x (fun hm => hin x (by simp [hm]) x hx rfl) h1 h2, ho8 x h1,
            hmin.temps x (fun hm => hin x (by simp [hm]) x hx rfl),
            ho5 x (hcut x hx).2.2.2.2.2.2 (hcut x hx).2.2.2.2.2.1 (hcut x hx).2.2.2.2.1 (hcut x hx).2.2.2.1,
            ho2' x (hcut x hx).1 (hcut x hx).2.1]⟩, hk'⟩
    cases d
    · wp_step; wp_step
      refine hI _ fun le' m' S' hA hc' => ?_
      obtain ⟨hA', hk'⟩ := hfin le' m' S' hA hc'
      exact hQ le' m' S' hA' hk'.w3 hk'.w4 hk'.st1 hk'.mk1 hk'.st2 hk'.mk2 (fun h => absurd h (by decide))
    · apply wp_seq
      wp_step; wp_step
      refine hI _ fun le' m' S' hA hc' => ?_
      obtain ⟨hA', hk'⟩ := hfin le' m' S' hA hc'
      simp only [seqPost, after_E0, E0_append]
      wp_step; wp_step
      apply wp_set_eval
      have hjn : id.«j» ∉ innerTemps t1 t2 t3 t4 t5 tv0 tv1 := by
        simp only [innerTemps, fragTemps, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, not_or]
        exact ⟨⟨by decide, hT.h1.ne' (by simp), hT.h2.ne' (by simp), hT.h3.ne' (by simp), hT.h4.ne' (by simp),
          hT.h5.ne' (by simp), by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
          by decide, fun h => hT.hfrag.b0 (by rw [← h]; simp), fun h => hT.hfrag.b1 (by rw [← h]; simp)⟩
      have hj' : PTree.get id.«j» le' = some (.Vint (ir last)) := by
        rw [hA.2.2.2.2.2 _ hjn (by decide) (by decide)]; exact hj6
      simp only [Exec.evalExpr, hj']
      refine hQ _ m' S' { hA' with
        tmp := hA'.tmp.set (x := id.«v1») _ (by decide)
        temps := fun x hx h0 h1 h2 => by
          rw [temps_gso _ _ (hcut x hx).2.2.1]; exact hA'.temps x hx h0 h1 h2 }
        hk'.w3 hk'.w4 hk'.st1 hk'.mk1 hk'.st2 hk'.mk2 (fun _ => by rw [temps_gss, ← hlast]; simp)

end NautyVerified.Proofs.Sparse.Refine.Count

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

/-- The count split of one cell, in both passes, computes `splitCounts`. -/
theorem countPass : CountPass (xi := xi) := by
  intro d n L G Q le m s S first hok hm hr ht hv hb hc hh hcell hlt hce hkey hv1 hw1 hQ
  cases d
  · show Wp xi sge F cellN Q empty_env le m
    rw [cellN_eq]
    exact wp_cellG ⟨by unfold TT; decide, by unfold TT; decide, by unfold TT; decide,
      by unfold TT; decide, by unfold TT; decide, ⟨by decide, by decide, by decide,
      by decide⟩, by decide, by decide, by decide, ⟨by decide, by decide⟩, by decide,
      fun x hx => by revert x; decide⟩ hok hm hr ht hv hb hc hh hcell hlt hce hkey hv1 hw1 hQ
  · show Wp xi sge F cellD Q empty_env le m
    rw [cellD_eq]
    exact wp_cellG ⟨by unfold TT; decide, by unfold TT; decide, by unfold TT; decide,
      by unfold TT; decide, by unfold TT; decide, ⟨by decide, by decide, by decide,
      by decide⟩, by decide, by decide, by decide, ⟨by decide, by decide⟩, by decide,
      fun x hx => by revert x; decide⟩ hok hm hr ht hv hb hc hh hcell hlt hce hkey hv1 hw1 hQ

end NautyVerified.Proofs.Sparse.Refine.Count

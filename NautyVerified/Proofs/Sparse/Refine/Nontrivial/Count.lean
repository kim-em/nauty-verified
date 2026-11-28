import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Edges

/-!
# The count loop of `refine_sg`'s nontrivial pass

`wp_countLoop`: `do { vi = v[lab[isplit]]; di = d[lab[isplit]]; ii = 0;
edgeLoopN } while (ptn[isplit++] > level);` over the splitter cell computes
the count phase `countPhase`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph CountScan)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {S : Scr}

/-- The temporaries the count loop assigns. -/
abbrev countTemps : List ident :=
  [id.«ii», id.«j», id.«k», id.«hitcells», idOf 751, idOf 752, id.«vi», id.«di», id.«isplit», idOf 750]

/-- The count state after the positions `[split, q)`. -/
def countTo (g : Graph n) (s : RefineSt n) (c0 : CS) (split q : Nat) : CS :=
  (List.range' split (q - split)).foldl (countVertex g s) c0

theorem countTo_succ (g : Graph n) (s : RefineSt n) (c0 : CS) {split q : Nat} (hq : split ≤ q) :
    countTo g s c0 split (q + 1) = countVertex g s (countTo g s c0 split q) q := by
  simp only [countTo]
  rw [show q + 1 - split = (q - split) + 1 by omega, List.range'_concat, List.foldl_append,
    Nat.one_mul, show split + (q - split) = q by omega]
  rfl

theorem wp_countLoop {Q : Post} {le : temp_env} {m : mem} {s : RefineSt n} {split len : Nat}
    (hok : Ok n L) (hm : Mem m L G s S) (hr : Rep L s S) (ht : Tmp le L s) (hv : s.Valid L.level)
    (hcr : CRep s S (s.marks, s.hits, #[]))
    (hc : IsCell s.ptn L.level split len) (hb : split + len ≤ n)
    (hi : PTree.get id.«isplit» le = some (.Vint (ir split)))
    (hhc : PTree.get id.«hitcells» le = some (.Vint (ir 0)))
    (hQ : ∀ le' m' S', Mem m' L G s S' → Rep L s S' → CRep s S' (countPhase (.ofGraph G) s split) →
      CountScan n s.stamp s.marks (countPhase (.ofGraph G) s split).1
        (countPhase (.ofGraph G) s split).2.2 s.cellstart (countPhase (.ofGraph G) s split).2.1
        (seenTo (.ofGraph G) s split (split + len) 0) →
      Frame L m m' →
      PTree.get id.«hitcells» le' = some (.Vint (ir (countPhase (.ofGraph G) s split).2.2.size)) →
      (∀ x, x ∉ countTemps → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F countLoop Q empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  have hlen := hc.1
  have he := hv.index.ends_eq split len hc hb (by omega)
  let c0 : CS := (s.marks, s.hits, #[])
  let e := split + len - 1
  have hcp : countPhase (.ofGraph G) s split = countTo (.ofGraph G) s c0 split (e + 1) := by
    simp only [countPhase, countTo, he, c0]; congr 2
  have hscan0 : CountScan n s.stamp s.marks c0.1 c0.2.2 s.cellstart c0.2.1
      (seenTo (.ofGraph G) s split split 0) := by
    have h0 : CountScan n s.stamp s.marks s.marks #[] s.cellstart s.hits [] :=
      CountScan.initial ⟨hv.scratch.marks_size, hv.scratch.marks_le⟩ hv.scratch.hits_size
    simpa [seenTo, c0] using h0
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q S', split ≤ q ∧ q ≤ e ∧ v = e - q ∧ Mem m' L G s S' ∧ Rep L s S' ∧
      CRep s S' (countTo (.ofGraph G) s c0 split q) ∧
      CountScan n s.stamp s.marks (countTo (.ofGraph G) s c0 split q).1
        (countTo (.ofGraph G) s c0 split q).2.2 s.cellstart (countTo (.ofGraph G) s c0 split q).2.1
        (seenTo (.ofGraph G) s split q 0) ∧
      Frame L m m' ∧ PTree.get id.«isplit» le' = some (.Vint (ir q)) ∧
      PTree.get id.«hitcells» le' = some (.Vint (ir (countTo (.ofGraph G) s c0 split q).2.2.size)) ∧
      ∀ x, x ∉ countTemps → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q S', split ≤ q ∧ q ≤ e ∧ v = e - q ∧ Mem m' L G s S' ∧ Rep L s S' ∧
      CRep s S' (countTo (.ofGraph G) s c0 split (q + 1)) ∧
      CountScan n s.stamp s.marks (countTo (.ofGraph G) s c0 split (q + 1)).1
        (countTo (.ofGraph G) s c0 split (q + 1)).2.2 s.cellstart
        (countTo (.ofGraph G) s c0 split (q + 1)).2.1 (seenTo (.ofGraph G) s split (q + 1) 0) ∧
      Frame L m m' ∧ PTree.get id.«isplit» le' = some (.Vint (ir q)) ∧
      PTree.get id.«hitcells» le' =
        some (.Vint (ir (countTo (.ofGraph G) s c0 split (q + 1)).2.2.size)) ∧
      ∀ x, x ∉ countTemps → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := e - split)
    ⟨rfl, rfl, split, S, Nat.le_refl _, by omega, rfl, hm, hr, by simpa [countTo] using hcr,
      by simpa [countTo] using hscan0, Frame.refl _ _, hi,
      by simpa [countTo, c0] using hhc,
      fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, q, S', hsq, hqe, rfl, hm', hr', hcr', hsc', hf, hiq, hhc', ho⟩
    have ht' := ht.frame ho (by decide)
    have hqn : q < n := by omega
    have hlq := Hex.GraphIso.Nauty.Sparse.perm_bound hv.lab hqn
    have hiqe : Exec.evalExpr sge empty_env le' m' (tv id.«isplit») = some (.Vint (ir q)) := hiq
    have hlab := eval_lab hok hm' ht' hiqe rfl hqn
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_idx (pe := .Etempvar id.«v» (tptr tulong)) hm'.graph.varr (by omega) ht'.v rfl rfl rfl
      _ _ hlq hlab rfl]
    let le1 := PTree.set id.«vi» (vVals G s.lab[q]!) le'
    wp_step; wp_step; wp_step
    apply wp_set_eval
    have ht1 : Tmp le1 L s := ht'.set _ (by decide)
    have hlab1 := eval_lab hok hm' ht1 (show Exec.evalExpr sge empty_env le1 m' (tv id.«isplit») = _ by
      simp only [Exec.evalExpr, le1]; rw [temps_gso _ _ (by decide)]; exact hiq) rfl hqn
    rw [eval_idx (pe := .Etempvar id.«d» (tptr tint)) hm'.graph.darr (by omega) ht1.d rfl rfl rfl
      _ _ hlq hlab1 rfl]
    let le2 := PTree.set id.«di» (dVals G s.lab[q]!) le1
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
    let le3 := PTree.set id.«ii» (.Vlong (lr 0)) le2
    have ht3 : Tmp le3 L s := (ht1.set _ (by decide)).set _ (by decide)
    have hg3 : ∀ x, x ≠ id.«ii» → x ≠ id.«di» → x ≠ id.«vi» → PTree.get x le3 = PTree.get x le' :=
      fun x h1 h2 h3 => by simp only [le3, le2, le1]; rw [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3]
    refine wp_edgeLoopN (split := split) (q := q) hok hm' hr' ht3 hv hcr' hsc' hqn hsq ?_ ?_ ?_ ?_ ?_
    · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]; rfl
    · rw [temps_gso _ _ (by decide), temps_gss]; rfl
    · exact temps_gss _ _ _
    · rw [hg3 _ (by decide) (by decide) (by decide)]; exact hhc'
    intro le4 m4 S4 hm4 hr4 hcr4 hsc4 hf4 hhc4 ho4
    refine ⟨by simp, rfl, q, S4, hsq, hqe, rfl, hm4, hr4, by rw [countTo_succ _ _ _ hsq]; exact hcr4,
      by rw [countTo_succ _ _ _ hsq]; exact hsc4, hf.trans hf4, ?_,
      by rw [countTo_succ _ _ _ hsq]; exact hhc4, fun x hx => ?_⟩
    · rw [ho4 _ (by decide), hg3 _ (by decide) (by decide) (by decide)]; exact hiq
    · rw [ho4 x (fun h => hx (by simp at h; rcases h with h | h | h | h | h | h <;> simp [h])), hg3 x (fun h => hx (by simp [h]))
        (fun h => hx (by simp [h])) (fun h => hx (by simp [h]))]
      exact ho x hx
  · rintro v tr e' le' m' ⟨rfl, rfl, q, S', hsq, hqe, rfl, hm', hr', hcr', hsc', hf, hiq, hhc', ho⟩
    have ht' := ht.frame ho (by decide)
    have hqn : q < n := by omega
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hiq]
    wp_step
    simp only [temps_gss, typeof, cop, ir_add]
    let le2 := PTree.set id.«isplit» (.Vint (ir ((q : Int) + 1))) (PTree.set (idOf 750) (.Vint (ir q)) le')
    have ho2 : ∀ x, x ∉ countTemps → PTree.get x le2 = PTree.get x le := fun x hx => by
      rw [temps_gso _ _ (fun h => hx (by simp [h])), temps_gso _ _ (fun h => hx (by simp [h])), ho x hx]
    have ht2 : Tmp le2 L s := ht.frame ho2 (by decide)
    apply wp_if_eval
    have h750 : Exec.evalExpr sge empty_env le2 m' (tv (idOf 750)) = some (.Vint (ir q)) := by
      simp only [Exec.evalExpr, le2]; rw [temps_gso _ _ (by decide), temps_gss]
    rw [eval_binop (eval_ptn hok hm' ht2 h750 rfl hqn)
      (show Exec.evalExpr sge empty_env le2 m' (tv id.«level») = _ from ht2.level)]
    simp only [typeof, cop]
    have hpl := hr'.ptnSmall q hqn
    rw [ir_lt (a := (L.level : Int)) (b := (s.ptn[q]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have hi2 : PTree.get id.«isplit» le2 = some (.Vint (ir ((q + 1 : Nat) : Int))) := by
      simp only [le2, temps_gss]; push_cast; rfl
    have hhc2 : PTree.get id.«hitcells» le2 = PTree.get id.«hitcells» le' := by
      simp only [le2]; rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]
    by_cases hqe' : q < e
    · rw [show decide ((L.level : Int) < (s.ptn[q]! : Int)) = true from
        decide_eq_true (by have := hc.2.2.1 q hsq (by omega); omega)]
      simp (config := {decide := true}) only [cop, ite_true]
      apply wp_skip
      exact ⟨e - (q + 1), by omega, by simp, rfl, q + 1, S', by omega, by omega, rfl, hm', hr', hcr',
        hsc', hf, hi2, hhc2.trans hhc', ho2⟩
    · have hqe2 : q = e := by omega
      rw [show decide ((L.level : Int) < (s.ptn[q]! : Int)) = false from
        decide_eq_false (by have := hc.2.2.2; rw [show split + len - 1 = q by omega] at this; omega)]
      simp (config := {decide := true}) only [cop, ite_false]
      apply wp_break
      have hq1 : q + 1 = split + len := by omega
      rw [hq1] at hcr' hsc' hhc'
      have hcp' : countPhase (.ofGraph G) s split = countTo (.ofGraph G) s c0 split (split + len) := by
        rw [hcp, show e + 1 = split + len by omega]
      exact hQ le2 m' S' hm' hr' (by rw [hcp']; exact hcr') (by rw [hcp']; exact hsc') hf
        (by rw [hhc2, hcp']; exact hhc') ho2

end NautyVerified.Proofs.Sparse.Refine.Nontrivial

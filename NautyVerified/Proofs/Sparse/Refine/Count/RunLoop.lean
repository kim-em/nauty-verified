import NautyVerified.Proofs.Sparse.Refine.Count.Store

/-!
# The run of a later fragment

`wp_runLoop`: `for (k = l; k < j-1 && HITS[lab[k+1]] == w3; ++k)
CELLSTART[lab[k+1]] = l;` computes `iterF (runStep l w3)` from `(t, l)`,
the loop of `fragStep`; only the cell starts change.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The run loop only writes cell starts. -/
theorem iterF_runStep (l w : Nat) : ∀ (F : Nat) (s : RefineSt n) (k : Nat),
    ∃ cs, (iterF (runStep l w) F (s, k)).1 = { s with cellstart := cs } ∧ cs.size = s.cellstart.size
  | 0, s, k => ⟨s.cellstart, rfl, rfl⟩
  | F + 1, s, k => by
    simp only [iterF, runStep]
    by_cases hc : (s.hits[s.lab[k + 1]!]! != w) = true
    · simp only [hc, ite_true]; exact ⟨s.cellstart, rfl, rfl⟩
    · simp only [hc, Bool.false_eq_true, ite_false]
      obtain ⟨cs, h1, h2⟩ := iterF_runStep l w F
        { s with cellstart := s.cellstart.set! s.lab[k + 1]! l } (k + 1)
      exact ⟨cs, h1, by rw [h2]; simp⟩

theorem wp_runLoop {Q : Post} {le : temp_env} {m : mem} {tv0 : ident} (htv : tv0 ∉ args ∧
    tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive ∧ tv0 ≠ id.«k» ∧ tv0 ≠ id.«j» ∧ tv0 ≠ id.«w3» ∧
      tv0 ≠ id.«l»)
    (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {l last w : Nat}
    (hlab : ∀ q < n, t.lab[q]! < n) (hhits : ∀ v < n, S.w3[v]! = t.hits[v]!)
    (hsz : t.cellstart.size = n) (hl : l + 1 ≤ last) (hlast : last ≤ n) (hwl : w < 2147483648)
    (hk0 : PTree.get id.«k» le = some (.Vint (ir l)))
    (hj : PTree.get id.«j» le = some (.Vint (ir last)))
    (hw : PTree.get id.«w3» le = some (.Vint (ir w)))
    (hll : PTree.get id.«l» le = some (.Vint (ir l)))
    (hQ : ∀ le' m' (S' : Scr), Mem m' L G (iterF (runStep l w) (last - 1 - l) (t, l)).1 S' →
      Rep L (iterF (runStep l w) (last - 1 - l) (t, l)).1 S' →
      S'.w2 = S.w2 → S'.w3 = S.w3 → S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 →
      S'.st2 = S.st2 → S'.mk2 = S.mk2 → S'.aw = S.aw → Frame L m m' →
      PTree.get id.«k» le' = some (.Vint (ir (iterF (runStep l w) (last - 1 - l) (t, l)).2)) →
      (∀ x, x ∉ [id.«k», tv0] → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (runLoopG tv0) Q empty_env le m := by
  have hnl := hok.nlt
  have hws : ∀ x ∈ [id.«k», tv0], x ∉ args ∧ x ≠ id.longcode ∧ x ≠ id.nactive := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact ⟨htv.1, htv.2.1, htv.2.2.1⟩
  let R := iterF (runStep l w) (last - 1 - l) (t, l)
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ k cs S', v = last - 1 - k ∧ l ≤ k ∧ k ≤ last - 1 ∧ cs.size = n ∧
      R = iterF (runStep l w) (last - 1 - k) ({ t with cellstart := cs }, k) ∧
      Mem m' L G { t with cellstart := cs } S' ∧ Rep L { t with cellstart := cs } S' ∧
      S'.w2 = S.w2 ∧ S'.w3 = S.w3 ∧ S'.w4 = S.w4 ∧ S'.st1 = S.st1 ∧ S'.mk1 = S.mk1 ∧
      S'.st2 = S.st2 ∧ S'.mk2 = S.mk2 ∧ S'.aw = S.aw ∧ Frame L m m' ∧
      PTree.get id.«k» le' = some (.Vint (ir k)) ∧
      ∀ x, x ∉ [id.«k», tv0] → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ k cs S', v = last - 1 - k ∧ l ≤ k ∧ k < last - 1 ∧ cs.size = n ∧
      R = iterF (runStep l w) (last - 1 - (k + 1)) ({ t with cellstart := cs }, k + 1) ∧
      Mem m' L G { t with cellstart := cs } S' ∧ Rep L { t with cellstart := cs } S' ∧
      S'.w2 = S.w2 ∧ S'.w3 = S.w3 ∧ S'.w4 = S.w4 ∧ S'.st1 = S.st1 ∧ S'.mk1 = S.mk1 ∧
      S'.st2 = S.st2 ∧ S'.mk2 = S.mk2 ∧ S'.aw = S.aw ∧ Frame L m m' ∧
      PTree.get id.«k» le' = some (.Vint (ir k)) ∧
      ∀ x, x ∉ [id.«k», tv0] → PTree.get x le' = PTree.get x le
  have hexit : ∀ k cs S' le' m', cs.size = n →
      R = ({ t with cellstart := cs }, k) → Mem m' L G { t with cellstart := cs } S' →
      Rep L { t with cellstart := cs } S' →
      S'.w2 = S.w2 → S'.w3 = S.w3 → S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 →
      S'.st2 = S.st2 → S'.mk2 = S.mk2 → S'.aw = S.aw → Frame L m m' →
      PTree.get id.«k» le' = some (.Vint (ir k)) →
      (∀ x, x ∉ [id.«k», tv0] → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m' := by
    intro k cs S' le' m' _ hR hm' hr' h2 h3 h4 h5 h6 h7 h8 h9 hf hk' ho
    refine hQ le' m' S' ?_ ?_ h2 h3 h4 h5 h6 h7 h8 h9 hf ?_ ho
    · show Mem m' L G R.1 S'; rw [hR]; exact hm'
    · show Rep L R.1 S'; rw [hR]; exact hr'
    · show PTree.get id.«k» le' = some (.Vint (ir R.2)); rw [hR]; exact hk'
  have ht0 : ({ t with cellstart := t.cellstart } : RefineSt n) = t := rfl
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := last - 1 - l)
    ⟨rfl, rfl, l, t.cellstart, S, rfl, Nat.le_refl _, by omega, hsz, by rw [ht0], by rw [ht0]; exact hm,
      by rw [ht0]; exact hr, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, hk0, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, k, cs, S', rfl, hk1, hk2, hcs, hR, hm', hr', h2, h3, h4, h5, h6, h7,
      h8, h9, hf, hkk, ho⟩
    let u : RefineSt n := { t with cellstart := cs }
    have ht' : Tmp le' L u := (ht.frame ho hws).congr rfl rfl
    have hnot : ∀ x, x ≠ id.«k» → x ≠ tv0 → x ∉ [id.«k», tv0] := fun x h1 h2 => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]; exact ⟨h1, h2⟩
    have hj' : PTree.get id.«j» le' = some (.Vint (ir last)) := by
      rw [ho _ (hnot _ (by decide) (fun h => htv.2.2.2.2.1 h.symm))]; exact hj
    have hw' : PTree.get id.«w3» le' = some (.Vint (ir w)) := by
      rw [ho _ (hnot _ (by decide) (fun h => htv.2.2.2.2.2.1 h.symm))]; exact hw
    have hl' : PTree.get id.«l» le' = some (.Vint (ir l)) := by
      rw [ho _ (hnot _ (by decide) (fun h => htv.2.2.2.2.2.2 h.symm))]; exact hll
    have hset : ∀ bv, (∀ x, x ∉ [id.«k», tv0] → PTree.get x (PTree.set tv0 bv le') = PTree.get x le) ∧
        PTree.get id.«k» (PTree.set tv0 bv le') = some (.Vint (ir k)) :=
      fun bv => ⟨fun x hx => by rw [temps_gso _ _ (fun h => hx (by simp [h]))]; exact ho x hx,
        by rw [temps_gso _ _ (fun h => htv.2.2.2.1 h.symm)]; exact hkk⟩
    wp_step; wp_step; wp_step; wp_step
    apply wp_if_eval
    have hsub : Exec.evalExpr sge empty_env le' m' (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) =
        some (.Vint (ir ((last - 1 : Nat) : Int))) := by
      simp only [Exec.evalExpr, hj', typeof, cop, ir_sub]
      congr 3; omega
    rw [eval_binop (show Exec.evalExpr sge empty_env le' m' (tv id.«k») = _ from hkk) hsub]
    simp only [typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := ((last - 1 : Nat) : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hkl : k < last - 1
    · rw [show decide ((k : Int) < ((last - 1 : Nat) : Int)) = true from decide_eq_true (by omega)]
      simp (config := {decide := true}) only [ite_true]
      wp_step; wp_step
      apply wp_set_eval
      have hadd : Exec.evalExpr sge empty_env le' m' (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint) =
          some (.Vint (ir ((k + 1 : Nat) : Int))) := by
        simp only [Exec.evalExpr, hkk, typeof, cop, ir_add]; rfl
      have hlk := hlab (k + 1) (by omega)
      have hkw := hr.w3small _ hlk
      rw [hhits _ hlk] at hkw
      have hb : Exec.evalExpr sge empty_env le' m' (.Ebinop .Oeq (gix id.«nausparse:work3»
          (ix id.lab (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint))) (tv id.«w3») tint) =
          some (Val.of_bool (decide (t.hits[t.lab[k + 1]!]! = w))) := by
        rw [eval_binop (eval_gw3 hok hm' (eval_lab hok hm' ht' hadd rfl (by omega)) rfl hlk)
          (show Exec.evalExpr sge empty_env le' m' (tv id.«w3») = _ from hw'), h3, hhits _ hlk]
        simp only [typeof, cop]
        rw [ir_eq (a := (t.hits[t.lab[k + 1]!]! : Int)) (b := (w : Int)) ⟨by omega, by omega⟩
          ⟨by omega, by omega⟩]
        congr 2
        exact decide_eq_decide.2 Int.ofNat_inj
      rw [eval_cast hb]
      simp only [typeof, cast_b]
      have hF : last - 1 - k = (last - 1 - (k + 1)) + 1 := by omega
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof]
      by_cases heq : t.hits[t.lab[k + 1]!]! = w
      · simp (config := {decide := true}) only [heq, decide_true, Val.of_bool, cop, ite_true]
        apply wp_skip
        wp_step; wp_step
        have hadd' : Exec.evalExpr sge empty_env (PTree.set tv0 Vtrue le') m'
            (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint) = some (.Vint (ir ((k + 1 : Nat) : Int))) := by
          simp only [Exec.evalExpr, (hset _).2, typeof, cop, ir_add]; rfl
        have ht2 := ht'.set (x := tv0) Vtrue ⟨htv.1, htv.2.1, htv.2.2.1⟩
        refine wp_w1F hok hm' (eval_lab hok hm' ht2 hadd' rfl (by omega)) rfl
          (show t.lab[k + 1]! < L.c1 by have := hok.c1; omega)
          (show Exec.evalExpr sge empty_env _ m' (tv id.«l») = _ by
            simp only [Exec.evalExpr]; rw [temps_gso _ _ (fun h => htv.2.2.2.2.2.2 h.symm)]; exact hl') rfl ?_
        intro m'' hm'' hf'
        refine ⟨by simp, rfl, k, cs.set! t.lab[k + 1]! l, _, rfl, hk1, hkl, by simp [hcs], ?_,
          hm''.congr rfl rfl rfl rfl, Rep.setStart hr' hcs (by omega), h2, h3, h4, h5, h6, h7, h8, h9,
          hf.trans hf', (hset _).2, (hset _).1⟩
        rw [hR, hF]
        simp only [iterF, runStep, heq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      · simp (config := {decide := true}) only [heq, decide_false, Val.of_bool, cop, ite_false]
        apply wp_break
        refine hexit k cs S' _ m' hcs ?_ hm' hr' h2 h3 h4 h5 h6 h7 h8 h9 hf (hset _).2 (hset _).1
        rw [hR, hF]
        simp only [iterF, runStep]
        rw [show (t.hits[t.lab[k + 1]!]! != w) = true by simpa using heq]
        rfl
    · rw [show decide ((k : Int) < ((last - 1 : Nat) : Int)) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [ite_false]
      wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp (config := {decide := true}) only [ite_false]
      apply wp_break
      refine hexit k cs S' _ m' hcs ?_ hm' hr' h2 h3 h4 h5 h6 h7 h8 h9 hf (hset _).2 (hset _).1
      rw [hR, show last - 1 - k = 0 by omega]; rfl
  · rintro v tr e' le' m' ⟨rfl, rfl, k, cs, S', rfl, hk1, hk2, hcs, hR, hm', hr', h2, h3, h4, h5, h6, h7,
      h8, h9, hf, hkk, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hkk, typeof, cop, ir_add]
    refine ⟨last - 1 - (k + 1), by omega, by simp, rfl, k + 1, cs, S', rfl, by omega, by omega, hcs, hR,
      hm', hr', h2, h3, h4, h5, h6, h7, h8, h9, hf, by simp, fun x hx => ?_⟩
    rw [temps_gso _ _ (fun h => hx (by simp [h])), ho x hx]

end NautyVerified.Proofs.Sparse.Refine.Count

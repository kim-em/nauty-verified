import NautyVerified.Proofs.Sparse.Refine.Trivial.Part

/-!
# The write-back of a touched cell's hit vertices

`revLoopT`: `while (--k >= 0) { j = HITS[k]; CELLSTART[j] = v2; lab[v3++] = j; }`
computes `revStep` over the hit vertices.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {u : RefineSt n} {S : Scr}

/-- The write-back after `q` vertices. -/
abbrev revAt (v2 : Nat) (hit lab starts : Array Nat) (q : Nat) : Array Nat × Array Nat × Nat :=
  (List.range' 0 q).foldl (revStep v2 hit) (lab, starts, v2)

theorem revAt_succ (v2 : Nat) (hit lab starts : Array Nat) (q : Nat) :
    revAt v2 hit lab starts (q + 1) = revStep v2 hit (revAt v2 hit lab starts q) q := by
  simp only [revAt, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Nat.one_mul, Nat.zero_add]

theorem revAt_inv (v2 : Nat) (hit lab starts : Array Nat) (hl : lab.size = n) (hs : starts.size = n) :
    ∀ q, (revAt v2 hit lab starts q).1.size = n ∧ (revAt v2 hit lab starts q).2.1.size = n ∧
      (revAt v2 hit lab starts q).2.2 = v2 + q
  | 0 => ⟨hl, hs, rfl⟩
  | q + 1 => by
    obtain ⟨h1, h2, h3⟩ := revAt_inv v2 hit lab starts hl hs q
    rw [revAt_succ]
    simp only [revStep, Array.size_set!, h1, h2, h3]
    exact ⟨True.intro, True.intro, by omega⟩

/-- The state after `q` vertices written back. -/
abbrev revSt (v2 : Nat) (hit : Array Nat) (u : RefineSt n) (q : Nat) : RefineSt n :=
  { u with lab := (revAt v2 hit u.lab u.cellstart q).1, cellstart := (revAt v2 hit u.lab u.cellstart q).2.1 }

/-- The temporaries the write-back assigns. -/
abbrev revTemps : List ident := [id.«k», id.«j», id.«v3», idOf 743, idOf 744]

theorem eval_dec {le : temp_env} {m : mem} {x : ident} {c : Int} (h : PTree.get x le = some (.Vint (ir c))) :
    Exec.evalExpr sge empty_env le m (.Ecast (.Ebinop .Osub (tv x) (ci 1 tint) tint) tint) =
      some (.Vint (ir (c - 1))) := by
  rw [Exec.evalExpr, eval_binop (eval_tv h) rfl]
  simp only [typeof, cop, ir_sub]

/-- `revLoopT` from `k = |hit|` and `v3 = v2`, `HITS[0..k)` holding `hit`. -/
theorem wp_revLoop {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G u S)
    (hr : Rep L u S) (ht : Tmp le L u) {v2 : Nat} {hit : Array Nat}
    (hw : ∀ i < hit.size, S.w3[i]! = hit[i]!) (hhit : ∀ i < hit.size, hit[i]! < n)
    (hv : v2 + hit.size ≤ n) (hls : u.lab.size = n) (hss : u.cellstart.size = n)
    (hk : PTree.get id.«k» le = some (.Vint (ir hit.size)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir v2)))
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir v2)))
    (hQ : ∀ le' m' (w1 : Nat → val),
      Mem m' L G (revSt v2 hit u hit.size) { S with w1 } →
      Rep L (revSt v2 hit u hit.size) { S with w1 } →
      Frame L m m' →
      PTree.get id.«v3» le' = some (.Vint (ir (v2 + hit.size))) →
      (∀ x, x ∉ revTemps → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F revLoopT Q empty_env le m := by
  have hnl := hok.nlt
  let U := revSt v2 hit u
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q w1, v = hit.size + 1 - q ∧ q ≤ hit.size ∧
      Mem m' L G (U q) { S with w1 } ∧ Rep L (U q) { S with w1 } ∧ Frame L m m' ∧
      PTree.get id.«k» le' = some (.Vint (ir ((hit.size : Int) - q))) ∧
      PTree.get id.«v3» le' = some (.Vint (ir (v2 + q))) ∧
      ∀ x, x ∉ revTemps → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q w1, v = hit.size + 2 - q ∧ 1 ≤ q ∧ q ≤ hit.size ∧
      Mem m' L G (U q) { S with w1 } ∧ Rep L (U q) { S with w1 } ∧ Frame L m m' ∧
      PTree.get id.«k» le' = some (.Vint (ir ((hit.size : Int) - q))) ∧
      PTree.get id.«v3» le' = some (.Vint (ir (v2 + q))) ∧
      ∀ x, x ∉ revTemps → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := hit.size + 1 - 0)
    ⟨rfl, rfl, 0, S.w1, rfl, Nat.zero_le _, hm, hr, Frame.refl _ _, by simpa using hk,
      by simpa using hv3, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, q, w1, rfl, hq, hm', hr', hf, hk', hv3', ho⟩
    have ht' : Tmp le' L (U q) := (ht.frame ho (by decide)).congr rfl rfl
    obtain ⟨i1, i2, i3⟩ := revAt_inv v2 hit u.lab u.cellstart hls hss q
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_dec hk']
    dsimp only
    apply wp_set_eval
    rw [eval_tv (temps_gss _ _ _)]
    dsimp only
    let le1 := PTree.set id.«k» (.Vint (ir ((hit.size : Int) - q - 1)))
      (PTree.set (idOf 743) (.Vint (ir ((hit.size : Int) - q - 1))) le')
    refine wp_if_ob (b := !decide ((hit.size : Int) - q - 1 < 0)) ?_ rfl ?_
    · rw [eval_binop (eval_tv (show PTree.get (idOf 743) le1 = _ by
        rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _)) rfl]
      simp only [typeof, cop]
      rw [ir_lt ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    · by_cases hqs : q < hit.size
      · simp only [show decide ((hit.size : Int) - q - 1 < 0) = false by simp; omega, Bool.not_false,
          ite_true]
        apply wp_skip
        simp only [E0_append]
        have hkv : PTree.get id.«k» le1 = some (.Vint (ir ((hit.size - 1 - q : Nat) : Int))) := by
          rw [temps_gss, show ((hit.size - 1 - q : Nat) : Int) = (hit.size : Int) - q - 1 by omega]
        have hjn : hit[hit.size - 1 - q]! < n := hhit _ (by omega)
        have hw' : w1 = w1 := rfl
        wp_step; wp_step; wp_step
        apply wp_set_eval
        rw [eval_gw3 hok hm' (eval_tv hkv) rfl (by omega)]
        dsimp only
        have hwv : S.w3[hit.size - 1 - q]! = hit[hit.size - 1 - q]! := hw _ (by omega)
        let le2 := PTree.set id.«j» (.Vint (ir (S.w3[hit.size - 1 - q]! : Int))) le1
        have hj2 : PTree.get id.«j» le2 = some (.Vint (ir (hit[hit.size - 1 - q]! : Int))) := by
          rw [temps_gss, hwv]
        have hv22 : PTree.get id.«v2» le2 = some (.Vint (ir v2)) := by
          rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide), ho _ (by decide)]
          exact hv2
        wp_step; wp_step; wp_step
        refine wp_w1 hok hm' (eval_tv hj2) rfl (by have := hok.c1; omega) (eval_tv hv22) rfl ?_
        intro m1 hm1 hf1
        wp_step; wp_step; wp_step; wp_step
        apply wp_set_eval
        rw [eval_tv (show PTree.get id.«v3» le2 = _ by
          rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hv3')]
        dsimp only
        apply wp_set_eval
        rw [eval_inc (temps_gss _ _ _)]
        dsimp only
        let le3 := PTree.set id.«v3» (.Vint (ir ((v2 : Int) + q + 1)))
          (PTree.set (idOf 744) (.Vint (ir ((v2 : Int) + q))) le2)
        have ht3 : Tmp le3 L (U q) :=
          ht'.frame (ws := revTemps) (fun x hx => by
            simp only [revTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
            rw [temps_gso _ _ hx.2.2.1, temps_gso _ _ hx.2.2.2.2, temps_gso _ _ hx.2.1,
              temps_gso _ _ hx.1, temps_gso _ _ hx.2.2.2.1]) (by decide)
        refine wp_lab hok hm1 ht3 (eval_tv (show PTree.get (idOf 744) le3 = some (.Vint (ir ((v2 + q : Nat) : Int))) by
          rw [temps_gso _ _ (by decide), temps_gss]; push_cast; rfl)) rfl (by omega)
          (eval_tv (show PTree.get id.«j» le3 = _ by
            rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj2)) rfl i1 ?_
        intro m2 hm2 hf2
        have hR : revAt v2 hit u.lab u.cellstart (q + 1) =
            ((revAt v2 hit u.lab u.cellstart q).1.set! (v2 + q) hit[hit.size - 1 - q]!,
              (revAt v2 hit u.lab u.cellstart q).2.1.set! hit[hit.size - 1 - q]! v2, v2 + q + 1) := by
          rw [revAt_succ]; simp only [revStep, i3]
        refine ⟨by simp, rfl, q + 1, upd w1 hit[hit.size - 1 - q]! (.Vint (ir v2)), by omega, by omega, hqs,
          ?_, ?_, hf.trans (hf1.trans hf2), ?_, ?_, ?_⟩
        · refine hm2.congr ?_ rfl rfl rfl
          simp only [U, hR]
        · refine ⟨fun x hx => ?_, hr'.queue, hr'.w3size, hr'.w3small, hr'.ptnSmall⟩
          simp only [U, hR]
          by_cases he : x = hit[hit.size - 1 - q]!
          · subst he; rw [upd_same, Array.getElem!_set!_self _ _ _ (by omega)]
          · rw [upd_ne _ _ he, Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]; exact hr'.starts x hx
        · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]
          rw [Int.natCast_add, Int.sub_sub]; rfl
        · rw [temps_gss]; push_cast; rfl
        · intro x hx
          simp only [revTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          rw [temps_gso _ _ hx.2.2.1, temps_gso _ _ hx.2.2.2.2, temps_gso _ _ hx.2.1,
            temps_gso _ _ hx.1, temps_gso _ _ hx.2.2.2.1]
          exact ho x (by simp [revTemps]; exact hx)
      · simp only [show decide ((hit.size : Int) - q - 1 < 0) = true by simp; omega, Bool.not_true,
          Bool.false_eq_true, ite_false]
        apply wp_break
        have hqe : q = hit.size := by omega
        subst hqe
        refine hQ le1 m' w1 hm' hr' hf ?_ ?_
        · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hv3'
        · intro x hx
          simp only [revTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.2.2.1]
          exact ho x (by simp [revTemps]; exact hx)
  · rintro v tr e' le' m' ⟨rfl, rfl, q, w1, rfl, hq1, hq, hm', hr', hf, hk', hv3', ho⟩
    apply wp_skip
    exact ⟨hit.size + 1 - q, by omega, by simp, rfl, q, w1, rfl, hq, hm', hr', hf, hk', hv3', ho⟩

end NautyVerified.Proofs.Sparse.Refine.Trivial

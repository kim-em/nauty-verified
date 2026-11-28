import NautyVerified.Proofs.Sparse.Refine.MainLoop

/-!
# The distance pass's cell loop

`for (v1 = 0; v1 < n; )`: a singleton cell is skipped, a nontrivial one is
hashed and split by `CountPass true` (`cellD`), and `v1` moves to the next
cell. `wp_distLoop` follows HexGraphIso's `Refinement.distance` as
`iterF (distStep level)` with HexGraphIso's `DistanceState` as the
invariant of the cells done so far.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph splitCounts DistanceState)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n}

/-- The temporaries the distance pass assigns. -/
def distTemps : List ident := cellTemps

theorem perm_bound' {level : Nat} {s : RefineSt n} (h : s.Valid level) {q : Nat} (hq : q < n) :
    s.lab[q]! < n := Hex.GraphIso.Nauty.Sparse.perm_bound h.lab hq

theorem iterF_dist_stop {level : Nat} {s : RefineSt n} {first : Nat} (h : n ≤ first) :
    ∀ F, iterF (distStep level) F (s, first) = (s, first)
  | 0 => rfl
  | F + 1 => by simp only [iterF, distStep, show first ≥ n from h, ite_true]

/-- The distance pass's invariant after the cells before `first`. -/
def DistInv (L : Loc) (G : Hex.SparseGraph n) (s0 res : RefineSt n) (m0 : mem) (le0 : temp_env)
    (first : Nat) (le : temp_env) (m : mem) : Prop :=
  ∃ s S F, DistanceState L.level s0 s first ∧ Mem m L G s S ∧ Rep L s S ∧
    (∀ v < n, S.w3[v]! = s.hits[v]!) ∧ Tmp le L s ∧ Budget L.level s ∧ s.longcode < 2 ^ 62 ∧
    Frame L m0 m ∧ n ≤ F + first ∧ res = (iterF (distStep L.level) F (s, first)).1 ∧
    PTree.get id.«v1» le = some (.Vint (ir first)) ∧
    ∀ x, x ∉ distTemps → x ∉ args → x ≠ id.longcode → x ≠ id.nactive →
      PTree.get x le = PTree.get x le0

theorem wp_distLoop (hC : CountPass (xi := xi)) {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    {s0 res : RefineSt n} (hv0 : s0.Valid L.level) (hd : ∀ v, v < n → s0.hits[v]! ≤ n)
    (h0 : DistInv L G s0 res m le 0 le m)
    (hQ : ∀ le' m' S, Mem m' L G res S → Rep L res S → (∀ v < n, S.w3[v]! = res.hits[v]!) →
      Tmp le' L res → DistanceState L.level s0 res n → Budget L.level res → res.longcode < 2 ^ 62 →
      Frame L m m' →
      (∀ x, x ∉ distTemps → x ∉ args → x ≠ id.longcode → x ≠ id.nactive →
        PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F distLoop Q empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ first, v = n - first ∧ DistInv L G s0 res m le first le' m'
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ first, n - first < v ∧ DistInv L G s0 res m le first le' m'
  rw [distLoop_eq]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0) ⟨rfl, rfl, 0, rfl, h0⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, first, rfl, s, S, F, hds, hm, hr, hh, ht, hb, hc, hf, hF, hres,
      hv1, ho⟩
    have hbd := hds.bound
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hv1, ht.n, typeof, cop]
    rw [ir_lt (a := (first : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hfn : first < n
    · rw [ite_eq_left (by simpa using hfn)]
      apply wp_skip
      simp only [E0_append]
      have hcell := hds.cell hfn
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hpf := hr.ptnSmall first hfn
      wp_step; wp_step; wp_step
      apply wp_if_eval
      rw [eval_binop (eval_ptn hok hm ht (show Exec.evalExpr sge empty_env le' m' (tv id.«v1») = _ from hv1)
        rfl hfn) (show Exec.evalExpr sge empty_env le' m' (tv id.«level») = _ from ht.level)]
      simp only [typeof, cop]
      rw [ir_lt (a := (L.level : Int)) (b := (s.ptn[first]! : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
      by_cases hsg : s.ptn[first]! ≤ L.level
      · rw [show decide ((L.level : Int) < (s.ptn[first]! : Int)) = false from decide_eq_false (by omega)]
        simp (config := {decide := true}) only [cop, ite_true]
        have he : s.cellend[first]! = first := by
          have hc1 := hcell.1
          rcases Nat.lt_or_ge (s.cellend[first]! + 1 - first) 2 with h | h
          · omega
          · exact absurd hsg (Nat.not_le.2 (hc1.2.2.1 first (Nat.le_refl _) (by omega)))
        wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, hv1, typeof, cop, ir_add]
        apply wp_continue
        refine ⟨by simp, rfl, first + 1, by omega, s, S, F', hds.singleton hfn he, hm, hr, hh,
          ht.set (x := id.«v1») _ (by decide), hb, hc, hf, by omega, ?_, by simp, fun x hx h1 h2 h3 => ?_⟩
        · rw [hres]; simp only [iterF, distStep, show ¬ first ≥ n by omega, ite_false, he,
            Nat.lt_irrefl, ite_false]
        · rw [temps_gso _ _ (by intro e; subst e; exact hx (by unfold distTemps cellTemps; decide)),
            ho x hx h1 h2 h3]
      · rw [show decide ((L.level : Int) < (s.ptn[first]! : Int)) = true from decide_eq_true (by omega)]
        simp (config := {decide := true}) only [cop, ite_false]
        apply wp_skip
        simp only [E0_append]
        have hlt : first < s.cellend[first]! := by
          have hc1 := hcell.1
          rcases Nat.lt_or_ge first s.cellend[first]! with h | h
          · exact h
          · exfalso
            have : s.cellend[first]! = first := by omega
            have hend := hc1.2.2.2
            rw [this, Nat.add_sub_cancel_left, Nat.add_sub_cancel] at hend
            exact hsg hend
        wp_step; wp_step; wp_step
        refine wp_mash ht.longcode hc (show Exec.evalExpr sge empty_env le' m' (tv id.«v1») = _ from hv1)
          rfl (by omega) ?_
        simp only [E0_append]
        have ht2 := ht.hash first
        have hlf := perm_bound' hds.valid hfn
        wp_step; wp_step; wp_step
        apply wp_set_eval
        have hv1' : Exec.evalExpr sge empty_env (PTree.set id.longcode
            (.Vlong (lr (Hex.GraphIso.Nauty.mash s.longcode first : Nat))) le') m' (tv id.«v1») =
            some (.Vint (ir first)) := by
          simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide)]; exact hv1
        rw [eval_gw3 hok hm (eval_lab hok (t := s.hash first) (hm.congr rfl rfl rfl rfl) ht2 hv1' rfl hfn) rfl hlf,
          hh (s.hash first).lab[first]! hlf]
        simp only [E0_append]
        have hkey : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2 := by
          intro q hq1 hq2
          have hq := perm_bound' hds.valid (show q < n by omega)
          rw [hds.hits]; have := hd _ hq; omega
        have hcs := hds.valid.counts first true hcell.1 hcell.2.2 hkey
        refine hC true hok hm hr (ht2.set (x := id.«w1») _ (by decide)) hds.valid hb hc hh hcell.1 hlt
          hcell.2.2 hkey (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hv1)
          (by rw [temps_gss]; rfl) ?_
        intro le3 m3 S3 ha hw3 _ _ _ _ _ hv13
        have hJ : J (n - first) E0 empty_env le3 m3 := by
          refine ⟨rfl, rfl, s.cellend[first]! + 1, by omega, splitCounts L.level first true s, S3, F',
            hds.counts hv0 hd hfn, ha.mem, ha.rep, ?_, ha.tmp, Budget.step hcs.2 hb, ha.code,
            hf.trans ha.frame, by omega, ?_, hv13 rfl, fun x hx h1 h2 h3 => ?_⟩
          · intro v hv
            rw [hw3, hh v hv, (Hex.GraphIso.Nauty.Sparse.splitCounts_frame L.level first true s).hits]
          · rw [hres]; simp only [iterF, distStep, show ¬ first ≥ n by omega, ite_false, hlt, ite_true]
          · rw [ha.temps x hx h1 h2 h3, temps_gso _ _ (by intro e; subst e; exact hx (by
              unfold distTemps cellTemps; decide)), temps_gso _ _ h2, ho x hx h1 h2 h3]
        split <;> exact hJ
    · rw [ite_eq_right (by simpa using hfn)]
      apply wp_break
      have hfe : first = n := by omega
      subst hfe
      rw [iterF_dist_stop (Nat.le_refl _)] at hres
      subst hres
      exact hQ le' m' S hm hr hh ht hds hb hc hf ho
  · rintro v tr e' le' m' ⟨rfl, rfl, first, hlt, hinv⟩
    apply wp_skip
    exact ⟨n - first, hlt, by simp, rfl, first, rfl, hinv⟩

end NautyVerified.Proofs.Sparse.Refine

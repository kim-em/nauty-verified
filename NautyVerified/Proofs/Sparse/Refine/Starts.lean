import NautyVerified.Proofs.Sparse.Refine.Wide
import NautyVerified.Proofs.Sparse.Refine.Select

/-!
# `CELLSTART`

`for (i = 0; i < n; )`: a singleton cell's vertex gets `n`, every vertex of
a nontrivial cell starting at `j` gets `j`. Since `lab` is a permutation,
every vertex is written, and the result is the cell index HexGraphIso's
`indexCells` builds (`Index.Valid`, whatever the indices held before):
`wp_startLoop`.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph perm_bound perm_injective)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n}

theorem perm_surj {lab : Array Nat} (h : lab.toList.Perm (List.range n)) {v : Nat} (hv : v < n) :
    ∃ j < n, lab[j]! = v := by
  have hs : lab.size = n := by simpa using h.length_eq
  have hm : v ∈ lab.toList := h.mem_iff.mpr (List.mem_range.mpr hv)
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨j, by simpa [hs] using hj, ?_⟩
  rw [getElem!_pos lab j (by simpa using hj)]
  simpa using he

/-- The temporaries the `CELLSTART` loop assigns. -/
def startTemps : List ident := [id.«i», id.«j», idOf 714]

/-- `CELLSTART` holds `t`'s cell starts at the vertices of positions below `k`. -/
def Written (t : RefineSt n) (S : Scr) (k : Nat) : Prop :=
  ∀ j < k, S.w1 t.lab[j]! = .Vint (ir t.cellstart[t.lab[j]!]!)

/-- The loop's invariant at the cell starting at `first`. -/
def StartInv (L : Loc) (G : Hex.SparseGraph n) (t : RefineSt n) (S : Scr) (m0 : mem)
    (le0 : temp_env) (first : Nat) (le : temp_env) (m : mem) : Prop :=
  ∃ S', Mem m L G t S' ∧ Written t S' first ∧ S'.w2 = S.w2 ∧ S'.w3 = S.w3 ∧ Tmp le L t ∧
    first ≤ n ∧ (first = 0 ∨ t.ptn[first - 1]! ≤ L.level) ∧ Unch m0 m (· = L.b1) ∧
    (∀ z, Mem.valid_block m0 z → Mem.valid_block m z) ∧
    PTree.get id.«i» le = some (.Vint (ir first)) ∧
    ∀ x, x ∉ startTemps → PTree.get x le = PTree.get x le0

theorem Written.store {t : RefineSt n} {S : Scr} {k : Nat} (hv : t.Valid L.level) (hw : Written t S k)
    (hk : k < n) {x : Nat} (hx : t.cellstart[t.lab[k]!]! = x) :
    Written t { S with w1 := upd S.w1 t.lab[k]! (.Vint (ir x)) } (k + 1) := by
  intro j hj
  show upd S.w1 t.lab[k]! _ t.lab[j]! = _
  by_cases he : j = k
  · subst he; rw [upd_same, hx]
  · rw [upd_ne _ _ (fun e => he (perm_injective hv.lab (by omega) hk e)), hw j (by omega)]

/-- The cell start of every vertex of the cell at `first`. -/
theorem starts_cell {t : RefineSt n} (hv : t.Valid L.level) {first : Nat} (hf : first < n)
    (hstart : first = 0 ∨ t.ptn[first - 1]! ≤ L.level) {j : Nat} (h1 : first ≤ j)
    (h2 : j ≤ t.cellend[first]!) :
    t.cellstart[t.lab[j]!]! = if first < t.cellend[first]! then first else n := by
  obtain ⟨hcell, hle, hlt⟩ := hv.cell hf hstart
  rw [hv.index.starts_eq first _ hcell (by omega) hf j h1 (by omega)]
  by_cases h : first < t.cellend[first]!
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]

theorem wp_startLoop {Q : Post} {le : temp_env} {m : mem} {t : RefineSt n} {S : Scr} (hok : Ok n L)
    (hm : Mem m L G t S) (ht : Tmp le L t) (hv : t.Valid L.level)
    (hps : ∀ i < n, t.ptn[i]! < 2147483648)
    (hi : PTree.get id.«i» le = some (.Vint (ir 0)))
    (hQ : ∀ le' m' S', Mem m' L G t S' → (∀ v < n, S'.w1 v = .Vint (ir t.cellstart[v]!)) →
      S'.w2 = S.w2 → S'.w3 = S.w3 → Tmp le' L t → Unch m m' (· = L.b1) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ∉ startTemps → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F startLoop Q empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  have hc1 := hok.c1
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ first, v = n - first ∧ StartInv L G t S m le first le' m'
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ first, n - first < v ∧ StartInv L G t S m le first le' m'
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0)
    ⟨rfl, rfl, 0, rfl, S, hm, fun j hj => absurd hj (by omega), rfl, rfl, ht, by omega, .inl rfl,
      Unch.refl _ _, fun _ h => h, hi, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, first, rfl, S', hm', hw, hw2, hw3, ht', hfn, hstart, hu', hg', hi',
      ho'⟩
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hi', ht'.n, typeof, cop]
    rw [ir_lt (a := (first : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hf : first < n
    · rw [ite_eq_left (by simpa using hf)]
      apply wp_skip
      simp only [E0_append]
      obtain ⟨hcell, hle, hlt⟩ := hv.cell hf hstart
      have hpf := hps first hf
      wp_step; wp_step
      apply wp_if_eval
      rw [eval_binop (eval_ptn hok hm' ht' (show Exec.evalExpr sge empty_env le' m' (tv id.«i») = _
        from hi') rfl hf) (show Exec.evalExpr sge empty_env le' m' (tv id.«level») = _ from ht'.level)]
      simp only [typeof, cop]
      rw [ir_lt (a := (L.level : Int)) (b := (t.ptn[first]! : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
      have hlf := perm_bound hv.lab hf
      have hlab : Exec.evalExpr sge empty_env le' m' (ix id.lab (tv id.«i»)) =
          some (.Vint (ir t.lab[first]!)) :=
        eval_lab hok hm' ht' (show Exec.evalExpr sge empty_env le' m' (tv id.«i») = _ from hi') rfl hf
      by_cases hsg : t.ptn[first]! ≤ L.level
      · rw [show decide ((L.level : Int) < (t.ptn[first]! : Int)) = false from decide_eq_false (by omega)]
        simp (config := {decide := true}) only [ite_true]
        have he : t.cellend[first]! = first := by
          rcases Nat.lt_or_ge (t.cellend[first]! + 1 - first) 2 with h | h
          · omega
          · exact absurd hsg (Nat.not_le.2 (hcell.2.2.1 first (Nat.le_refl _) (by omega)))
        wp_step; wp_step; wp_step
        refine wp_storeW1 (c := t.lab[first]!) (x := n) hok hm' hlab rfl (by omega) ht'.n rfl ?_
        intro m2 hm2 hu2 hg2
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, hi', typeof, cop, ir_add]
        have hw' := hw.store hv hf (x := n) (by rw [starts_cell hv hf hstart (Nat.le_refl _) (by omega)]; simp [he])
        exact ⟨by simp, rfl, first + 1, by omega, _, hm2, hw', hw2, hw3,
          ht'.set (x := id.«i») _ (by decide), by omega, .inr (by simpa using hsg), hu'.trans hu2,
          fun z h => hg2 _ (hg' _ h), by rw [temps_gss]; push_cast; rfl,
          fun x hx => by rw [temps_gso _ _ (by intro e; subst e; exact hx (by simp [startTemps])), ho' x hx]⟩
      · rw [show decide ((L.level : Int) < (t.ptn[first]! : Int)) = true from decide_eq_true (by omega)]
        simp (config := {decide := true}) only [ite_false]
        have hnt : first < t.cellend[first]! := by
          rcases Nat.lt_or_ge first t.cellend[first]! with h | h
          · exact h
          · exfalso
            have : t.cellend[first]! = first := by omega
            have hend := hcell.2.2.2
            rw [this, Nat.add_sub_cancel_left, Nat.add_sub_cancel] at hend
            exact hsg hend
        let last := t.cellend[first]!
        wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, hi']
        let le1 := PTree.set id.«j» (.Vint (ir first)) le'
        have ht1 : Tmp le1 L t := ht'.set _ (by decide)
        let In := fun (k : Nat) (le2 : temp_env) (m2 : mem) => ∃ S2, Mem m2 L G t S2 ∧ Written t S2 k ∧
          S2.w2 = S.w2 ∧ S2.w3 = S.w3 ∧ Tmp le2 L t ∧ Unch m m2 (· = L.b1) ∧
          (∀ z, Mem.valid_block m z → Mem.valid_block m2 z) ∧
          PTree.get id.«j» le2 = some (.Vint (ir first)) ∧
          ∀ x, x ∉ startTemps → PTree.get x le2 = PTree.get x le
        let I2 := fun (v : Nat) (tr : trace) (e' : env) (le2 : temp_env) (m2 : mem) => tr = E0 ∧
          e' = empty_env ∧ ∃ k, v = last - k ∧ first ≤ k ∧ k ≤ last ∧
            PTree.get id.«i» le2 = some (.Vint (ir k)) ∧ In k le2 m2
        let J2 := fun (v : Nat) (tr : trace) (e' : env) (le2 : temp_env) (m2 : mem) => tr = E0 ∧
          e' = empty_env ∧ ∃ k, v = last - k ∧ first ≤ k ∧ k ≤ last ∧
            PTree.get id.«i» le2 = some (.Vint (ir k)) ∧ In (k + 1) le2 m2
        refine wp_loop (I := I2) (J := J2) ?_ ?_ (n := last - first)
          ⟨rfl, rfl, first, rfl, Nat.le_refl _, by omega, by rw [temps_gso _ _ (by decide)]; exact hi',
            S', hm', hw, hw2, hw3, ht1, hu', hg', temps_gss _ _ _,
            fun x hx => by rw [temps_gso _ _ (by intro e; subst e; exact hx (by simp [startTemps])), ho' x hx]⟩
        · rintro v2 tr e2 le2 m2 ⟨rfl, rfl, k, rfl, hk1, hk2, hik, S2, hm2, hw', hw2', hw3', ht2, hu2, hg2,
            hj2, ho2⟩
          have hkn : k < n := by omega
          wp_step; wp_step
          refine wp_storeW1 (c := t.lab[k]!) (x := first) hok hm2
            (eval_lab hok hm2 ht2 (show Exec.evalExpr sge empty_env le2 m2 (tv id.«i») = _ from hik) rfl hkn)
            rfl (by have := perm_bound hv.lab hkn; omega)
            (show Exec.evalExpr sge empty_env le2 m2 (tv id.«j») = _ from hj2) rfl ?_
          intro m3 hm3 hu3 hg3
          exact ⟨by simp, rfl, k, rfl, hk1, hk2, hik, _, hm3,
            hw'.store hv hkn (by rw [starts_cell hv hf hstart hk1 hk2, if_pos hnt]), hw2', hw3', ht2,
            hu2.trans hu3, fun z h => hg3 _ (hg2 _ h), hj2, ho2⟩
        · rintro v2 tr e2 le2 m2 ⟨rfl, rfl, k, rfl, hk1, hk2, hik, S2, hm2, hw', hw2', hw3', ht2, hu2, hg2,
            hj2, ho2⟩
          have hkn : k < n := by omega
          wp_step; wp_step; wp_step; wp_step
          apply wp_set_eval
          simp only [Exec.evalExpr, hik]
          apply wp_set_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]
          have ht3 := (ht2.set (x := idOf 714) (.Vint (ir k)) (by decide)).set (x := id.«i»)
            (.Vint (ir ((k : Int) + 1))) (by decide)
          apply wp_if_eval
          have hpk := hps k hkn
          rw [eval_binop (eval_ptn hok hm2 ht3 (c := k) (by simp (config := {decide := true}) only
            [Exec.evalExpr, temps_gso, temps_gss]) rfl hkn)
            (show Exec.evalExpr sge empty_env _ m2 (tv id.«level») = _ from ht3.level)]
          simp only [typeof, cop]
          rw [ir_lt (a := (L.level : Int)) (b := (t.ptn[k]! : Int)) ⟨by omega, by omega⟩
            ⟨by omega, by omega⟩]
          have ho3 : ∀ x, x ∉ startTemps → PTree.get x (PTree.set id.«i» (.Vint (ir ((k : Int) + 1)))
              (PTree.set (idOf 714) (.Vint (ir k)) le2)) = PTree.get x le := fun x hx => by
            simp only [startTemps, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
            rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.2, ho2 x (by simp [startTemps, hx.1, hx.2.1, hx.2.2])]
          by_cases hgt : L.level < t.ptn[k]!
          · rw [show decide ((L.level : Int) < (t.ptn[k]! : Int)) = true from decide_eq_true (by omega)]
            simp (config := {decide := true}) only [ite_true]
            apply wp_skip
            have hkl : k < last := by
              rcases Nat.lt_or_ge k last with h | h
              · exact h
              · have : k = last := by omega
                have hend := hcell.2.2.2
                rw [show first + (t.cellend[first]! + 1 - first) - 1 = last by omega, ← this] at hend
                omega
            exact ⟨last - (k + 1), by omega, by simp, rfl, k + 1, rfl, by omega, by omega,
              by rw [temps_gss]; push_cast; rfl, S2, hm2, hw', hw2', hw3', ht3, hu2, hg2,
              by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj2, ho3⟩
          · rw [show decide ((L.level : Int) < (t.ptn[k]! : Int)) = false from decide_eq_false (by omega)]
            simp (config := {decide := true}) only [Bool.false_eq_true, ite_false]
            apply wp_break
            have hkl : k = last := by
              rcases Nat.lt_or_ge k last with h | h
              · exact absurd (hcell.2.2.1 k hk1 (by omega)) (by omega)
              · omega
            exact ⟨by simp, rfl, last + 1, by omega, S2, hm2, hkl ▸ hw', hw2', hw3', ht3, by omega,
              .inr (by simpa [Nat.add_sub_cancel] using (hkl ▸ (Nat.not_lt.1 hgt))), hu2, hg2,
              by rw [temps_gss, hkl]; push_cast; rfl, ho3⟩
    · rw [ite_eq_right (by simpa using hf)]
      apply wp_break
      have hfe : first = n := by omega
      subst hfe
      refine hQ le' m' S' hm' (fun v hv' => ?_) hw2 hw3 ht' hu' hg' ho'
      obtain ⟨j, hj, rfl⟩ := perm_surj hv.lab hv'
      exact hw j hj
  · rintro v tr e' le' m' ⟨rfl, rfl, first, hlt, hinv⟩
    apply wp_skip
    exact ⟨n - first, hlt, by simp, rfl, first, rfl, hinv⟩

end NautyVerified.Proofs.Sparse.Refine

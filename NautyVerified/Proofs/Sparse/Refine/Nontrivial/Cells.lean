import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Sort

/-!
# The touched-cell loop of `refine_sg`'s nontrivial pass

`wp_cellLoopN`:
`for (i = 0; i < hitcells; ++i) { v1 = HITCELL[i]; w1 = HITS[lab[v1]];
MASH(v1); cellN }` over the sorted touched starts `l` folds `splitCounts`
over `l` (the fold of `splitNontrivial_eq`).
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph splitCounts)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

/-- The touched-cell fold after `k` starts of `l`. -/
def foldTo {n : Nat} (level : Nat) (l : List Nat) (b : RefineSt n) (k : Nat) : RefineSt n :=
  (l.take k).foldl (fun t first => splitCounts level first false t) b

theorem foldTo_succ {n : Nat} (level : Nat) (l : List Nat) (b : RefineSt n) {k : Nat}
    (hk : k < l.length) :
    foldTo level l b (k + 1) = splitCounts level l[k] false (foldTo level l b k) := by
  simp only [foldTo, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem drop_eq_cons {l : List Nat} {k : Nat} (hk : k < l.length) : l.drop k = l[k] :: l.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons hk]

/-- The loop over the sorted touched starts `l`, from the state `b0` after the
count phase. -/
theorem wp_cellLoopN (hc : CountPass (xi := xi)) {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {S : Scr}
    {Q : Post} {le : temp_env} {m : mem} {b0 : RefineSt n} {l : List Nat} {lenB : Nat}
    {ends : Array Nat}
    (hok : Ok n L) (hm : Mem m L G b0 S) (hr : Rep L b0 S) (ht : Tmp le L b0)
    (hF : Fold L.level lenB ends b0 b0 l) (hlenB : lenB ≤ n) (hbud : Budget L.level b0)
    (hcode : b0.longcode < 2 ^ 62) (hhits : ∀ v < n, S.w3[v]! = b0.hits[v]!)
    (hw4 : ∀ i < l.length, S.w4 i = .Vint (ir l[i]!)) (hl : l.length ≤ n)
    (hi : PTree.get id.«i» le = some (.Vint (ir 0)))
    (hhc : PTree.get id.«hitcells» le = some (.Vint (ir l.length)))
    (hQ : ∀ le' m' S', After L G (foldTo L.level l b0 l.length) passTemps le m le' m' S' →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F cellLoopN Q empty_env le m := by
  have hnl := hok.nlt
  have hc4 := hok.c4
  have hv0 := hF.valid
  let b := foldTo L.level l b0
  let Inv (k : Nat) (le' : temp_env) (m' : mem) : Prop :=
    ∃ S', Mem m' L G (b k) S' ∧ Rep L (b k) S' ∧ S'.w3 = S.w3 ∧ S'.w4 = S.w4 ∧
      Fold L.level lenB ends b0 (b k) (l.drop k) ∧ Budget L.level (b k) ∧ (b k).longcode < 2 ^ 62 ∧
      Frame L m m' ∧ Tmp le' L (b k) ∧ PTree.get id.«hitcells» le' = some (.Vint (ir l.length)) ∧
      ∀ x, x ∉ passTemps → x ∉ args → x ≠ id.longcode → x ≠ id.nactive →
        PTree.get x le' = PTree.get x le
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ k, k ≤ l.length ∧ v = l.length - k ∧ Inv k le' m' ∧
      PTree.get id.«i» le' = some (.Vint (ir k))
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ k, k < l.length ∧ v = l.length - k ∧ Inv (k + 1) le' m' ∧
      PTree.get id.«i» le' = some (.Vint (ir k))
  rw [cellLoopN_eq]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := l.length - 0)
    ⟨rfl, rfl, 0, Nat.zero_le _, rfl, ⟨S, by simpa [b, foldTo] using hm, by simpa [b, foldTo] using hr,
      rfl, rfl, by simpa [b, foldTo] using hF, by simpa [b, foldTo] using hbud,
      by simpa [b, foldTo] using hcode, Frame.refl _ _, by simpa [b, foldTo] using ht, hhc,
      fun _ _ _ _ _ => rfl⟩, hi⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, k, hk, rfl, ⟨S', hm', hr', h3, h4, hF', hbud', hcode', hf, ht', hhc',
      ho⟩, hik⟩
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hik, hhc', typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := (l.length : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hkl : k < l.length
    · rw [ite_eq_left (by simpa using hkl)]
      apply wp_skip
      have hfo := hF'
      rw [drop_eq_cons hkl] at hfo
      obtain ⟨he, hcl, hlt, hbn, hkey⟩ := hfo.head
      have hfirst : l[k]! = l[k] := getElem!_pos l k hkl
      have hfn : l[k] < n := by
        have h5 := (hfo.cells l[k] List.mem_cons_self).2.1; have h6 := (hfo.cells l[k] List.mem_cons_self).2.2.1; omega
      have hvk := (hfo.valid)
      have hlf := Hex.GraphIso.Nauty.Sparse.perm_bound hvk.lab hfn
      have hbh : (b k).hits = b0.hits := hfo.hits
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_gw4 hok hm' (show Exec.evalExpr sge empty_env le' m' (tv id.«i») = _ from hik) rfl
        (by omega), h4, hw4 k hkl, hfirst]
      let le1 := PTree.set id.«v1» (.Vint (ir l[k])) le'
      have ht1 : Tmp le1 L (b k) := ht'.set _ (by decide)
      have hv1 : Exec.evalExpr sge empty_env le1 m' (tv id.«v1») = some (.Vint (ir l[k])) := by
        simp only [Exec.evalExpr, le1, temps_gss]
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_gw3 hok hm' (eval_lab hok hm' ht1 hv1 rfl hfn) rfl hlf, h3, hhits _ hlf, ← hbh]
      let le2 := PTree.set id.«w1» (.Vint (ir (b k).hits[(b k).lab[l[k]]!]!)) le1
      have ht2 : Tmp le2 L (b k) := ht1.set _ (by decide)
      wp_step; wp_step; wp_step
      refine wp_mash ht2.longcode hcode' (show Exec.evalExpr sge empty_env le2 m' (tv id.«v1») = _ by
        simp only [Exec.evalExpr, le2]; rw [temps_gso _ _ (by decide)]; exact hv1) rfl (by omega) ?_
      have ht3 := ht2.hash l[k]
      let le3 := PTree.set id.longcode (.Vlong (lr (Hex.GraphIso.Nauty.mash (b k).longcode l[k] : Nat))) le2
      have hg3 : ∀ x, x ≠ id.longcode → x ≠ id.«w1» → x ≠ id.«v1» → PTree.get x le3 = PTree.get x le' :=
        fun x h1 h2 h3 => by
          simp only [le3, le2, le1]; rw [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3]
      have hb1 : b (k + 1) = splitCounts L.level l[k] false (b k) := foldTo_succ _ _ _ hkl
      have hFn := hfo.next hv0 hlenB
      refine hc false hok hm' hr' ht3 hvk hbud' hcode' (fun v hv => by rw [h3, hhits v hv, hbh])
        hcl hlt hbn (fun q h1 h2 => by have := hkey q h1 h2; omega) ?_ ?_ ?_
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]
        exact hv1
      · rw [temps_gso _ _ (by decide), temps_gss]
      intro le4 m4 S4 hA h3'' h4'' _ _ _ _ _
      have hsub : ∀ x, x ∉ passTemps → x ∉ cellTemps := fun x hx h => hx (by
        unfold passTemps; exact List.mem_append_left _ (List.mem_append_left _ h))
      have hinv : Inv (k + 1) le4 m4 := by
        refine ⟨S4, ?_, ?_, h3''.trans h3, h4''.trans h4, ?_, ?_, ?_, hf.trans hA.frame, ?_, ?_, ?_⟩
        · rw [hb1]; exact hA.mem
        · rw [hb1]; exact hA.rep
        · rw [hb1]; exact hFn
        · rw [hb1]; exact Budget.step hFn.step hbud
        · rw [hb1]; exact hA.code
        · rw [hb1]; exact hA.tmp
        · rw [hA.temps _ (by decide) (by decide) (by decide) (by decide),
            hg3 _ (by decide) (by decide) (by decide)]; exact hhc'
        · intro x hx h1 h2 h3'
          rw [hA.temps x (hsub x hx) h1 h2 h3', hg3 x h2 (fun h => hx (by simp [h, passTemps, cellTemps]))
            (fun h => hx (by simp [h, passTemps, cellTemps]))]
          exact ho x hx h1 h2 h3'
      have hi4 : PTree.get id.«i» le4 = some (.Vint (ir k)) := by
        rw [hA.temps _ (by decide) (by decide) (by decide) (by decide),
          hg3 _ (by decide) (by decide) (by decide)]; exact hik
      split
      · exact ⟨by simp, rfl, k, hkl, rfl, hinv, hi4⟩
      · exact ⟨by simp, rfl, k, hkl, rfl, hinv, hi4⟩
    · rw [ite_eq_right (by simpa using hkl)]
      apply wp_break
      have hkl' : k = l.length := by omega
      subst hkl'
      exact hQ le' m' S' ⟨hm', hr', hf, ht', hcode', ho⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, k, hk, rfl, hinv, hik⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hik, typeof, cop, ir_add]
    obtain ⟨S', hm', hr', h3, h4, hF', hbud', hcode', hf, ht', hhc', ho⟩ := hinv
    refine ⟨l.length - (k + 1), by omega, by simp, rfl, k + 1, by omega, rfl,
      ⟨S', hm', hr', h3, h4, hF', hbud', hcode', hf, ht'.set _ (by decide), ?_, fun x hx => ?_⟩, ?_⟩
    · rw [temps_gso _ _ (by decide)]; exact hhc'
    · intro h1 h2 h3
      rw [temps_gso _ _ (fun h => hx (by simp [h, passTemps])), ho x hx h1 h2 h3]
    · simp only [temps_gss]; push_cast; rfl

end NautyVerified.Proofs.Sparse.Refine.Nontrivial

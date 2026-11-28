import HexGraphIso.Nauty.Sparse.GraphProps
import Std.Tactic.Do

/-!
# HexGraphIso's `Sparse.isautom`, row by row

`isautom_rows`: `Sparse.isautom (ofGraph G) p` accepts exactly when every
moved vertex `i` has the degree of `p[i]` and every neighbour of `p[i]` is
the image under `p` of a neighbour of `i`. This is the form `isautom_sg`'s
loops establish. The statement and proof are HexGraphIso's (the lemma is
private there, in `HexGraphIso/Nauty/Sparse/Autom.lean`).
-/

namespace NautyVerified.Proofs.Sparse

open Std.Do
open Hex.GraphIso.Nauty.Sparse
set_option mvcgen.warning false
set_option linter.deprecated.syntax false
set_option maxHeartbeats 800000

/-- Vertex `v` is `p` of a neighbour of `i`. -/
def Image {n : Nat} (g : Graph n) (p : Array Nat) (i v : Nat) : Prop :=
  ∃ e, g.offsets[i]! ≤ e ∧ e < g.offsets[i + 1]! ∧ p[g.neighbor e]! = v

/-- Row `p[i]` is the image of row `i`. -/
def RowOk {n : Nat} (g : Graph n) (p : Array Nat) (i : Nat) : Prop :=
  g.degree p[i]! = g.degree i ∧
    ∀ e, g.offsets[p[i]!]! ≤ e → e < g.offsets[p[i]! + 1]! →
      Image g p i (g.neighbor e)
private theorem range_cursor {s t i : Nat} {pref suff : List Nat}
    (h : List.range' s (t - s) = pref ++ i :: suff) :
    s ≤ i ∧ i < t ∧ i = s + pref.length := by
  have hi := List.mem_of_range'_eq_append_cons h
  have he := List.eq_of_range'_eq_append_cons h
  simp only [List.mem_range'_1] at *
  omega

theorem isautom_rows (G : Hex.SparseGraph n) (p : Array Nat)
    (hp : ∀ i, i < n → p[i]! < n) :
    isautom (.ofGraph G) p = true ↔
      ∀ i, i < n → p[i]! ≠ i → RowOk (.ofGraph G) p i := by
  unfold isautom
  apply Id.of_wp_run_eq rfl (fun b : Bool => b = true ↔
    ∀ i, i < n → p[i]! ≠ i → RowOk (.ofGraph G) p i)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜
      (s.1 = none ∨ cursor.suffix = []) ∧
      (s.1 = none → s.2.size = n ∧
        (∀ v, v < n → s.2[v]! ≤ cursor.prefix.length) ∧
        ∀ i ∈ cursor.prefix, p[i]! ≠ i → RowOk (.ofGraph G) p i) ∧
      (∀ b, s.1 = some b → (b = true ↔
        ∀ i, i < n → p[i]! ≠ i → RowOk (.ofGraph G) p i))⌝
  | inv2 pref i suff he s marks hmove pi hdegree stamp hs => ⇓⟨cursor, marks⟩ => ⌜
      marks.size = n ∧ (∀ v, v < n → marks[v]! ≤ i + 1) ∧
      (∀ v, v < n → (marks[v]! = i + 1 ↔
        ∃ e ∈ cursor.prefix, p[(Graph.ofGraph G).neighbor e]! = v))⌝
  | inv3 pref i suff he s oldmarks hmove pi hdegree stamp hs marks hm => ⇓⟨cursor, r⟩ => ⌜
      (r.1 = none ∨ cursor.suffix = []) ∧
      (r.1 = none → ∀ e ∈ cursor.prefix, Image (.ofGraph G) p i ((Graph.ofGraph G).neighbor e)) ∧
      (∀ b, r.1 = some b → b = false ∧ ∃ e ∈ cursor.prefix,
        ¬Image (.ofGraph G) p i ((Graph.ofGraph G).neighbor e))⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, bne_iff_ne] at *

  all_goals simp_all
  case vc1.step.isTrue.isTrue =>
    rename_i pref i suff b marks pi hs hr hm hd
    have hi := range_cursor (s := 0) (t := n) hr
    exact ⟨i, hi.2.1, hm, fun h => hd h.1⟩
  case vc2.step =>
    rename_i hmark' hold hmark hr hmove hdeg he
    constructor
    · intro v hv
      have h := hmark.2.1 v hv
      rw [Array.getElem_setIfInBounds (by omega)]
      split <;> simp_all
    · intro v hv
      have h := hmark.2.2 v hv
      rw [Array.getElem_setIfInBounds (by omega)]
      split <;> simp_all
  case vc3.step.isTrue.isFalse.pre =>
    rename_i pref i suff b marks pi stamp hs' hs hr hm hd
    have hi := range_cursor (s := 0) (t := n) hr
    have hsize := (hs.2.1 hs.1).1
    constructor <;> intro v hv
    all_goals
      have h := (hs.2.1 hs.1).2.1 v hv
      rw [getElem!_pos b.2 v (by omega)] at h
      omega
  case vc4.step.isTrue =>
    rename_i hs ht hr hm hd hmarks he hmiss
    have hi := range_cursor (s := 0) (t := n) hr
    have hj := range_cursor he
    have hv := Graph.neighbor_lt G ⟨_, hp _ hi.2.1⟩ hj.2.1
    refine ⟨_, Or.inr (Or.inl rfl), ?_⟩
    intro himage
    obtain ⟨j, hlo, hhi, hval⟩ := himage
    apply hmiss
    apply (hmarks.2.2 _ hv).mpr
    exact ⟨j, ⟨hlo, by omega⟩, hval⟩
  case vc5.step.isFalse =>
    rename_i hs ht hr hm hd hmarks he hhit
    have hi := range_cursor (s := 0) (t := n) hr
    have hj := range_cursor he
    have hv := Graph.neighbor_lt G ⟨_, hp _ hi.2.1⟩ hj.2.1
    intro e he'
    rcases he' with he' | rfl
    · exact ht.2.1 ht.1 e he'
    · obtain ⟨j, ⟨hlo, hhi⟩, hval⟩ := (hmarks.2.2 _ hv).mp hhit
      exact ⟨j, hlo, by omega, hval⟩
  case vc7.step.isTrue.isFalse.post.success.post.success.h_1 =>
    rename_i hs hx hr hm hd hmarks hbad
    have hi := range_cursor (s := 0) (t := n) hr
    refine ⟨_, hi.2.1, hm, ?_⟩
    intro hrow
    obtain ⟨e, ⟨hlo, hhi⟩, he⟩ := hbad.2
    exact he (hrow.2 e hlo (by omega))
  case vc8.step.isTrue.isFalse.post.success.post.success.h_2 =>
    rename_i hmarks' hs hx hr hm hd hmarks hrow
    have hi := range_cursor (s := 0) (t := n) hr
    constructor
    · intro v hv
      have h := hmarks.2.1 v hv
      have hsize := hmarks.1
      simp_all
    · intro i hi' hmove
      rcases hi' with hi' | rfl
      · exact (hs.2.1 hs.1).2.2 i hi' hmove
      · exact ⟨hd, fun e hlo hhi => hrow e hlo (by omega)⟩
  case vc9.step.isFalse =>
    grind

end NautyVerified.Proofs.Sparse

import HexGraphIso.Nauty.Search.Refine

/-!
# Prefix extrema and multiplicities of a count list

nauty's nontrivial pass counts a cell's members one at a time, keeping the
least and greatest count so far (`bmin`, `bmax`) and the multiplicity of
every count in between (`bucket`). `pmin cs k`, `pmax cs k` and
`pmult cs k v` are those after the first `k + 1` counts; at the last count
they are HexGraphIso's `foldl Nat.min (headD 0)`, `foldl Nat.max (headD 0)`
and `multOf`.
-/

namespace NautyVerified.Spec

open Hex.GraphIso.Nauty

def pmin (cs : List Nat) (k : Nat) : Nat := (cs.take (k + 1)).foldl Nat.min (cs.headD 0)
def pmax (cs : List Nat) (k : Nat) : Nat := (cs.take (k + 1)).foldl Nat.max (cs.headD 0)
def pmult (cs : List Nat) (k v : Nat) : Nat := (cs.take (k + 1)).countP (· == v)

theorem take_succ_get {cs : List Nat} {k : Nat} (h : k < cs.length) :
    cs.take (k + 1) = cs.take k ++ [cs[k]!] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, getElem!_pos cs k h]
  rfl

theorem head_eq {cs : List Nat} (h : 0 < cs.length) : cs.headD 0 = cs[0]! := by
  cases cs with
  | nil => simp at h
  | cons a l => rfl

theorem pmin_zero {cs : List Nat} (h : 0 < cs.length) : pmin cs 0 = cs[0]! := by
  rw [pmin, take_succ_get h, List.take_zero, List.nil_append, List.foldl_cons, List.foldl_nil,
    head_eq h]
  exact Nat.min_self _

theorem pmax_zero {cs : List Nat} (h : 0 < cs.length) : pmax cs 0 = cs[0]! := by
  rw [pmax, take_succ_get h, List.take_zero, List.nil_append, List.foldl_cons, List.foldl_nil,
    head_eq h]
  exact Nat.max_self _

theorem pmult_zero {cs : List Nat} (h : 0 < cs.length) (v : Nat) :
    pmult cs 0 v = if cs[0]! = v then 1 else 0 := by
  rw [pmult, take_succ_get h, List.take_zero, List.nil_append]
  simp

theorem pmin_succ {cs : List Nat} {k : Nat} (h : k + 1 < cs.length) :
    pmin cs (k + 1) = min (pmin cs k) cs[k + 1]! := by
  rw [pmin, take_succ_get h, List.foldl_append]
  rfl

theorem pmax_succ {cs : List Nat} {k : Nat} (h : k + 1 < cs.length) :
    pmax cs (k + 1) = max (pmax cs k) cs[k + 1]! := by
  rw [pmax, take_succ_get h, List.foldl_append]
  rfl

theorem pmult_succ {cs : List Nat} {k : Nat} (h : k + 1 < cs.length) (v : Nat) :
    pmult cs (k + 1) v = pmult cs k v + if cs[k + 1]! = v then 1 else 0 := by
  rw [pmult, take_succ_get h, List.countP_append]
  simp [pmult]

theorem pmin_le {cs : List Nat} : ∀ {k o : Nat}, k < cs.length → o ≤ k → pmin cs k ≤ cs[o]!
  | 0, o, hk, ho => by rw [pmin_zero hk, show o = 0 by omega]; exact Nat.le_refl _
  | k + 1, o, hk, ho => by
    rw [pmin_succ hk]
    rcases Nat.lt_or_ge o (k + 1) with h | h
    · exact Nat.le_trans (Nat.min_le_left _ _) (pmin_le (by omega) (by omega))
    · rw [show o = k + 1 by omega]; exact Nat.min_le_right _ _

theorem le_pmax {cs : List Nat} : ∀ {k o : Nat}, k < cs.length → o ≤ k → cs[o]! ≤ pmax cs k
  | 0, o, hk, ho => by rw [pmax_zero hk, show o = 0 by omega]; exact Nat.le_refl _
  | k + 1, o, hk, ho => by
    rw [pmax_succ hk]
    rcases Nat.lt_or_ge o (k + 1) with h | h
    · exact Nat.le_trans (le_pmax (by omega) (by omega)) (Nat.le_max_left _ _)
    · rw [show o = k + 1 by omega]; exact Nat.le_max_right _ _

theorem pmin_le_pmax {cs : List Nat} {k : Nat} (hk : k < cs.length) : pmin cs k ≤ pmax cs k :=
  Nat.le_trans (pmin_le hk (Nat.zero_le k)) (le_pmax hk (Nat.zero_le k))

theorem pmult_out {cs : List Nat} : ∀ {k : Nat}, k < cs.length → ∀ v,
    v < pmin cs k ∨ pmax cs k < v → pmult cs k v = 0
  | 0, hk, v, hv => by
    rw [pmult_zero hk, ite_eq_right]
    intro h; rw [pmin_zero hk, pmax_zero hk] at hv; omega
  | k + 1, hk, v, hv => by
    rw [pmult_succ hk, pmult_out (k := k) (by omega) v ?_]
    · rw [ite_eq_right]; intro h; rw [pmin_succ hk, pmax_succ hk] at hv
      have := Nat.min_le_right (pmin cs k) cs[k + 1]!
      have := Nat.le_max_right (pmax cs k) cs[k + 1]!
      omega
    · rw [pmin_succ hk, pmax_succ hk] at hv
      have := Nat.min_le_left (pmin cs k) cs[k + 1]!
      have := Nat.le_max_left (pmax cs k) cs[k + 1]!
      omega

theorem take_full {cs : List Nat} {k : Nat} (hk : k + 1 = cs.length) : cs.take (k + 1) = cs := by
  rw [hk, List.take_length]

theorem pmin_last {cs : List Nat} {k : Nat} (hk : k + 1 = cs.length) :
    pmin cs k = cs.foldl Nat.min (cs.headD 0) := by rw [pmin, take_full hk]

theorem pmax_last {cs : List Nat} {k : Nat} (hk : k + 1 = cs.length) :
    pmax cs k = cs.foldl Nat.max (cs.headD 0) := by rw [pmax, take_full hk]

theorem pmult_last {cs : List Nat} {k : Nat} (hk : k + 1 = cs.length) (v : Nat) :
    pmult cs k v = multOf cs v := by rw [pmult, take_full hk, multOf]

theorem pmult_le {cs : List Nat} (k v : Nat) : pmult cs k v ≤ k + 1 :=
  Nat.le_trans List.countP_le_length (by simp; omega)

theorem pmax_le {cs : List Nat} {B : Nat} (hb : ∀ o : Nat, cs[o]! ≤ B) : ∀ {k : Nat}, k < cs.length →
    pmax cs k ≤ B
  | 0, hk => by rw [pmax_zero hk]; exact hb 0
  | k + 1, hk => by
    rw [pmax_succ hk]
    have := pmax_le hb (k := k) (by omega)
    have := hb (k + 1)
    omega

end NautyVerified.Spec

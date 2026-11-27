import NautyVerified.Proofs.Harness.Opts
import NautyVerified.Proofs.Harness.PartC
import NautyVerified.Proofs.Harness.Input

/-!
# The partition phase of `main`

`wp_tPart`: from the colours of `G` in `colour` (and their maximum in
`maxc`) and zeroed `lab` and `ptn`, the cell and end loops leave
`initialPartition G` in `lab` and `ptn` as `densenautySpec` takes it.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso Hex.GraphIso.Nauty

theorem foldl_max_ge : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
  | [], _ => Nat.le_refl _
  | x :: l, a => Nat.le_trans (Nat.le_max_left a x) (foldl_max_ge l (max a x))

theorem le_foldl_max : ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => absurd h (by simp)
  | y :: l, a, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a x) (foldl_max_ge l _)
    · exact le_foldl_max l _ x h

theorem le_maxPrefix {cs : List Nat} {k j : Nat} (hj : j < k) (hl : j < cs.length) :
    cs[j]! ≤ maxPrefix cs k := by
  rw [getElem!_pos cs j hl]
  exact le_foldl_max _ 0 _ (List.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩)

/-- Colours above every key list nothing. -/
theorem listed_stable (key : Nat → Nat) {n K : Nat} (hK : ∀ v < n, key v < K) :
    ∀ d, listed key n (K + d) 0 = listed key n K 0
  | 0 => rfl
  | d + 1 => by
    rw [← listed_stable key hK d]
    simp only [listed, List.range_zero, List.filter_nil, List.append_nil,
      show K + (d + 1) = (K + d) + 1 by omega, List.range_succ, List.flatMap_append]
    have : clsOf key n (K + d) = [] := by
      simp only [clsOf, List.filter_eq_nil_iff, List.mem_range]
      intro v hv; have := hK v hv; simp; omega
    simp [this]

theorem ints_prefixArr_zero (L : List Nat) (N : Nat) :
    ∀ j < N, (fun _ => Vint (ir 0)) j = ints (prefixArr L N 0) j := by
  intro j hj
  simp [ints, prefixArr_get hj]

theorem wp_tPart {n k : Nat} (G : Colored n k) {Q : Post} {e : env} {le : temp_env} {m : mem}
    {bcol bl bp : block} (hn0 : 0 < n) (hN : n < 2147483648) (hk : k < 2147483648)
    (hcol : PTree.get dense.id.colour le = some (.Vptr bcol Ptrofs.zero))
    (hlab : PTree.get dense.id.lab le = some (.Vptr bl Ptrofs.zero))
    (hptn : PTree.get dense.id.ptn le = some (.Vptr bp Ptrofs.zero))
    (hn : PTree.get dense.id.n le = some (.Vint (ir n)))
    (hmaxc : PTree.get dense.id.maxc le = some (.Vint (ir (maxPrefix (colours G) n))))
    (hcarr : ArrayAt m .Mint32 bcol 0 (ints (prefixArr (colours G) n n)) n)
    (hlz : ArrayAt m .Mint32 bl 0 (fun _ => .Vint (ir 0)) n)
    (hpz : ArrayAt m .Mint32 bp 0 (fun _ => .Vint (ir 0)) n)
    (hb1 : bl ≠ bcol) (hb2 : bp ≠ bcol) (hb3 : bl ≠ bp)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bl 0 (ints (initialPartition G).1) n →
      ArrayAt m' .Mint32 bp 0 (ints (harnessPtn n (initialPartition G).2)) n →
      Unch m m' (fun z => z = bl ∨ z = bp) →
      (∀ x, x ≠ dense.id.c → x ≠ dense.id.j → x ≠ dense.id.pos → x ≠ dense.id.i → x ≠ idOf 715 →
        PTree.get x le' = PTree.get x le) →
      Wp Statement.xi ge dense.fn.main tOpts Q e le' m') :
    Wp Statement.xi ge dense.fn.main tPart Q e le m := by
  have hcl := colours_length G
  have hkey : ∀ v < n, keyOf G v < k := fun v hv => keyOf_bound G hv
  have hk0 : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) (hkey 0 hn0)
  have hmk : maxPrefix (colours G) n < k :=
    maxPrefix_lt hk0 fun j hj => hkey j (by omega)
  have hKk : ∀ v < n, keyOf G v < maxPrefix (colours G) n + 1 := fun v hv =>
    Nat.lt_succ_of_le (le_maxPrefix hv (by omega))
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  apply wp_seq
  refine wp_cells (keyOf G) (colours G) (fun _ _ => rfl) (fun v hv => by have := hkey v hv; omega)
    hN (K := maxPrefix (colours G) n + 1) (by omega) (by omega)
    (by rw [temps_gso _ _ (by decide)]; exact hcol) (by rw [temps_gso _ _ (by decide)]; exact hlab)
    (by rw [temps_gso _ _ (by decide)]; exact hptn) (by rw [temps_gso _ _ (by decide)]; exact hn)
    (by rw [temps_gso _ _ (by decide)]; simpa using hmaxc) (temps_gss _ _ _) hcarr
    ⟨hlz.congr (ints_prefixArr_zero _ n), hpz.congr (ints_prefixArr_zero _ n)⟩ hb1 hb2 hb3
    fun le1 m1 hL hu1 _ ho1 => ?_
  simp only [seqPost, Post.after, E0_append]
  have hlen := listed_full (keyOf G) hKk
  have hLeq : listed (keyOf G) n (maxPrefix (colours G) n + 1) 0 = listed (keyOf G) n k 0 := by
    have := listed_stable (keyOf G) hKk (k - (maxPrefix (colours G) n + 1))
    rw [show maxPrefix (colours G) n + 1 + (k - (maxPrefix (colours G) n + 1)) = k by omega] at this
    exact this.symm
  have hle1 : ∀ x, x ≠ dense.id.c → x ≠ dense.id.j → x ≠ dense.id.pos → PTree.get x le1 = PTree.get x le :=
    fun x h1 h2 h3 => by rw [ho1 x h1 h2 h3, temps_gso _ _ h3]
  apply wp_seq
  refine wp_ends (keyOf G) (colours G) (fun _ _ => rfl) (fun v hv => by have := hkey v hv; omega)
    hn0 hN _ (listed_lt (keyOf G) (Nat.zero_le _)) hlen
    (by rw [hle1 _ (by decide) (by decide) (by decide)]; exact hcol)
    (by rw [hle1 _ (by decide) (by decide) (by decide)]; exact hlab)
    (by rw [hle1 _ (by decide) (by decide) (by decide)]; exact hptn)
    (by rw [hle1 _ (by decide) (by decide) (by decide)]; exact hn)
    (hcarr.unch hu1 (by rintro (h | h) <;> exact absurd h.symm (by assumption)))
    (by have := hL.lab; rwa [hlen] at this)
    (by
      have := hL.ptn; rw [hlen] at this
      refine this.congr fun j hj => ?_
      simp [ints, prefixArr_get hj, endPtn_get hj, hj])
    (Ne.symm hb2 |> fun h => by intro h'; exact hb2 h') hb3.symm
    fun le2 m2 hp2 hu2 ho2 => ?_
  simp only [seqPost, Post.after, E0_append]
  refine hQ le2 m2 ?_ ?_ ?_ ?_
  · have := hL.lab.unch hu2 hb3
    rw [hlen] at this
    refine this.congr fun j hj => ?_
    rw [initialPartition_eq]
    simp only [ints, prefixArr_get hj, hj, ite_true, hLeq]
    have hj' : j < (listed (keyOf G) n k 0).length := by rw [← hLeq, hlen]; exact hj
    rw [getElem!_pos _ j hj', getElem!_pos _ j (by simpa using hj')]
    simp
  · refine hp2.congr fun j hj => ?_
    simp only [ints]
    rw [endPtn_get hj, harnessPtn_get G hj, hLeq]
    simp [hj]
  · exact (hu1.trans (hu2.mono fun z hz => .inr hz))
  · intro x h1 h2 h3 h4 h5
    rw [ho2 x h4 h5, hle1 x h1 h2 h3]

end NautyVerified.Proofs.Harness

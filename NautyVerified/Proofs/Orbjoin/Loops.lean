import NautyVerified.Proofs.Orbjoin.Join
import NautyVerified.Logic.For

/-!
# The two loops of `orbjoin`

`wp_joinLoop`: the first loop turns `orbits` from `o` into
`(List.range n).foldl (join map n) o`.
-/

namespace NautyVerified.Proofs.Orbjoin

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open Hex.GraphIso.Nauty.Orbit

variable {xi : ExternalCalls}

theorem foldl_range_succ {β : Type} (f : β → Nat → β) (b : β) (k : Nat) :
    (List.range (k + 1)).foldl f b = f ((List.range k).foldl f b) k := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem wp_joinLoop {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {bo : block} {ofs : ptrofs} {bm : block} {mofs : ptrofs} {o mp : Array Nat} {n : Nat}
    (h : Frame m le bo ofs bm mofs o mp n)
    (hQ : ∀ le' m', Frame m' le' bo ofs bm mofs ((List.range n).foldl (join mp n) o) mp n →
      Unch m m' (· = bo) → Q.normal E0 e le' m') :
    Wp xi ge f (forI joinStep) Q e le m := by
  refine wp_forLoop (xi := xi) id.i id.n joinStep n h.nlt
    (fun k le m' => Frame m' le bo ofs bm mofs ((List.range k).foldl (join mp n) o) mp n ∧
      Unch m m' (· = bo) ∧ k ≤ n ∧ PTree.get id.i le = some (.Vint (ir k)))
    (fun k le m' => Frame m' le bo ofs bm mofs ((List.range (k + 1)).foldl (join mp n) o) mp n ∧
      Unch m m' (· = bo) ∧ k < n ∧ PTree.get id.i le = some (.Vint (ir k))) ?_ ?_ ?_ ?_ ?_
  · rintro k le m ⟨hf, -, hk, hi⟩
    exact ⟨hk, hi, hf.hn⟩
  · refine ⟨h.temps fun k hk => ?_, Unch.refl _ _, Nat.zero_le _, temps_gss _ _ _⟩
    rw [temps_gso _ _ (by rcases hk with rfl | rfl | rfl <;> decide)]
  · rintro k le m' hk ⟨hf, hu, -, hi⟩
    refine wp_joinStep hf hk hi ?_
    intro le' m'' hf' hu' hi'
    exact ⟨rfl, by rw [foldl_range_succ]; exact hf', hu.trans hu', hk, hi'⟩
  · rintro k le m ⟨hf, hu, hk, hi⟩
    refine ⟨hi, hf.temps fun k' hk' => ?_, hu, hk, temps_gss _ _ _⟩
    rw [temps_gso _ _ (by rcases hk' with rfl | rfl | rfl <;> decide)]
  · rintro le m ⟨hf, hu, -, -⟩
    exact hQ le m hf hu

/-- One iteration of the second loop: `HexGraphIso`'s `compress`. -/
theorem wp_compressStep {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {bo : block} {ofs : ptrofs} {bm : block} {mofs : ptrofs} {o mp : Array Nat} {n c : Nat}
    (h : Frame m le bo ofs bm mofs o mp n) {k : Nat} (hk : k < n)
    (hiv : PTree.get id.i le = some (.Vint (ir k)))
    (hjv : PTree.get id.j1 le = some (.Vint (ir c)))
    (hQ : ∀ le' m', Frame m' le' bo ofs bm mofs (compress (o, c) k).1 mp n → Unch m m' (· = bo) →
      PTree.get id.i le' = some (.Vint (ir k)) →
      PTree.get id.j1 le' = some (.Vint (ir (compress (o, c) k).2)) → Q.normal E0 e le' m') :
    Wp xi ge f compressStep Q e le m := by
  have hnl := h.nlt
  have hii : Exec.evalExpr ge e le m (tv id.i) = some (.Vint (ir k)) := hiv
  have hok := ints_lt h.desc hk
  have hook := ints_lt h.desc hok
  have hsz : o.size = n := h.desc.1
  have hoo := eval_orb h.arr h.nlt h.horb (orb (tv id.i)) o[k]! hok
    (eval_orb h.arr h.nlt h.horb (tv id.i) k hk hii rfl) rfl
  simp only [compressStep, sk]
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, hoo]
  simp only [ints, typeof, cop]
  have hle1 : ∀ k', k' ≠ id.t → PTree.get k' (PTree.set id.t (.Vint (ir (o[o[k]!]! : Int))) le) =
      PTree.get k' le := fun k' hk' => temps_gso _ _ hk'
  have h1 : Frame m (PTree.set id.t (.Vint (ir (o[o[k]!]! : Int))) le) bo ofs bm mofs o mp n :=
    h.temps fun k' hk' => hle1 k' (by rcases hk' with rfl | rfl | rfl <;> decide)
  refine wp_store h1.arr h1.nlt id.orbits h1.horb (tv id.i) k hk
    (by show PTree.get _ _ = _; rw [hle1 _ (by decide)]; exact hiv) rfl
    (tv id.t) (o[o[k]!]!) (temps_gss _ _ _) rfl ?_
  intro m' harr' hu
  have hset : ints (o.set! k o[o[k]!]!) = upd (ints o) k (.Vint (ir (o[o[k]!]! : Int))) :=
    ints_set (by omega) _
  have h2 : Frame m' (PTree.set id.t (.Vint (ir (o[o[k]!]! : Int))) le) bo ofs bm mofs
      (compress (o, c) k).1 mp n :=
    { h1 with
      arr := by simp only [compress]; rw [hset]; exact harr'
      marr := h1.marr.unch hu h.hne.symm
      desc := compress_desc (s := (o, c)) h.desc hk }
  apply wp_if_eval
  simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, temps_gso, hiv, typeof, cop]
  rw [ir_eq (a := (o[o[k]!]! : Int)) (b := k) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  have hci : (compress (o, c) k).2 = if o[o[k]!]! = k then c + 1 else c := by
    simp only [compress, Array.getElem!_set!_self _ _ _ (show k < o.size by omega), beq_iff_eq]
  by_cases hr : o[o[k]!]! = k
  · rw [ite_eq_left (by simp [hr])]
    wp_step; wp_step
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, hjv, typeof, cop, ir_add]
    refine hQ _ m' (h2.temps fun k' hk' => ?_) hu ?_ ?_
    · rw [temps_gso _ _ (by rcases hk' with rfl | rfl | rfl <;> decide)]
    · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hiv
    · rw [temps_gss, hci, ite_eq_left hr]; push_cast; rfl
  · rw [ite_eq_right (by simp; omega)]
    apply wp_skip
    refine hQ _ m' h2 hu ?_ ?_
    · rw [temps_gso _ _ (by decide)]; exact hiv
    · rw [temps_gso _ _ (by decide), hci, ite_eq_right hr]; exact hjv

/-- The second loop: `(List.range n).foldl compress (o, c₀)`, counting in `j1`. -/
theorem wp_compressLoop {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {bo : block} {ofs : ptrofs} {bm : block} {mofs : ptrofs} {o mp : Array Nat} {n : Nat}
    (h : Frame m le bo ofs bm mofs o mp n)
    (hjv : PTree.get id.j1 le = some (.Vint (ir 0)))
    (hQ : ∀ le' m', Frame m' le' bo ofs bm mofs ((List.range n).foldl compress (o, 0)).1 mp n →
      PTree.get id.j1 le' = some (.Vint (ir ((List.range n).foldl compress (o, 0)).2)) →
      Unch m m' (· = bo) → Q.normal E0 e le' m') :
    Wp xi ge f (forI compressStep) Q e le m := by
  refine wp_forLoop (xi := xi) id.i id.n compressStep n h.nlt
    (fun k le m' => Frame m' le bo ofs bm mofs ((List.range k).foldl compress (o, 0)).1 mp n ∧
      Unch m m' (· = bo) ∧ k ≤ n ∧ PTree.get id.i le = some (.Vint (ir k)) ∧
      PTree.get id.j1 le = some (.Vint (ir ((List.range k).foldl compress (o, 0)).2)))
    (fun k le m' => Frame m' le bo ofs bm mofs ((List.range (k + 1)).foldl compress (o, 0)).1 mp n ∧
      Unch m m' (· = bo) ∧ k < n ∧ PTree.get id.i le = some (.Vint (ir k)) ∧
      PTree.get id.j1 le = some (.Vint (ir ((List.range (k + 1)).foldl compress (o, 0)).2)))
    ?_ ?_ ?_ ?_ ?_
  · rintro k le m ⟨hf, -, hk, hi, -⟩
    exact ⟨hk, hi, hf.hn⟩
  · refine ⟨h.temps fun k hk => ?_, Unch.refl _ _, Nat.zero_le _, temps_gss _ _ _, ?_⟩
    · rw [temps_gso _ _ (by rcases hk with rfl | rfl | rfl <;> decide)]
    · rw [temps_gso _ _ (by decide)]; exact hjv
  · rintro k le m' hk ⟨hf, hu, -, hi, hj⟩
    refine wp_compressStep (c := ((List.range k).foldl compress (o, 0)).2)
      (o := ((List.range k).foldl compress (o, 0)).1) hf hk hi hj ?_
    intro le' m'' hf' hu' hi' hj'
    refine ⟨rfl, by rw [foldl_range_succ]; exact hf', hu.trans hu', hk, hi',
      by rw [foldl_range_succ]; exact hj'⟩
  · rintro k le m ⟨hf, hu, hk, hi, hj⟩
    refine ⟨hi, hf.temps fun k' hk' => ?_, hu, hk, temps_gss _ _ _, ?_⟩
    · rw [temps_gso _ _ (by rcases hk' with rfl | rfl | rfl <;> decide)]
    · rw [temps_gso _ _ (by decide)]; exact hj
  · rintro le m ⟨hf, hu, -, -, hj⟩
    exact hQ le m hf hj hu

end NautyVerified.Proofs.Orbjoin

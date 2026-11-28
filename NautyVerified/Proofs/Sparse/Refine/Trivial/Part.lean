import NautyVerified.Proofs.Sparse.Refine.Trivial.Marks
import NautyVerified.Proofs.Sparse.Distvals.Search
import NautyVerified.Proofs.Sparse.Refine.Trivial.Store

/-!
# The partition of a touched cell

`partLoopT`: `do { lj = lab[j]; if (ISMARKED2(lj)) HITS[k++] = lj; else
lab[v2++] = lj; } while (ptn[j++] > level);` over the cell at `first` of
length `len` computes `partStep` over the cell: the untouched vertices
packed from `first`, the touched ones in `HITS[0..k)`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem bool_val_ob (b : Bool) (m : mem) : Cfrontend.Cop.bool_val (Val.of_bool b) tint m = some b := by
  cases b <;> rfl

/-- A conditional on a comparison. -/
theorem wp_if_ob {f : function} {Q : Post} {le : temp_env} {m : mem} {a : expr} {s1 s2 : statement}
    {b : Bool} (ha : Exec.evalExpr sge empty_env le m a = some (Val.of_bool b)) (hty : typeof a = tint)
    (h : Wp xi sge f (if b then s1 else s2) Q empty_env le m) :
    Wp xi sge f (.Sifthenelse a s1 s2) Q empty_env le m := by
  apply wp_if_eval
  rw [ha, hty]
  dsimp only
  rw [bool_val_ob]
  exact h

theorem push_lt (a : Array Nat) (x i : Nat) (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i h]; simp [Array.getElem_push, h]

theorem push_size (a : Array Nat) (x : Nat) : (a.push x)[a.size]! = x := by simp

theorem eval_binop {le : temp_env} {m : mem} {op : Cfrontend.Cop.binary_operation} {a1 a2 : expr}
    {ty : Cfrontend.Ctypes.type} {v1 v2 : val}
    (h1 : Exec.evalExpr sge empty_env le m a1 = some v1) (h2 : Exec.evalExpr sge empty_env le m a2 = some v2) :
    Exec.evalExpr sge empty_env le m (.Ebinop op a1 a2 ty) =
      Cfrontend.Cop.sem_binary_operation sge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m := by
  rw [Exec.evalExpr, h1, h2]

theorem eval_tv {le : temp_env} {m : mem} {x : ident} {v : val} (h : PTree.get x le = some v) :
    Exec.evalExpr sge empty_env le m (.Etempvar x tint) = some v := h

/-- `x + 1`. -/
theorem eval_inc {le : temp_env} {m : mem} {x : ident} {c : Int} (h : PTree.get x le = some (.Vint (ir c))) :
    Exec.evalExpr sge empty_env le m (.Ebinop .Oadd (tv x) (ci 1 tint) tint) =
      some (.Vint (ir (c + 1))) := by
  rw [eval_binop (eval_tv h) rfl]
  simp only [typeof, cop, ir_add]

/-- The partition after `q` positions. -/
abbrev partAt (vm : Array Nat) (stamp first : Nat) (lab : Array Nat) (q : Nat) :
    Array Nat × Nat × Array Nat :=
  (List.range' first q).foldl (partStep vm stamp) (lab, first, #[])

theorem partAt_succ (vm : Array Nat) (stamp first : Nat) (lab : Array Nat) (q : Nat) :
    partAt vm stamp first lab (q + 1) = partStep vm stamp (partAt vm stamp first lab q) (first + q) := by
  simp only [partAt, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Nat.one_mul]

/-- The partition keeps the array's size and range, packs below the cursor,
and collects the rest. -/
theorem partAt_inv (vm : Array Nat) (stamp first : Nat) (lab : Array Nat) (hn : lab.size = n)
    (hb : ∀ i < n, lab[i]! < n) : ∀ q, first + q ≤ n →
    (partAt vm stamp first lab q).1.size = n ∧
      (∀ i < n, (partAt vm stamp first lab q).1[i]! < n) ∧
      (partAt vm stamp first lab q).2.1 + (partAt vm stamp first lab q).2.2.size = first + q ∧
      (∀ i < (partAt vm stamp first lab q).2.2.size, (partAt vm stamp first lab q).2.2[i]! < n) ∧
      (∀ i, first + q ≤ i → (partAt vm stamp first lab q).1[i]! = lab[i]!)
  | 0, _ => ⟨hn, hb, by simp [partAt], by simp [partAt], fun _ _ => rfl⟩
  | q + 1, hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := partAt_inv vm stamp first lab hn hb q (by omega)
    rw [partAt_succ]
    generalize partAt vm stamp first lab q = p at h1 h2 h3 h4 h5
    have hj : p.1[first + q]! < n := h2 _ (by omega)
    unfold partStep
    split
    · refine ⟨h1, h2, by simp; omega, fun i hi => ?_, fun i hi => h5 i (by omega)⟩
      simp only [Array.size_push] at hi
      by_cases he : i = p.2.2.size
      · subst he; rw [push_size]; exact hj
      · rw [push_lt _ _ _ (by omega)]; exact h4 i (by omega)
    · refine ⟨by simp [h1], fun i hi => ?_, by simp; omega, h4, fun i hi => ?_⟩
      · by_cases he : i = p.2.1
        · subst he; rw [Array.getElem!_set!_self _ _ _ (by omega)]; exact hj
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]; exact h2 i hi
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]; exact h5 i (by omega)

/-- The temporaries the partition loop assigns. -/
abbrev partTemps : List ident := [id.«j», id.«v2», id.«k», id.«lj», idOf 740, idOf 741, idOf 742]

/-- `partLoopT` over the cell of length `len` at `first`, from `j = v2 = first`
and `k = 0`, with `vmark2` marking exactly the vertices `v` with
`vm[v] = stamp`. -/
theorem wp_partLoop {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (hr : Rep L t S) (ht : Tmp le L t) {first len : Nat} (hc : IsCell t.ptn L.level first len)
    (hfl : first + len ≤ n) (hls : t.lab.size = n) (hlb : ∀ i < n, t.lab[i]! < n)
    {vm : Array Nat} {stamp : Nat} (hmk : ∀ v < n, (S.mk2 v = S.st2 ↔ vm[v]! = stamp))
    (hj : PTree.get id.«j» le = some (.Vint (ir first)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir first)))
    (hk : PTree.get id.«k» le = some (.Vint (ir 0)))
    (hQ : ∀ le' m' (w : Array Nat),
      Mem m' L G { t with lab := (partAt vm stamp first t.lab len).1 } { S with w3 := w } →
      Rep L { t with lab := (partAt vm stamp first t.lab len).1 } { S with w3 := w } →
      (∀ i < (partAt vm stamp first t.lab len).2.2.size,
        w[i]! = (partAt vm stamp first t.lab len).2.2[i]!) →
      Frame L m m' →
      PTree.get id.«j» le' = some (.Vint (ir (first + len))) →
      PTree.get id.«v2» le' = some (.Vint (ir (partAt vm stamp first t.lab len).2.1)) →
      PTree.get id.«k» le' = some (.Vint (ir (partAt vm stamp first t.lab len).2.2.size)) →
      (∀ x, x ∉ partTemps → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F partLoopT Q empty_env le m := by
  have hnl := hok.nlt
  have hlen := hc.1
  let P := partAt vm stamp first t.lab
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q w, v = len - q ∧ q < len ∧
      Mem m' L G { t with lab := (P q).1 } { S with w3 := w } ∧
      Rep L { t with lab := (P q).1 } { S with w3 := w } ∧
      (∀ i < (P q).2.2.size, w[i]! = (P q).2.2[i]!) ∧ Frame L m m' ∧
      PTree.get id.«j» le' = some (.Vint (ir (first + q))) ∧
      PTree.get id.«v2» le' = some (.Vint (ir (P q).2.1)) ∧
      PTree.get id.«k» le' = some (.Vint (ir (P q).2.2.size)) ∧
      ∀ x, x ∉ partTemps → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q w, v = len - q ∧ q < len ∧
      Mem m' L G { t with lab := (P (q + 1)).1 } { S with w3 := w } ∧
      Rep L { t with lab := (P (q + 1)).1 } { S with w3 := w } ∧
      (∀ i < (P (q + 1)).2.2.size, w[i]! = (P (q + 1)).2.2[i]!) ∧ Frame L m m' ∧
      PTree.get id.«j» le' = some (.Vint (ir (first + q))) ∧
      PTree.get id.«v2» le' = some (.Vint (ir (P (q + 1)).2.1)) ∧
      PTree.get id.«k» le' = some (.Vint (ir (P (q + 1)).2.2.size)) ∧
      ∀ x, x ∉ partTemps → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := len - 0)
    ⟨rfl, rfl, 0, S.w3, rfl, hlen, hm, hr, fun i hi => by simp [P, partAt] at hi, Frame.refl _ _,
      by simpa using hj, by simpa [P, partAt] using hv2, by simpa [P, partAt] using hk,
      fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, q, w, rfl, hq, hm', hr', hw, hf, hj', hv2', hk', ho⟩
    have ht' : Tmp le' L { t with lab := (P q).1 } := (ht.frame ho (by decide)).congr rfl rfl
    have hi := partAt_inv vm stamp first t.lab hls hlb q (by omega)
    have i1 : (P q).1.size = n := hi.1
    have i2 : ∀ i < n, (P q).1[i]! < n := hi.2.1
    have i3 : (P q).2.1 + (P q).2.2.size = first + q := hi.2.2.1
    have i4 : ∀ i < (P q).2.2.size, (P q).2.2[i]! < n := hi.2.2.2.1
    have hjn : first + q < n := by omega
    have hlj : (P q).1[first + q]! < n := i2 _ hjn
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_lab hok hm' ht' (eval_tv hj') rfl hjn]
    dsimp only
    wp_step; wp_step
    let le1 := PTree.set id.«lj» (.Vint (ir ((P q).1[first + q]! : Int))) le'
    have hlj1 : PTree.get id.«lj» le1 = some (.Vint (ir ((P q).1[first + q]! : Int))) := temps_gss _ _ _
    have hM2 : Marks2.MarksAt m' L.mc2 L.mb2 S.st2 S.mk2 := hm'.k2
    have hmb := hM2.bounds ((P q).1[first + q]!) (by have := hok.mc2; omega)
    refine wp_if_ob (b := decide (S.mk2 (P q).1[first + q]! = S.st2)) ?_ rfl ?_
    · rw [eval_binop (eval_mk2 hok hm' (eval_tv hlj1) rfl (by have := hok.mc2; omega))
        (eval_val2 hm')]
      simp only [typeof, cop]
      rw [eq_marks hmb.1 (by have := hM2.val32; omega) (by omega) (by have := hM2.val32; omega)]
    have hstep : P (q + 1) = partStep vm stamp (P q) (first + q) := partAt_succ _ _ _ _ _
    by_cases hmark : S.mk2 (P q).1[first + q]! = S.st2
    · have hvm : (vm[(P q).1[first + q]!]! == stamp) = true := by
        simpa using (hmk _ hlj).1 hmark
      have hP : P (q + 1) = ((P q).1, (P q).2.1, (P q).2.2.push (P q).1[first + q]!) := by
        rw [hstep]; unfold partStep; rw [ite_eq_left hvm]
      simp only [hmark, decide_true, ite_true]
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_tv (show PTree.get id.«k» le1 = _ by rw [temps_gso _ _ (by decide)]; exact hk')]
      dsimp only
      apply wp_set_eval
      rw [eval_inc (temps_gss _ _ _)]
      dsimp only
      let le2 := PTree.set id.«k» (.Vint (ir (((P q).2.2.size + 1 : Nat) : Int)))
        (PTree.set (idOf 741) (.Vint (ir ((P q).2.2.size : Int))) le1)
      have hsz : (P q).2.2.size < n := by omega
      refine wp_w3 hok hm' hr'.w3size (eval_tv (show PTree.get (idOf 741) le2 = _ by
        rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _)) rfl hsz
        (eval_tv (show PTree.get id.«lj» le2 = _ by
          rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hlj1)) rfl ?_
      intro m'' hm'' hf'
      refine ⟨by simp, rfl, q, w.set! (P q).2.2.size (P q).1[first + q]!, rfl, hq, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · rw [hP]; exact hm''
      · rw [hP]
        exact { hr' with
          w3size := by simp [hr'.w3size]
          w3small := fun i hi => by
            by_cases he : i = (P q).2.2.size
            · subst he; rw [Array.getElem!_set!_self _ _ _ (by simp [hr'.w3size]; omega)]; omega
            · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]; exact hr'.w3small i hi }
      · intro i hi
        rw [hP] at hi ⊢
        simp only [Array.size_push] at hi
        by_cases he : i = (P q).2.2.size
        · subst he
          rw [Array.getElem!_set!_self _ _ _ (by simp [hr'.w3size]; omega), push_size]
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he), push_lt _ _ _ (by omega)]
          exact hw i (by omega)
      · exact hf.trans hf'
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj'
      · rw [hP, temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]
        exact hv2'
      · rw [hP, temps_gss]; simp
      · intro x hx
        simp only [partTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [temps_gso _ _ hx.2.2.1, temps_gso _ _ hx.2.2.2.2.2.1, temps_gso _ _ hx.2.2.2.1]
        exact ho x (by simp [partTemps]; exact hx)
    · have hvm : (vm[(P q).1[first + q]!]! == stamp) = false := by
        simpa using fun h => hmark ((hmk _ hlj).2 h)
      have hP : P (q + 1) = ((P q).1.set! (P q).2.1 (P q).1[first + q]!, (P q).2.1 + 1, (P q).2.2) := by
        rw [hstep]; unfold partStep; rw [ite_eq_right (by simp [hvm])]
      simp only [hmark, decide_false, Bool.false_eq_true, ite_false]
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_tv (show PTree.get id.«v2» le1 = _ by rw [temps_gso _ _ (by decide)]; exact hv2')]
      dsimp only
      apply wp_set_eval
      rw [eval_inc (temps_gss _ _ _)]
      dsimp only
      let le2 := PTree.set id.«v2» (.Vint (ir (((P q).2.1 + 1 : Nat) : Int)))
        (PTree.set (idOf 742) (.Vint (ir ((P q).2.1 : Int))) le1)
      have ht2 : Tmp le2 L { t with lab := (P q).1 } :=
        ht'.frame (ws := [id.«v2», idOf 742, id.«lj»]) (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.1, temps_gso _ _ hx.2.2]) (by decide)
      refine wp_lab hok hm' ht2 (eval_tv (show PTree.get (idOf 742) le2 = _ by
        rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _)) rfl (by omega)
        (eval_tv (show PTree.get id.«lj» le2 = _ by
          rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hlj1)) rfl i1 ?_
      intro m'' hm'' hf'
      refine ⟨by simp, rfl, q, w, rfl, hq, ?_, ?_, ?_, hf.trans hf', ?_, ?_, ?_, ?_⟩
      · rw [hP]; exact hm''
      · rw [hP]; exact ⟨hr'.starts, hr'.queue, hr'.w3size, hr'.w3small, hr'.ptnSmall⟩
      · rw [hP]; exact hw
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj'
      · rw [hP, temps_gss]
      · rw [hP, temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]
        exact hk'
      · intro x hx
        simp only [partTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [temps_gso _ _ hx.2.1, temps_gso _ _ hx.2.2.2.2.2.2, temps_gso _ _ hx.2.2.2.1]
        exact ho x (by simp [partTemps]; exact hx)
  · rintro v tr e' le' m' ⟨rfl, rfl, q, w, rfl, hq, hm', hr', hw, hf, hj', hv2', hk', ho⟩
    have ht' : Tmp le' L { t with lab := (P (q + 1)).1 } := (ht.frame ho (by decide)).congr rfl rfl
    have hjn : first + q < n := by omega
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_tv hj']
    dsimp only
    apply wp_set_eval
    rw [eval_inc (temps_gss _ _ _)]
    dsimp only
    let le2 := PTree.set id.«j» (.Vint (ir ((first : Int) + q + 1)))
      (PTree.set (idOf 740) (.Vint (ir ((first : Int) + q))) le')
    have ht2 : Tmp le2 L { t with lab := (P (q + 1)).1 } :=
      ht'.frame (ws := [id.«j», idOf 740]) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2]) (by decide)
    have hpt : t.ptn[first + q]! < 2147483648 := hr'.ptnSmall (first + q) hjn
    have hlv := hok.levlt
    refine wp_if_ob (b := decide (L.level < t.ptn[first + q]!)) ?_ rfl ?_
    · rw [eval_binop (eval_ptn hok hm' ht2 (eval_tv (show PTree.get (idOf 740) le2 = _ by
        rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _)) rfl hjn) (eval_tv ht2.level)]
      simp only [typeof, cop]
      rw [ir_lt ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      simp
    · by_cases hlast : q + 1 < len
      · have hgt : L.level < t.ptn[first + q]! := hc.2.2.1 (first + q) (by omega) (by omega)
        simp only [hgt, decide_true, ite_true]
        apply wp_skip
        refine ⟨len - (q + 1), by omega, by simp, rfl, q + 1, w, rfl, hlast, hm', hr', hw, hf, ?_, ?_, ?_, ?_⟩
        · rw [temps_gss]; congr 2
        · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hv2'
        · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hk'
        · intro x hx
          simp only [partTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.2.2.2.1]
          exact ho x (by simp [partTemps]; exact hx)
      · have hql : q + 1 = len := by omega
        have hle : t.ptn[first + q]! ≤ L.level := by
          have := hc.2.2.2; rw [show first + len - 1 = first + q by omega] at this; exact this
        simp only [show decide (L.level < t.ptn[first + q]!) = false by simp; omega, Bool.false_eq_true,
          ite_false]
        apply wp_break
        simp only [E0_append]
        subst hql
        refine hQ le2 m' w hm' hr' hw hf ?_ ?_ ?_ ?_
        · rw [temps_gss]; congr 2
        · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hv2'
        · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hk'
        · intro x hx
          simp only [partTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.2.2.2.1]
          exact ho x (by simp [partTemps]; exact hx)

end NautyVerified.Proofs.Sparse.Refine.Trivial

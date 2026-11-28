import NautyVerified.Proofs.Sparse.Refine.Ops
import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Model
import NautyVerified.Proofs.Sparse.Distvals.Search

/-!
# The first-touch clearing of `refine_sg`'s nontrivial pass

`wp_storeHits`: `HITS[a] = x` as a `Frame` step. `wp_clearLoop`:
`do HITS[lab[k]] = 0; while (ptn[k++] > level);` from the start `a` of a cell
ending at `e` zeroes the hit counts of the cell's vertices (the fold of
`clear_writes`), leaving `k = e + 1`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem eval_binop {e : env} {le : temp_env} {m : mem} {op : Cfrontend.Cop.binary_operation}
    {a1 a2 : expr} {ty : Cfrontend.Ctypes.type} {v1 v2 : val}
    (h1 : Exec.evalExpr sge e le m a1 = some v1) (h2 : Exec.evalExpr sge e le m a2 = some v2) :
    Exec.evalExpr sge e le m (.Ebinop op a1 a2 ty) =
      Cfrontend.Cop.sem_binary_operation sge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m := by
  simp only [Exec.evalExpr, h1, h2]

/-- `HITS[a] = x`, as a step of `refine_sg`. -/
theorem wp_storeHits {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (hsize : S.w3.size = n) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w3 := S.w3.set! c x } → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work3» a) rhs) Q empty_env le m := by
  obtain ⟨T, hT, htl⟩ := hm.hi
  refine wp_idx_store_far hm.w3 (by have := hok.nlt; omega) htl (Int.le_refl _) (eval_w3 hok hm) rfl rfl rfl a c hc ha hty
    rhs tint hrty _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr htl' hu hk hg
  refine hQ m' (hm.setW3 hok hu hk _ ?_ ⟨T, hT, htl'⟩) (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))
  rw [ints_set (by omega) x]; exact harr

/-- Zeroing the hit counts of `lab[a..a+len)`. -/
def clearCell (lab : Array Nat) (a len : Nat) (H : Array Nat) : Array Nat :=
  (List.range' a len).foldl (fun h q => h.set! lab[q]! 0) H

/-- `HITCELL[a] = x`, as a step of `refine_sg`. -/
theorem wp_storeHitcell {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.c4) {rhs : expr} {x : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w4 := upd S.w4 c (.Vint (ir x)) } → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work4» a) rhs) Q empty_env le m := by
  refine wp_idx_store hm.w4 hm.d4.capLt (eval_w4 hok hm) rfl rfl rfl a c hc ha hty rhs tint hrty
    _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  exact hQ m' (hm.setW4 hok hu hk _ harr) (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))

theorem size_foldl_set (lab : Array Nat) : ∀ (l : List Nat) (A : Array Nat),
    (l.foldl (fun h q => h.set! lab[q]! 0) A).size = A.size
  | [], _ => rfl
  | q :: l, A => by rw [List.foldl_cons, size_foldl_set lab l, Array.size_set!]

theorem foldl_set_succ (lab : Array Nat) (A : Array Nat) {a p : Nat} (hp : a ≤ p) :
    (List.range' a (p + 1 - a)).foldl (fun h q => h.set! lab[q]! 0) A =
      ((List.range' a (p - a)).foldl (fun h q => h.set! lab[q]! 0) A).set! lab[p]! 0 := by
  rw [show p + 1 - a = (p - a) + 1 by omega, List.range'_concat, List.foldl_append, Nat.one_mul,
    show a + (p - a) = p by omega]
  rfl

/-- The clearing loop over the cell `[a, e]`. -/
theorem wp_clearLoop {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (hr : Rep L t S) (ht : Tmp le L t) (hlab : ∀ i < n, t.lab[i]! < n)
    {a e : Nat} (hae : a ≤ e) (hen : e < n)
    (hin : ∀ q, a ≤ q → q < e → L.level < t.ptn[q]!) (hend : t.ptn[e]! ≤ L.level)
    (hk : PTree.get id.«k» le = some (.Vint (ir a)))
    (hQ : ∀ le' m', Mem m' L G t { S with w3 := clearCell t.lab a (e + 1 - a) S.w3 } →
      Frame L m m' →
      PTree.get id.«k» le' = some (.Vint (ir (e + 1))) →
      (∀ x, x ∉ [id.«k», idOf 752] → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F clearLoop Q empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  let W (p : Nat) : Array Nat := (List.range' a (p - a)).foldl (fun h l => h.set! t.lab[l]! 0) S.w3
  have hWs : ∀ p, (W p).size = n := fun p => by
    simp only [W, size_foldl_set]; exact hr.w3size
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ p, a ≤ p ∧ p ≤ e ∧ v = e - p ∧ Mem m' L G t { S with w3 := W p } ∧
      Frame L m m' ∧ PTree.get id.«k» le' = some (.Vint (ir p)) ∧
      ∀ x, x ∉ [id.«k», idOf 752] → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ p, a ≤ p ∧ p ≤ e ∧ v = e - p ∧ Mem m' L G t { S with w3 := W (p + 1) } ∧
      Frame L m m' ∧ PTree.get id.«k» le' = some (.Vint (ir p)) ∧
      ∀ x, x ∉ [id.«k», idOf 752] → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := e - a)
    ⟨rfl, rfl, a, Nat.le_refl _, hae, rfl, by simpa [W] using hm, Frame.refl _ _, hk,
      fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, p, hap, hpe, rfl, hm', hf, hkp, ho⟩
    have ht' := ht.frame ho (by decide)
    wp_step; wp_step
    refine wp_storeHits hok hm' (hWs p) (eval_lab hok hm' ht' (show Exec.evalExpr sge empty_env le' m'
      (tv id.«k») = _ from hkp) rfl (by omega)) rfl (hlab p (by omega)) (x := 0) rfl rfl ?_
    intro m'' hm'' hf'
    refine ⟨by simp, rfl, p, hap, hpe, rfl, ?_, hf.trans hf', hkp, ho⟩
    simpa only [W, foldl_set_succ _ _ hap] using hm''
  · rintro v tr e' le' m' ⟨rfl, rfl, p, hap, hpe, rfl, hm', hf, hkp, ho⟩
    have ht' := ht.frame ho (by decide)
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hkp]
    wp_step
    simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]
    let le2 := PTree.set id.«k» (.Vint (ir ((p : Int) + 1))) (PTree.set (idOf 752) (.Vint (ir p)) le')
    have ho2 : ∀ x, x ∉ [id.«k», idOf 752] → PTree.get x le2 = PTree.get x le := fun x hx => by
      rw [temps_gso _ _ (fun h => hx (by simp [h])), temps_gso _ _ (fun h => hx (by simp [h])), ho x hx]
    have ht2 : Tmp le2 L t := ht.frame ho2 (by decide)
    apply wp_if_eval
    have h752 : Exec.evalExpr sge empty_env le2 m' (tv (idOf 752)) = some (.Vint (ir p)) := by
      simp only [Exec.evalExpr, le2]; rw [temps_gso _ _ (by decide), temps_gss]
    rw [eval_binop (eval_ptn hok hm' ht2 h752 rfl (by omega))
      (show Exec.evalExpr sge empty_env le2 m' (tv id.«level») = _ from ht2.level)]
    simp only [typeof, cop]
    have hpl := hr.ptnSmall p (by omega)
    rw [ir_lt (a := (L.level : Int)) (b := (t.ptn[p]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have hk2 : PTree.get id.«k» le2 = some (.Vint (ir ((p + 1 : Nat) : Int))) := by
      simp only [le2, temps_gss]; push_cast; rfl
    by_cases hpe' : p < e
    · rw [show decide ((L.level : Int) < (t.ptn[p]! : Int)) = true from
        decide_eq_true (by have := hin p hap hpe'; omega)]
      simp (config := {decide := true}) only [cop, ite_true]
      apply wp_skip
      exact ⟨e - (p + 1), by omega, by simp, rfl, p + 1, by omega, by omega, rfl,
        by simpa [W] using hm', hf, hk2, ho2⟩
    · have hpe2 : p = e := by omega
      subst hpe2
      rw [show decide ((L.level : Int) < (t.ptn[p]! : Int)) = false from
        decide_eq_false (by omega)]
      simp (config := {decide := true}) only [cop, ite_false]
      apply wp_break
      exact hQ le2 m' (by simpa [W, clearCell] using hm') hf hk2 ho2

end NautyVerified.Proofs.Sparse.Refine.Nontrivial

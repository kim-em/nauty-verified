import NautyVerified.Proofs.Sparse.Refine.Wide
import NautyVerified.Proofs.Refine.Guard
import NautyVerified.Proofs.Sparse.Refine.Ops

/-!
# The initial queue of `refine_sg`

`for (i = -1; (i = nextelement(active, m, i)) >= 0;) ACTIVE[nactive++] = i;`
fills `ACTIVE` with the members of `active` in ascending order:
`wp_queueLoop` follows HexGraphIso's `Refinement.queue` as
`iterF (queueStep active)` (`queue_eq`), with `ActiveScan` as the invariant
of the members found so far.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk pv)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph ActiveScan)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n}

theorem iterF_queue_none {a : Hex.GraphIso.Nauty.VSet n} {q : Array Nat} :
    ∀ F, iterF (queueStep a) F (q, none) = (q, none)
  | 0 => rfl
  | _ + 1 => rfl

theorem iterF_queue_some {a : Hex.GraphIso.Nauty.VSet n} {q : Array Nat} {i : Nat} (F : Nat) :
    iterF (queueStep a) (F + 1) (q, some i) = iterF (queueStep a) F (q.push i, a.nextElem (some i)) :=
  rfl

/-- `t` with queue `q`. -/
abbrev withQ (t : RefineSt n) (q : Array Nat) : RefineSt n := { t with queue := q }

/-- The temporaries the queue loop assigns besides `nactive`. -/
def queueTemps : List ident := [id.«i», idOf 711, idOf 712, idOf 713]

theorem type_nextelement :
    type_of_fundef (.Internal dense.fn.nextelement) = tfun [tptr tulong, tint, tint] tint := rfl

theorem nextelement_id : sparse.id.«nextelement» = dense.id.nextelement := rfl

/-- The queue loop's invariant: `q` holds the members found so far, `last`
the last one (in `i`). -/
def QueueInv (L : Loc) (G : Hex.SparseGraph n) (t : RefineSt n) (S : Scr) (m0 : mem)
    (le0 : temp_env) (q : Array Nat) (last : Option Nat) (le : temp_env) (m : mem) : Prop :=
  ∃ S' F', ActiveScan t.active q (t.active.nextElem last) ∧
    Hex.GraphIso.Nauty.Sparse.Refinement.queue t.active =
      (iterF (queueStep t.active) F' (q, t.active.nextElem last)).1 ∧ n ≤ F' + q.size ∧
    Mem m L G (withQ t q) S' ∧ (∀ i < q.size, S'.w2 i = .Vint (ir q[i]!)) ∧ S'.w1 = S.w1 ∧
    S'.w3 = S.w3 ∧ Tmp le L (withQ t q) ∧ Unch m0 m (· = L.b2) ∧
    (∀ z, Mem.valid_block m0 z → Mem.valid_block m z) ∧
    PTree.get id.«i» le = some (.Vint (ir (NautyVerified.Proofs.Refine.posOf last))) ∧
    (∀ p, last = some p → p < n) ∧ ∀ x, x ∉ queueTemps → x ≠ id.nactive → PTree.get x le = PTree.get x le0

theorem wp_queueLoop {Q : Post} {le : temp_env} {m : mem} {t : RefineSt n} {S : Scr}
    (hok : Ok n L) (hm : Mem m L G t S) (ht : Tmp le L t) (hq : t.queue = #[])
    (hi : PTree.get id.«i» le = some (.Vint (ir (-1))))
    (hQ : ∀ le' m' S', Mem m' L G (withQ t (Hex.GraphIso.Nauty.Sparse.Refinement.queue t.active)) S' →
      (∀ i < (Hex.GraphIso.Nauty.Sparse.Refinement.queue t.active).size,
        S'.w2 i = .Vint (ir (Hex.GraphIso.Nauty.Sparse.Refinement.queue t.active)[i]!)) →
      S'.w1 = S.w1 → S'.w3 = S.w3 →
      Tmp le' L (withQ t (Hex.GraphIso.Nauty.Sparse.Refinement.queue t.active)) →
      Unch m m' (· = L.b2) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ∉ queueTemps → x ≠ id.nactive → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F queueLoop Q empty_env le m := by
  have hnl := hok.nlt
  have hnM := hok.nM
  have hM1 := hok.M1
  have hMl := hok.Mlt
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q last, v = n - q.size ∧ QueueInv L G t S m le q last le' m'
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q last, n - q.size < v ∧ QueueInv L G t S m le q last le' m'
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0)
    ⟨rfl, rfl, #[], none, rfl, S, n, ActiveScan.initial _, queue_eq _, by simp,
      hm.congr rfl rfl rfl rfl, fun i hi => absurd hi (by simp), rfl, rfl,
      ht.congr rfl (by simp [hq]), Unch.refl _ _, fun _ h => h, hi, ⟨fun _ h => absurd h (by simp), fun _ _ _ => rfl⟩⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, q, last, rfl, S', F', hsc, hfin, hF, hm', hw2, hw1, hw3, ht', hu',
      hg', hi', hlast, ho'⟩
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    have hpos : NautyVerified.Proofs.Refine.posOf last < 64 * L.M := by
      cases last with
      | none => simp [NautyVerified.Proofs.Refine.posOf]; omega
      | some p =>
        simp only [NautyVerified.Proofs.Refine.posOf]
        have := hlast p rfl
        omega
    refine wp_call (vf := .Vptr NautyEnv.nextelement Ptrofs.zero) (targs := [tptr tulong, tint, tint])
      (tres := tint) (cc := Common.AST.cc_default) _
      (Nextelement.nextSpec L.ba L.aofs L.M (NautyVerified.Proofs.Refine.posOf last) S'.aw)
      (Nextelement.nextelement_satisfies _ _ _ _ _) rfl
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
        show PTree.get id.«nextelement» (empty_env : env) = none from rfl,
        show Genv.find_symbol sge.genv_genv id.«nextelement» = some NautyEnv.nextelement from
          NautyEnv.find_nextelement, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
      (by simp only [Exec.evalExprlist, Exec.evalExpr, ht'.active, ht'.m, hi', typeof, cop])
      (by simp [Common.Globalenvs.Genv.find_funct, NautyEnv.funct_nextelement]) type_nextelement
      ⟨rfl, by cases last <;> simp [NautyVerified.Proofs.Refine.posOf], hpos, hM1, by omega,
        Graph.wordsAt_of hm'.act, hm'.left⟩ ?_
    rintro t' r m2 ⟨rfl, rfl, r, rfl, hspec⟩
    have hnx := NautyVerified.Proofs.Refine.next_eq hm'.actRep hspec
    simp only [set_opttemp, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    apply wp_if_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss, typeof, cop]
    have ht3 := ((ht'.set (x := idOf 711) (.Vint (ir r)) (by decide)).set (x := idOf 712) (.Vint (ir r))
      (by decide)).set (x := id.«i») (.Vint (ir r)) (by decide)
    have ho3 : ∀ x, x ∉ queueTemps → PTree.get x (PTree.set id.«i» (.Vint (ir r))
        (PTree.set (idOf 712) (.Vint (ir r)) (PTree.set (idOf 711) (.Vint (ir r)) le'))) =
        PTree.get x le' := fun x hx => by
      simp only [queueTemps, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
      rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.2.1, temps_gso _ _ hx.2.1]
    rcases hnx with ⟨hn, rfl⟩ | ⟨v, hv, rfl⟩
    · rw [show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, ir_lt (a := -1) (b := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
      simp (config := {decide := true}) only [ite_false]
      apply wp_break
      have hqf : Hex.GraphIso.Nauty.Sparse.Refinement.queue t.active = q := by
        have hn' : t.active.nextElem last = none := hn
        rw [hfin, hn', iterF_queue_none]
      rw [hqf] at hQ
      exact hQ _ m2 S' hm' hw2 hw1 hw3 (ht3.congr rfl rfl) hu' hg' fun x hx h1 => by
        rw [ho3 x hx, ho' x hx h1]
    · have hvn : v < n := Hex.GraphIso.Nauty.VSet.mem_lt (Hex.GraphIso.Nauty.VSet.nextElem_mem hv)
      have hqv := hsc.progress v hv
      rw [show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, ir_lt (a := (v : Int)) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
      rw [show decide ((v : Int) < 0) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [ite_true]
      apply wp_skip
      simp only [E0_append]
      obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
      have ht4 := ht3.set (x := idOf 713) (.Vint (ir q.size)) (by decide)
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, ht3.nactive]
      apply wp_set_eval
      simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]
      have ht5 := ht4.setNactive (withQ t (q.push v)) rfl
      simp only [Array.size_push] at ht5
      refine wp_storeW2 (c := q.size) (x := v) hok hm' (by simp (config := {decide := true}) only
        [Exec.evalExpr, temps_gso, temps_gss]) rfl (by have := hok.c2; omega)
        (by simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, temps_gss]) rfl ?_
      intro m3 hm3 hu3 hg3
      refine ⟨by simp, rfl, q.push v, some v, by simp; omega, _, F'', hsc.step hv, ?_, by simp; omega,
        hm3.congr rfl rfl rfl rfl, ?_, hw1, hw3, ht5.congr rfl rfl, hu'.trans hu3,
        fun z h => hg3 _ (hg' _ h), ?_, fun p hp => by cases hp; exact hvn, fun x hx h1 => ?_⟩
      · rw [hfin, show t.active.nextElem last = some v from hv, iterF_queue_some]
      · intro i hi
        simp only [Array.size_push] at hi
        by_cases he : i = q.size
        · subst he; simp [upd]
        · show upd S'.w2 q.size _ i = _
          rw [upd_ne _ _ he, hw2 i (by omega)]
          rw [getElem!_pos (q.push v) i (by simp; omega), getElem!_pos q i (by omega),
            Array.getElem_push_lt]
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]; rfl
      · rw [temps_gso _ _ h1, temps_gso _ _ (by intro e; subst e; exact hx (by simp [queueTemps])),
          ho3 x hx, ho' x hx h1]
  · rintro v tr e' le' m' ⟨rfl, rfl, q, last, hlt, hinv⟩
    apply wp_skip
    exact ⟨n - q.size, hlt, by simp, rfl, q, last, rfl, hinv⟩

end NautyVerified.Proofs.Sparse.Refine

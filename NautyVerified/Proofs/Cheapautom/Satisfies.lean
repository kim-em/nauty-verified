import NautyVerified.Program.Env
import NautyVerified.Proofs.Cheapautom.Loop
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# `cheapautom` meets its specification

`cheapautomSpec`: called for an undirected graph (`digraph = FALSE`) with a
`ptn` array whose last cell is closed, nauty's `cheapautom` returns HexGraphIso's
`cheapautom ptn level n` (as 1 or 0), without changing memory or emitting events.
-/

namespace NautyVerified.Proofs.Cheapautom

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs

def cheapautomSpec (bp : block) (pofs : ptrofs) (ptn : Array Nat) (level n : Nat) : FunSpec where
  pre args m := args = [.Vptr bp pofs, .Vint (ir level), .Vint (ir 0), .Vint (ir n)] ∧
    ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n ∧
    ptn.size = n ∧ (∀ x < n, ptn[x]! < 2147483648) ∧ ptn[n - 1]! ≤ level ∧
    n < 1073741824 ∧ level < 2147483648
  post _ m t v m' := t = E0 ∧ m' = m ∧
    v = .Vint (ir (if Hex.GraphIso.Nauty.cheapautom ptn level n then 1 else 0))

def entryTemps (bp : block) (pofs : ptrofs) (level n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.digraph (.Vint (ir 0))
    (PTree.set id.level (.Vint (ir level)) (PTree.set id.ptn (.Vptr bp pofs)
      (create_undef_temps Source.dense.fn.cheapautom.fn_temps))))

theorem cheapautom_satisfies {xi : ExternalCalls} (bp : block) (pofs : ptrofs) (ptn : Array Nat)
    (level n : Nat) :
    Satisfies xi ge (.Internal Source.dense.fn.cheapautom) (cheapautomSpec bp pofs ptn level n) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bp pofs level n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bp pofs level n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, harr, hsz, hsm, hlast, hn, hlev⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.cheapautom.fn_body_eq, body_eq]
    have hf : Frame m (entryTemps bp pofs level n) bp pofs ptn level n :=
      { hptn := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hlev := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hn := by simp (config := {decide := true}) only [entryTemps, temps_gss]
        arr := harr, size := hsz, small := hsm, last := hlast, nlt := by omega, levlt := hlev }
    simp only [body]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp (config := {decide := true}) only [Exec.evalExpr, entryTemps, temps_gso, temps_gss, typeof,
      cop]
    rw [ite_eq_right (by simp)]
    apply wp_skip
    wp_step; wp_step; wp_step; wp_step
    simp only [temps_gss]
    wp_step; wp_step; wp_step; wp_step
    let le2 := PTree.set id.nnt (.Vint (ir 0)) (PTree.set id.k (.Vint (ir n)) (entryTemps bp pofs level n))
    have hf2 : Frame m le2 bp pofs ptn level n :=
      hf.temps fun x _ h2 h3 _ _ => by simp only [le2]; rw [temps_gso _ _ h3, temps_gso _ _ h2]
    wp_step
    refine wp_cells hf2 (by rw [temps_gso _ _ (by decide), temps_gss])
      (by rw [temps_gss]) ?_
    intro le3 hk3 hn3 ho3
    dsimp only
    obtain ⟨K, NN, hR⟩ : ∃ K NN, Hex.GraphIso.Nauty.cheapautom.go ptn level n 0 n 0 = (K, NN) :=
      ⟨_, _, rfl⟩
    rw [hR] at hk3 hn3
    -- the counts are bounded by `n`
    have hb : K ≤ n ∧ NN ≤ n := by
      have := go_bound ptn level n 0 n 0
      rw [hR] at this; simp at this; omega
    have hRes : Hex.GraphIso.Nauty.cheapautom ptn level n = decide (K ≤ NN + 1 ∨ K ≤ 4) := by
      simp only [Hex.GraphIso.Nauty.cheapautom, hR]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hk3, hn3, typeof, cop, ir_add]
    rw [ir_lt (a := (NN : Int) + 1) (b := (K : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases h1 : K ≤ NN + 1
    · rw [ite_eq_left (by simp; omega)]
      apply wp_set_eval
      simp only [Exec.evalExpr]
      apply wp_return_some_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop, Source.dense.fn.cheapautom.fn_return_eq,
        Nextelement.free_empty]
      refine ⟨rfl, rfl, ?_⟩
      rw [hRes, decide_eq_true (.inl h1)]; rfl
    · rw [ite_eq_right (by simp; omega)]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hk3, typeof, cop]
      rw [ir_lt (a := 4) (b := (K : Int)) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩]
      have hR' : Hex.GraphIso.Nauty.cheapautom ptn level n = decide (K ≤ 4) := by
        rw [hRes]; apply decide_eq_decide.2; omega
      by_cases h2 : K ≤ 4
      · rw [show (!decide ((4 : Int) < K)) = true by simp; omega]
        simp only [Val.of_bool, ite_true, Vtrue, cop,
          show Lib.Integers.Int.eq Lib.Integers.Int.one Lib.Integers.Int.zero = false from rfl,
          Bool.false_eq_true, ite_false]
        apply wp_return_some_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop, Source.dense.fn.cheapautom.fn_return_eq,
          Nextelement.free_empty]
        refine ⟨rfl, rfl, ?_⟩
        rw [hR', decide_eq_true h2]; rfl
      · rw [show (!decide ((4 : Int) < K)) = false by simp; omega]
        simp only [Val.of_bool, Bool.false_eq_true, ite_false, Vfalse, cop,
          show Lib.Integers.Int.eq Lib.Integers.Int.zero Lib.Integers.Int.zero = true from rfl,
          ite_true]
        apply wp_return_some_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop, Source.dense.fn.cheapautom.fn_return_eq,
          Nextelement.free_empty]
        refine ⟨rfl, rfl, ?_⟩
        rw [hR', decide_eq_false h2]; rfl

end NautyVerified.Proofs.Cheapautom

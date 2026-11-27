import NautyVerified.Proofs.Isautom.Scan
import HexGraphIso.Nauty.Cert.Translator

/-!
# `isautom` meets its specification

`isautomSpec`: called for an undirected graph (`digraph = FALSE`) on `n`
vertices with `M` words per row and an array `perm` of vertices, nauty's
`isautom` returns HexGraphIso's `isautom ⟨rows⟩ perm` (as 1 or 0), without
changing memory or emitting events.
-/

namespace NautyVerified.Proofs.Isautom

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs BitTable)
open NautyVerified.Proofs.Graph (GraphAt)
open Hex.GraphIso.Nauty (VSet)

theorem isautom_iff_rows {n : Nat} (rows : Array (VSet n)) (perm : Array Nat) :
    Hex.GraphIso.Nauty.isautom ⟨rows⟩ perm = true ↔ ∀ i < n, RowOK rows perm i := by
  rw [Hex.GraphIso.Nauty.isautom_iff]
  constructor
  · intro h i hi pos hm hlt
    exact h i hi pos (VSet.mem_toList.2 hm) hlt
  · intro h i hi pos hm hlt
    exact h i hi pos (VSet.mem_toList.1 hm) hlt

def isautomSpec {n : Nat} (bg : block) (gofs : ptrofs) (gw : Nat → Lib.Integers.int64)
    (rows : Array (VSet n)) (bpm : block) (pofs : ptrofs) (perm : Array Nat) (M : Nat) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bpm pofs, .Vint (ir 0), .Vint (ir M), .Vint (ir n)] ∧
    GraphAt m bg gofs gw rows M ∧
    ArrayAt m .Mint32 bpm (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n ∧
    (∀ x, x < n → perm[x]! < n) ∧ BitTable m Block.naugraphBit ∧ Nextelement.LeftbitTable m ∧
    1 ≤ M ∧ 64 * M < 2147483648 ∧ n ≤ 64 * M
  post _ m t v m' := t = E0 ∧ m' = m ∧
    v = .Vint (ir (if Hex.GraphIso.Nauty.isautom ⟨rows⟩ perm then 1 else 0))

def entryTemps (bg : block) (gofs : ptrofs) (bpm : block) (pofs : ptrofs) (n M : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.digraph (.Vint (ir 0)) (PTree.set id.perm (.Vptr bpm pofs)
      (PTree.set id.g (.Vptr bg gofs) (create_undef_temps Source.dense.fn.isautom.fn_temps)))))

theorem isautom_satisfies {xi : ExternalCalls} {n : Nat} (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (rows : Array (VSet n)) (bpm : block) (pofs : ptrofs)
    (perm : Array Nat) (M : Nat) :
    Satisfies xi ge (.Internal Source.dense.fn.isautom) (isautomSpec bg gofs gw rows bpm pofs perm M) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bg gofs bpm pofs n M ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bg gofs bpm pofs n M, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hg, hparr, hps, hbit, hlb, hM1, hM64, hnM⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.isautom.fn_body_eq, body_eq]
    have hn : n < 2147483648 := by omega
    have hf : Frame m (entryTemps bg gofs bpm pofs n M) bg gofs gw rows bpm pofs perm M :=
      { hg := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hperm := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hm := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hn := by simp (config := {decide := true}) only [entryTemps, temps_gss]
        hdig := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        graph := hg, parr := hparr, psmall := hps, bit := hbit, lb := hlb, M1 := hM1, M64 := hM64,
        nM := hnM }
    let base := intOfZ (Ptrofs.unsigned gofs)
    let le0 := entryTemps bg gofs bpm pofs n M
    let Oth := fun le' : temp_env => ∀ x, x ≠ id.pg → x ≠ id.pos → x ≠ id.pgp → x ≠ id.posp →
      x ≠ id.i → x ≠ id.t1 → x ≠ id.t2 → x ≠ id.t3 → PTree.get x le' = PTree.get x le0
    let I := fun (k : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
      e' = empty_env ∧ m' = m ∧ ∃ c, c ≤ n ∧ k = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
        PTree.get id.pg le' = some (.Vptr bg (ptrTo base 8 (M * c))) ∧
        (∀ v < c, RowOK rows perm v) ∧ Oth le'
    let J := fun (k : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
      e' = empty_env ∧ m' = m ∧ ∃ c, c < n ∧ k = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
        PTree.get id.pg le' = some (.Vptr bg (ptrTo base 8 (M * c))) ∧
        (∀ v < c + 1, RowOK rows perm v) ∧ Oth le'
    simp only [body]
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hf.hg]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0)
      ⟨rfl, rfl, rfl, 0, Nat.zero_le _, rfl, temps_gss _ _ _, by
        rw [temps_gso _ _ (by decide), temps_gss, Nat.mul_zero, Graph.ptrTo_zero],
        fun v hv => absurd hv (by omega), fun x h1 _ _ _ h5 _ _ _ => by
          rw [temps_gso _ _ h5, temps_gso _ _ h1]⟩
    · rintro k t e' le' m' ⟨rfl, rfl, rfl, c, hc, rfl, hi, hpg, hrows, ho⟩
      have hf' := hf.temps fun x h1 h2 h3 h4 h5 h6 h7 h8 => ho x h1 h2 h3 h4 h5 h6 h7 h8
      wp_step; wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' _ (tv id.i) = _ from hi,
        show Exec.evalExpr ge empty_env le' _ (tv id.n) = _ from hf'.hn]
      simp only [typeof, cop]
      rw [ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hcn : c < n
      · rw [ite_eq_left (by simpa using hcn)]
        apply wp_skip
        have hpc := hps c hcn
        have hpe := eval_at (ge := ge) (e := empty_env) hparr hn id.perm hf'.hperm (tv id.i) c hcn hi rfl
        wp_step; wp_step; wp_step
        apply wp_set_eval
        have e1 : Exec.evalExpr ge empty_env le' m' (.Ecast (Set.pv id.g) (tptr tulong)) =
            some (.Vptr bg gofs) := by simp only [Exec.evalExpr, hf'.hg, typeof, cop]
        have e3 : Exec.evalExpr ge empty_env le' m' (.Ecast (permAt (tv id.i)) tulong) =
            some (.Vlong (lr (perm[c]! : Int))) := by
          rw [Exec.evalExpr, hpe]
          simp only [ints, typeof, cop, cast_int_long_ir (a := (perm[c]! : Int)) ⟨by omega, by omega⟩]
        rw [Exec.evalExpr, e1, Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' (tv id.m) = _ from hf'.hm, e3]
        simp only [typeof, cop, Graph.mul_lr (show M < 2147483648 by omega)]
        have hpgpv : Ptrofs.add gofs (Ptrofs.mul (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong))
            (Ptrofs.of_int64 (lr ((M : Int) * (perm[c]! : Int))))) = ptrTo base 8 (M * perm[c]!) := by
          rw [show ((M : Int) * (perm[c]! : Int)) = ((M * perm[c]! : Nat) : Int) by push_cast; rfl]
          exact Graph.add_ptrTo_long _ _ _
        rw [hpgpv]
        let le2 := PTree.set id.pgp (.Vptr bg (ptrTo base 8 (M * perm[c]!))) le'
        have ho2 : ∀ x, x ≠ id.pgp → PTree.get x le2 = PTree.get x le' := fun x hx => temps_gso _ _ hx
        wp_step; wp_step; wp_step; wp_step
        apply wp_if_eval
        simp only [Exec.evalExpr]
        rw [ho2 _ (by decide), hf'.hdig]
        simp only [typeof, cop]
        rw [ite_eq_right (by decide)]
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr]
        rw [ho2 _ (by decide), hi]
        simp only [typeof, cop]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss]
        refine wp_scan (v := c) (hf'.temps fun x _ h2 h3 _ _ h6 _ _ => by
            rw [temps_gso _ _ h2, temps_gso _ _ h6, ho2 x h3]) hcn ?_ ?_ (temps_gss _ _ _) ?_ ?_
        · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), ho2 _ (by decide)]; exact hpg
        · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]
        · intro hrow le5 ho5
          refine ⟨by simp, rfl, rfl, c, hcn, rfl, ?_, ?_, fun v hv => ?_, fun x h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
          · rw [ho5 _ (by decide) (by decide) (by decide) (by decide), temps_gso _ _ (by decide),
              temps_gso _ _ (by decide), ho2 _ (by decide)]; exact hi
          · rw [ho5 _ (by decide) (by decide) (by decide) (by decide), temps_gso _ _ (by decide),
              temps_gso _ _ (by decide), ho2 _ (by decide)]; exact hpg
          · rcases Nat.lt_or_ge v c with h | h
            · exact hrows v h
            · rw [show v = c by omega]; exact hrow
          · rw [ho5 x h2 h4 h7 h8, temps_gso _ _ h2, temps_gso _ _ h6, ho2 x h3, ho x h1 h2 h3 h4 h5 h6 h7 h8]
        · intro hbad
          refine ⟨by simp, rfl, ?_⟩
          have : Hex.GraphIso.Nauty.isautom ⟨rows⟩ perm = false := by
            cases hh : Hex.GraphIso.Nauty.isautom ⟨rows⟩ perm with
            | false => rfl
            | true => exact absurd ((isautom_iff_rows rows perm).1 hh c hcn) hbad
          rw [this]; rfl
      · rw [ite_eq_right (by simpa using hcn)]
        apply wp_break
        have hall : ∀ v < n, RowOK rows perm v := fun v hv => hrows v (by omega)
        wp_step; wp_step
        apply wp_return_some_eval
        simp only [Exec.evalExpr, typeof, cop, Source.dense.fn.isautom.fn_return_eq,
          Nextelement.free_empty]
        refine ⟨by simp, rfl, ?_⟩
        rw [(isautom_iff_rows rows perm).2 hall]; rfl
    · rintro k t e' le' m' ⟨rfl, rfl, rfl, c, hcn, rfl, hi, hpg, hrows, ho⟩
      have hf' := hf.temps fun x h1 h2 h3 h4 h5 h6 h7 h8 => ho x h1 h2 h3 h4 h5 h6 h7 h8
      wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hpg, hf'.hm, typeof, cop]
      rw [Prune.Long.add_ptrTo8 _ _ _ _ (by omega)]
      apply wp_set_eval
      simp only [Exec.evalExpr]
      rw [temps_gso _ _ (by decide), hi]
      simp only [typeof, cop, ir_add]
      refine ⟨n - (c + 1), by omega, by simp, rfl, rfl, c + 1, by omega, rfl, by rw [temps_gss]; rfl,
        ?_, hrows, fun x h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
      · rw [temps_gso _ _ (by decide), temps_gss, Nat.mul_succ]
      · rw [temps_gso _ _ h5, temps_gso _ _ h1, ho x h1 h2 h3 h4 h5 h6 h7 h8]

end NautyVerified.Proofs.Isautom

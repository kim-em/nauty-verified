import NautyVerified.Proofs.Orbjoin.Loops
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# `orbjoin` meets its specification

`orbjoinSpec`: called with an `orbits` array holding a descending orbit forest
`o`, a `map` array (in another block) holding `mp` with entries below `n`,
and `n`, nauty's `orbjoin` leaves in `orbits` exactly HexGraphIso's
`(orbjoin o mp n).1`, returns its `(orbjoin o mp n).2`, changes nothing
outside the `orbits` block, and emits no events.
-/

namespace NautyVerified.Proofs.Orbjoin

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open Hex.GraphIso.Nauty.Orbit

def orbjoinSpec (bo : block) (ofs : ptrofs) (bm : block) (mofs : ptrofs) (o mp : Array Nat)
    (n : Nat) : FunSpec where
  pre args m := args = [.Vptr bo ofs, .Vptr bm mofs, .Vint (ir n)] ∧
    ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n ∧
    ArrayAt m .Mint32 bm (intOfZ (Ptrofs.unsigned mofs)) (ints mp) n ∧
    bo ≠ bm ∧ n < 2147483648 ∧ (∀ i < n, mp[i]! < n) ∧ Descending o n
  post _ m t v m' := t = E0 ∧ v = .Vint (ir (Hex.GraphIso.Nauty.orbjoin o mp n).2) ∧
    ArrayAt m' .Mint32 bo (intOfZ (Ptrofs.unsigned ofs))
      (ints (Hex.GraphIso.Nauty.orbjoin o mp n).1) n ∧ Unch m m' (· = bo)

def entryTemps (bo : block) (ofs : ptrofs) (bm : block) (mofs : ptrofs) (n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.map (.Vptr bm mofs)
    (PTree.set id.orbits (.Vptr bo ofs) (create_undef_temps Source.dense.fn.orbjoin.fn_temps)))

theorem orbjoin_satisfies {xi : ExternalCalls} (bo : block) (ofs : ptrofs) (bm : block)
    (mofs : ptrofs) (o mp : Array Nat) (n : Nat) :
    Satisfies xi ge (.Internal Source.dense.fn.orbjoin) (orbjoinSpec bo ofs bm mofs o mp n) := by
  refine satisfies_internal
    (Entry := fun _ m₀ e le m => e = empty_env ∧ le = entryTemps bo ofs bm mofs n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bo ofs bm mofs n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, harr, hmarr, hne, hn, hmlt, hd⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.orbjoin.fn_body_eq, body_eq]
    have hf : Frame m (entryTemps bo ofs bm mofs n) bo ofs bm mofs o mp n :=
      { horb := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hmap := by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hn := by simp (config := {decide := true}) only [entryTemps, temps_gss]
        arr := harr, marr := hmarr, hne := hne, nlt := hn, mlt := hmlt, desc := hd }
    simp only [body]
    wp_step
    refine wp_joinLoop hf ?_
    intro le1 m1 hf1 hu1
    simp only [E0_append]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, E0_append]
    wp_step
    refine wp_compressLoop (hf1.temps fun k hk => ?_) (temps_gss _ _ _) ?_
    · rw [temps_gso _ _ (by rcases hk with rfl | rfl | rfl <;> decide)]
    intro le2 m2 hf2 hj hu2
    simp only [E0_append]
    wp_step; wp_step
    apply wp_return_some_eval
    simp only [Exec.evalExpr, hj, typeof, cop, Source.dense.fn.orbjoin.fn_return_eq,
      Nextelement.free_empty]
    simp only [orbjoinSpec, orbjoin_eq]
    exact ⟨trivial, trivial, hf2.arr, hu1.trans hu2⟩

end NautyVerified.Proofs.Orbjoin

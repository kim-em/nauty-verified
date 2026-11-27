import NautyVerified.Proofs.Nextelement.Body
import NautyVerified.Spec.VSet

/-!
# `nextelement` meets its specification

`nextSpec b ofs n pos ws`: called with the set at `b + ofs` (words `ws`), `m = n`
words and `pos`, nauty's `nextelement` returns, without changing memory or
emitting events, the least member above `pos` or `-1` (`NextSpec`).
-/

namespace NautyVerified.Proofs.Nextelement

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word

theorem norepet_of_nodup {A : Type} : ∀ {l : List A}, l.Nodup → list_norepet l
  | [], _ => .nil _
  | _ :: _, h => .cons _ (List.nodup_cons.1 h).1 (norepet_of_nodup (List.nodup_cons.1 h).2)

theorem disjoint_of {A : Type} {l1 l2 : List A} (h : ∀ x ∈ l1, ∀ y ∈ l2, x ≠ y) :
    list_disjoint l1 l2 := fun x y hx hy => h x hx y hy

/-- The specification of `nextelement`. -/
def nextSpec (b : block) (ofs : ptrofs) (n : Nat) (pos : Int) (ws : Nat → Lib.Integers.int64) :
    FunSpec where
  pre args m := args = [.Vptr b ofs, .Vint (ir n), .Vint (ir pos)] ∧ -1 ≤ pos ∧ pos < 64 * n ∧
    1 ≤ n ∧ 64 * n < 2147483648 ∧ WordsAt m b ofs ws n ∧ LeftbitTable m
  post _ m t v m' := t = E0 ∧ m' = m ∧
    ∃ r : Int, v = .Vint (ir r) ∧ NextSpec (fun i => bv64 (ws i)) n pos r

/-- The temporaries on entry. -/
def entryTemps (b : block) (ofs : ptrofs) (n : Nat) (pos : Int) : temp_env :=
  PTree.set id.pos (.Vint (ir pos)) (PTree.set id.m (.Vint (ir n))
    (PTree.set id.set1 (.Vptr b ofs) (create_undef_temps Source.dense.fn.nextelement.fn_temps)))

theorem nextelement_satisfies {xi : ExternalCalls} (b : block) (ofs : ptrofs) (n : Nat) (pos : Int)
    (ws : Nat → Lib.Integers.int64) :
    Satisfies xi ge (.Internal Source.dense.fn.nextelement) (nextSpec b ofs n pos ws) := by
  refine satisfies_internal
    (Entry := fun _ m₀ e le m => e = empty_env ∧ le = entryTemps b ofs n pos ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps b ofs n pos, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact norepet_of_nodup (by decide)
    · exact disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hp1, hp2, hn1, hn, hw, hlb⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.nextelement.fn_body_eq, body_eq]
    refine wp_body (n := n) (pos := pos) (ws := ws) ?_ ?_ ?_ hp1 hp2 hn1 hn hw hlb ?_
    · simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    · simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    · simp (config := {decide := true}) only [entryTemps, temps_gss]
    · intro r hr
      exact ⟨rfl, rfl, r, rfl, hr⟩

/-- nauty's result determines HexGraphIso's `VSet.nextElem`, for a `VSet` whose
members are those of the C set: `-1` is `none`, anything else the position. -/
theorem nextElem_of_nextSpec {nv : Nat} {s : Hex.GraphIso.Nauty.VSet nv} {ws : Nat → BitVec 64}
    {n : Nat} (hrep : ∀ v, s.mem v = decide (InSet ws n v)) (hnv : nv ≤ 64 * n)
    {pos : Option Nat} {r : Int} (h : NextSpec ws n (Spec.posOf pos) r) :
    s.nextElem pos = if r = -1 then none else some r.toNat := by
  rcases h with ⟨rfl, hnone⟩ | ⟨v, rfl, hv, hin, hmin⟩
  · rw [ite_eq_left rfl]
    exact Spec.nextElem_eq_none hrep hnv
      (fun u hu1 _ => by simpa using hnone u hu1)
  · rw [ite_eq_right (by omega)]
    rw [Spec.nextElem_eq_some hrep ⟨hv, by simpa using hin,
      fun u hu1 hu2 => by simpa using hmin u hu1 hu2⟩]
    simp

end NautyVerified.Proofs.Nextelement

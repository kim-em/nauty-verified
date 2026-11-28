import NautyVerified.Spec.SearchInfRun
import NautyVerified.Spec.Gca

/-!
# What nauty.c's search nodes need of HexGraphIso's state

The C search runs HexGraphIso's search with `inf = nautyInfinity`
(`Spec/SearchInfRun.lean`). `NodeOk G first level numcells st`: the state `st`
of that run, at a node call, is the image under `tw (phi (n + 2)
nautyInfinity) t` of a state `st₂` of HexGraphIso's own run (`inf = n + 2`)
meeting the node precondition of the inf contract: HexGraphIso's partition
invariant `SearchOk`, the contract's `Inv`, and on the first path the identity
orbits and the first-path codes so far, off it a first leaf (`Depth`).

`nodeOk_run`: such a node call is the renamed image of HexGraphIso's node call
on `st₂`; `nodeOk_noFuel`: with nauty's fuel `n + 3 - level` it never returns
`.fuel`. `nodeOk_root`: the root call of `nauty()` satisfies `NodeOk`.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {n k : Nat}

/-- The renamed-run part of `NodeOk`. -/
def NodeOk₀ (G : Colored n k) (first : Bool) (level numcells : Nat) (st : Search n) : Prop :=
  ∃ t st₂, st = tw (phi (n + 2) nautyInfinity) t st₂ ∧ 1 ≤ level ∧ SearchOk G level numcells st₂ ∧
    Inv st₂ ∧ (first = true → OrbId st₂ ∧ AgreeTo (level - 1) t st₂.firsttc) ∧
    (first = false → ∃ last, Depth last st₂ ∧ AgreeTo (last + 1) t st₂.firsttc)

/-- The node precondition nauty.c's search nodes need of HexGraphIso's state: the
renamed-run part, and off the first path the level counters (`GcaOk`). -/
def NodeOk (G : Colored n k) (first : Bool) (level numcells : Nat) (st : Search n) : Prop :=
  NodeOk₀ G first level numcells st ∧ (first = false → GcaOk level st)

/-- A node call satisfying `NodeOk` is the renamed image of HexGraphIso's call. -/
theorem nodeOk_run {G : Colored n k} {first : Bool} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : NodeOk G first level numcells st)
    (ctx : Ctx n) (tcLevel fuel : Nat) :
    ∃ t' st₂, SearchOk G level numcells st₂ ∧
      node first ctx nautyInfinity tcLevel fuel level numcells st =
        ((node first ctx (n + 2) tcLevel fuel level numcells st₂).1,
          tw (phi (n + 2) nautyInfinity) t' (node first ctx (n + 2) tcLevel fuel level numcells st₂).2) := by
  obtain ⟨⟨t, st₂, rfl, hlevel, hok, hinv, hfirst, hoff⟩, -⟩ := h
  have hpost := Generic.node_sound (infPolicy (G := G) (ctx := ctx) (tcLevel := tcLevel)
    (B := nautyInfinity) hn0 hn) first fuel level numcells st₂ ⟨hlevel, hok⟩
  obtain ⟨-, himp⟩ := hpost
  obtain ⟨hoffP, hfirstP⟩ := himp hinv
  cases first with
  | true =>
    obtain ⟨horb, hag⟩ := hfirst rfl
    obtain ⟨t', heq, -, -⟩ := hfirstP rfl t horb hag
    refine ⟨t', st₂, hok, ?_⟩
    rw [node_eq_generic, node_eq_generic]; exact heq
  | false =>
    obtain ⟨last, hd, hag⟩ := hoff rfl
    obtain ⟨heq, -, -, -⟩ := hoffP rfl last t hd hag
    refine ⟨t, st₂, hok, ?_⟩
    rw [node_eq_generic, node_eq_generic]; exact heq

/-- With nauty's node fuel, a node call satisfying `NodeOk` never runs out of fuel. -/
theorem nodeOk_noFuel {G : Colored n k} {first : Bool} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : NodeOk G first level numcells st)
    (ctx : Ctx n) (tcLevel : Nat) (hlev : level ≤ n) :
    (node first ctx nautyInfinity tcLevel (n + 3 - level) level numcells st).1 ≠ .fuel := by
  have hlevel : 1 ≤ level := by obtain ⟨⟨_, _, _, h1, _⟩, _⟩ := h; exact h1
  obtain ⟨t', st₂, hok, heq⟩ := nodeOk_run hn0 hn h ctx tcLevel (n + 3 - level)
  rw [heq]
  exact node_noFuel first hn0 hlevel hok (by omega)

/-- The root call of `nauty()` satisfies `NodeOk`. -/
theorem nodeOk_root (G : Colored n k) (hn0 : 0 < n) :
    NodeOk G true 1 (initialPartition G).2.length
      (initialC n (initialPartition G).1 (initialPartition G).2) := by
  refine ⟨⟨.replicate (n + 2) 0, initial n (initialPartition G).1 (initialPartition G).2,
    initialC_eq _ _ _, Nat.le_refl _, initial_ok G hn0, ⟨by show 1 ≤ n + 1; omega, by simp [initial]⟩,
    fun _ => ⟨?_, ?_⟩, fun h => absurd h (by decide)⟩, fun h => absurd h (by decide)⟩
  · intro v hv
    show (Array.ofFn (n := n) fun i => i.val)[v]! = v
    rw [getElem!_pos _ v (by simpa using hv)]
    simp
  · exact ⟨by simp [initial], fun i h1 h2 => absurd h2 (by omega)⟩

end NautyVerified.Spec.SearchInf

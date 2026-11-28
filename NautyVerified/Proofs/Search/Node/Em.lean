import NautyVerified.Proofs.Search.Node.OtherHex
import NautyVerified.Proofs.Search.Node.FirstHex
import NautyVerified.Proofs.Search.Node.Process

/-!
# What a node emits, from what its children emit

The node specifications take the emitted words `Em first level numcells st`
as a parameter. A node emits through its children (and, off the first path,
through `processnode` at a leaf), so `Em` is pinned down by two laws, one per
kind of node, stated with the sweeps' emissions:

- `sweepEm Em ctx level nc tc tv1 cfuel tv tcell st`: an off-path sweep from
  vertex `tv`, child by child as `sweep false` runs them (`otherChild`);
- `sweepEmFirst`: the same for a first-path sweep (`firstChild`), where only
  orbit representatives are entered and the child at `tv1` is on the first
  path.

`EmLawOff Em ctx` and `EmLawFirst Em ctx` say that `Em` satisfies the law at
every node; they follow `node_false_succ` and `node_true_succ`.
-/

namespace NautyVerified.Proofs.Search

open NautyVerified NautyVerified.Spec
open Hex.GraphIso.Nauty

variable {n : Nat}

/-- What an off-path sweep emits from vertex `tv` on. -/
def sweepEm (Em : Bool → Nat → Nat → Search n → List Int) (ctx : Ctx n)
    (level nc tc tv1 : Nat) : Nat → Option Nat → VSet n → Search n → List Int
  | _, none, _, _ => []
  | 0, some _, _, _ => []
  | cfuel + 1, some tv, tcell, st =>
    Em false (level + 1) (nc + 1) (child false level tc tv st) ++
      match otherChild ctx nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv tcell st with
      | (.done, tcell', st') => sweepEm Em ctx level nc tc tv1 cfuel (tcell'.nextElem (some tv)) tcell' st'
      | _ => []

/-- What a first-path sweep emits from vertex `tv` on. -/
def sweepEmFirst (Em : Bool → Nat → Nat → Search n → List Int) (ctx : Ctx n)
    (level nc tc tv1 : Nat) : Nat → Option Nat → VSet n → Search n → List Int
  | _, none, _, _ => []
  | 0, some _, _, _ => []
  | cfuel + 1, some tv, tcell, st =>
    (if st.orbits[tv]! == tv then Em (tv == tv1) (level + 1) (nc + 1) (child true level tc tv st)
      else []) ++
      match firstChild ctx nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv tcell st with
      | (.done, tcell', st') =>
        sweepEmFirst Em ctx level nc tc tv1 cfuel (tcell'.nextElem (some tv)) tcell' st'
      | _ => []

/-- `Em` at off-path nodes: `processnode`'s words, then, at an internal node,
the sweep's. -/
def EmLawOff (Em : Bool → Nat → Nat → Search n → List Int) (ctx : Ctx n) : Prop :=
  ∀ level nc st, 1 ≤ level → level ≤ n →
    Em false level nc st =
      let v := visit ctx level nc st
      let st₁ := compareCodes level v.2.1 v.2.2
      let ct := chooseTarget false ctx 100 level v.1 st₁
      let lx := procExit ctx level v.1 ct.2.2.2
      procWords ctx level v.1 ct.2.2.2 ++
        if lx.1 matches .done then
          sweepEm Em ctx level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1)
            (ct.2.1.nextElem none) ct.2.1 (cheapCheck false level lx.2)
        else []

/-- `Em` at first-path nodes: nothing at the first leaf, else the sweep's. -/
def EmLawFirst (Em : Bool → Nat → Nat → Search n → List Int) (ctx : Ctx n) : Prop :=
  ∀ level nc st, 1 ≤ level → level ≤ n →
    Em true level nc st =
      let v := visit ctx level nc st
      let st₁ := recordFirst level v.2.1 v.2.2
      let ct := chooseTarget true ctx 100 level v.1 st₁
      if v.1 = n then [] else
        sweepEmFirst Em ctx level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1)
          (ct.2.1.nextElem none) ct.2.1 (cheapCheck true level ct.2.2.2)

end NautyVerified.Proofs.Search

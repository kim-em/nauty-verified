import NautyVerified.Proofs.Search.Node.Spec

/-!
# HexGraphIso's off-path node, step by step

`node_false_succ` and `sweep_false_some` unfold `node false` and one step of
`sweep false` into the order nauty.c's `othernode0` runs them: refine
(`visit`), compare codes (`compareCodes`), choose the target cell
(`chooseTarget false`), classify the node (`classify`, `leafExit`), test for a
cheap automorphism (`cheapCheck false`), then sweep the target cell; each child
(`otherChild`) individualizes a vertex (`child`), recurses, erases the fixed
point, and on return prunes the cell (`shortprune` on request, `longprune`
after the first child) and recovers the partition (`recover`).
-/

namespace NautyVerified.Proofs.Search

open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {n : Nat}

/-- One child of an off-path sweep: the exit, the pruned target cell, the state. -/
def otherChild (ctx : Ctx n) (inf tl fuel level nc tc tv1 tv : Nat) (tcell : VSet n)
    (st : Search n) : Exit × VSet n × Search n :=
  let r := node false ctx inf tl fuel (level + 1) (nc + 1) (child false level tc tv st)
  let st := { r.2 with fixedpts := r.2.fixedpts.erase tv }
  match r.1 with
  | .fuel => (.fuel, tcell, st)
  | .unwind target short =>
    if target < level then (.unwind target short, tcell, st) else
      let tcell := if short then shortprune tcell st else tcell
      let tcell := if tv == tv1 then longprune tcell st.fixedpts st.autos else tcell
      (.done, tcell, Hex.GraphIso.Nauty.recover inf level st)
  | .done =>
    let tcell := if tv == tv1 then longprune tcell st.fixedpts st.autos else tcell
    (.done, tcell, Hex.GraphIso.Nauty.recover inf level st)

theorem sweep_false_none (ctx : Ctx n) (inf tl fuel cfuel level nc tc tv1 index : Nat)
    (tcell : VSet n) (st : Search n) :
    sweep false ctx inf tl fuel cfuel level nc tc tv1 none tcell index st = (.done, index, st) := by
  rw [sweep]

theorem sweep_false_some (ctx : Ctx n) (inf tl fuel cfuel level nc tc tv1 tv index : Nat)
    (tcell : VSet n) (st : Search n) :
    sweep false ctx inf tl fuel (cfuel + 1) level nc tc tv1 (some tv) tcell index st =
      match otherChild ctx inf tl fuel level nc tc tv1 tv tcell st with
      | (.done, tcell', st') =>
        sweep false ctx inf tl fuel cfuel level nc tc tv1 (tcell'.nextElem (some tv)) tcell' index st'
      | (e, _, st') => (e, index, st') := by
  rw [sweep]
  simp only [Id.run, pure, otherChild, Bool.not_false, Bool.true_or, ite_true,
    Bool.false_and, Bool.false_eq_true, ite_false]
  rcases (node false ctx inf tl fuel (level + 1) (nc + 1) (child false level tc tv st)).1 with
    _ | ⟨target, short⟩ | _
  · cases htv : tv == tv1 <;> simp only [htv, Bool.true_and, ite_true, ite_false,
      Bool.false_eq_true] <;> rfl
  · by_cases ht : target < level
    · simp [ht]
    · cases htv : tv == tv1 <;> cases short <;> simp only [ht, htv, Bool.true_and, ite_true,
        ite_false, Bool.false_eq_true] <;> rfl
  · rfl

/-- `node false` with fuel left, as `othernode0` runs it. -/
theorem node_false_succ (ctx : Ctx n) (inf tl fuel level nc : Nat) (st : Search n) :
    node false ctx inf tl (fuel + 1) level nc st =
      let v := visit ctx level nc st
      let st₁ := compareCodes level v.2.1 v.2.2
      let ct := chooseTarget false ctx tl level v.1 st₁
      let cl := classify ctx level v.1 ct.2.2.2
      let lx := leafExit cl.1 level cl.2
      match lx.1 with
      | .done =>
        let tv := ct.2.1.nextElem none
        let sw := sweep false ctx inf tl fuel (n + 1) level v.1 ct.1.toNat (tv.getD 0) tv ct.2.1 0
          (cheapCheck false level lx.2)
        match sw.1 with
        | .done => (.unwind (level - 1) false, afterSweep false level ct.2.2.1 sw.2.1 sw.2.2)
        | _ => (sw.1, sw.2.2)
      | _ => (lx.1, lx.2) := by
  rw [node]
  simp only [Id.run, pure, Bool.false_eq_true, ite_false]
  rcases (leafExit (classify ctx level (visit ctx level nc st).1
      (chooseTarget false ctx tl level (visit ctx level nc st).1
        (compareCodes level (visit ctx level nc st).2.1 (visit ctx level nc st).2.2)).2.2.2).1 level
      (classify ctx level (visit ctx level nc st).1
      (chooseTarget false ctx tl level (visit ctx level nc st).1
        (compareCodes level (visit ctx level nc st).2.1 (visit ctx level nc st).2.2)).2.2.2).2).1 with
    _ | _ | _ <;> rfl

/-! ### For any search policy

The same steps for `Generic.node` and `Generic.sweep` at any policy `P`
(`otherChildG`, `sweep_false_someG`, `node_false_succG`). -/

section Generic

open Generic (Policy)

variable {σ γ : Type} [P : Generic.Policy σ n (γ := γ)]

/-- `otherChild` for the policy `P`. -/
def otherChildG (ctx : γ) (inf tl fuel level nc tc tv1 tv : Nat) (tcell : VSet n) (st : σ) :
    Exit × VSet n × σ :=
  let r := Generic.node false ctx inf tl fuel (level + 1) (nc + 1)
    (Policy.child (n := n) false level tc tv st)
  let st := Policy.leaveChild (n := n) tv r.2
  match r.1 with
  | .fuel => (.fuel, tcell, st)
  | .unwind target short =>
    if target < level then (.unwind target short, tcell, st) else
      let tcell := if short then Policy.shortprune (n := n) tcell st else tcell
      let tcell := if tv == tv1 then Policy.longprune (n := n) tcell st else tcell
      (.done, tcell, Policy.recover (n := n) inf level st)
  | .done =>
    let tcell := if tv == tv1 then Policy.longprune (n := n) tcell st else tcell
    (.done, tcell, Policy.recover (n := n) inf level st)

theorem sweep_false_noneG (ctx : γ) (inf tl fuel cfuel level nc tc tv1 index : Nat)
    (tcell : VSet n) (st : σ) :
    Generic.sweep false ctx inf tl fuel cfuel level nc tc tv1 none tcell index st =
      (.done, index, st) := by
  rw [Generic.sweep]

theorem sweep_false_someG (ctx : γ) (inf tl fuel cfuel level nc tc tv1 tv index : Nat)
    (tcell : VSet n) (st : σ) :
    Generic.sweep false ctx inf tl fuel (cfuel + 1) level nc tc tv1 (some tv) tcell index st =
      match otherChildG ctx inf tl fuel level nc tc tv1 tv tcell st with
      | (.done, tcell', st') =>
        Generic.sweep false ctx inf tl fuel cfuel level nc tc tv1 (tcell'.nextElem (some tv))
          tcell' index st'
      | (e, _, st') => (e, index, st') := by
  rw [Generic.sweep]
  unfold Generic.sweepStep Generic.advance Generic.resume
  simp only [Id.run, pure, otherChildG, Bool.not_false, Bool.true_or, ite_true,
    Bool.false_and, Bool.false_eq_true, ite_false]
  rcases (Generic.node false ctx inf tl fuel (level + 1) (nc + 1)
      (Policy.child (n := n) false level tc tv st)).1 with _ | ⟨target, short⟩ | _
  · cases htv : tv == tv1 <;> simp only [htv, Bool.true_and, ite_true, ite_false,
      Bool.false_eq_true] <;> rfl
  · by_cases ht : target < level
    · simp [ht]
    · cases htv : tv == tv1 <;> cases short <;> simp only [ht, htv, Bool.true_and, ite_true,
        ite_false, Bool.false_eq_true] <;> rfl
  · rfl

/-- `node false` with fuel left, for the policy `P`. -/
theorem node_false_succG (ctx : γ) (inf tl fuel level nc : Nat) (st : σ) :
    Generic.node false ctx inf tl (fuel + 1) level nc st =
      let v := Policy.visit (n := n) ctx level nc st
      let st₁ := Policy.compareCodes (n := n) level v.2.1 v.2.2
      let ct := Policy.chooseTarget (n := n) false ctx tl level v.1 st₁
      let cl := Policy.classify (n := n) ctx level v.1 ct.2.2.2
      let lx := Policy.leafExit (n := n) cl.1 level cl.2
      match lx.1 with
      | .done =>
        let tv := ct.2.1.nextElem none
        let sw := Generic.sweep false ctx inf tl fuel (n + 1) level v.1 ct.1.toNat (tv.getD 0) tv
          ct.2.1 0 (Policy.cheapCheck (n := n) false level lx.2)
        match sw.1 with
        | .done => (.unwind (level - 1) false,
            Policy.afterSweep (n := n) false level ct.2.2.1 sw.2.1 sw.2.2)
        | _ => (sw.1, sw.2.2)
      | _ => (lx.1, lx.2) := by
  rw [Generic.node]
  unfold Generic.nodeStep
  simp only [Id.run, pure, Bool.false_eq_true, ite_false]
  split <;> rename_i h <;> simp only [h] <;> rfl

end Generic

end NautyVerified.Proofs.Search

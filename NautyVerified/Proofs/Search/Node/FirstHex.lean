import NautyVerified.Proofs.Search.Node.Spec

/-!
# HexGraphIso's first-path node, step by step

`node_true_succ` and `sweep_true_some` unfold `node true` and one step of
`sweep true` into the order nauty.c's `firstpathnode0` runs them: refine
(`visit`), record the code (`recordFirst`), choose the target cell
(`chooseTarget true`), install the first leaf (`firstterminal`) or test for a
cheap automorphism (`cheapCheck true`), then sweep the target cell. Each
vertex whose orbit it represents (`firstChild`) is individualized (`child`),
recursed on (the first vertex on the first path, the others off it), recorded
after the first child (`afterChildFirst`), erased from the fixed points, and on
return the cell is pruned (`shortprune` on request) and the partition
recovered (`recover`).
-/

namespace NautyVerified.Proofs.Search

open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {n : Nat}

/-- One vertex of a first-path sweep: the exit, the pruned target cell, the state. -/
def firstChild (ctx : Ctx n) (inf tl fuel level nc tc tv1 tv : Nat) (tcell : VSet n)
    (st : Search n) : Exit × VSet n × Search n :=
  if st.orbits[tv]! == tv then
    let r := node (tv == tv1) ctx inf tl fuel (level + 1) (nc + 1) (child true level tc tv st)
    let s := if tv == tv1 then afterChildFirst level tv1 r.2 else r.2
    let s := { s with fixedpts := s.fixedpts.erase tv }
    match r.1 with
    | .fuel => (.fuel, tcell, s)
    | .unwind target short =>
      if target < level then (.unwind target short, tcell, s) else
        ((.done), (if short then shortprune tcell s else tcell), Hex.GraphIso.Nauty.recover inf level s)
    | .done => (.done, tcell, Hex.GraphIso.Nauty.recover inf level s)
  else (.done, tcell, st)

theorem sweep_true_none (ctx : Ctx n) (inf tl fuel cfuel level nc tc tv1 index : Nat)
    (tcell : VSet n) (st : Search n) :
    sweep true ctx inf tl fuel cfuel level nc tc tv1 none tcell index st = (.done, index, st) := by
  rw [sweep]

theorem sweep_true_some (ctx : Ctx n) (inf tl fuel cfuel level nc tc tv1 tv index : Nat)
    (tcell : VSet n) (st : Search n) :
    sweep true ctx inf tl fuel (cfuel + 1) level nc tc tv1 (some tv) tcell index st =
      match firstChild ctx inf tl fuel level nc tc tv1 tv tcell st with
      | (.done, tcell', st') =>
        sweep true ctx inf tl fuel cfuel level nc tc tv1 (tcell'.nextElem (some tv)) tcell'
          (if st'.orbits[tv]! == tv1 then index + 1 else index) st'
      | (e, _, st') => (e, index, st') := by
  rw [sweep]
  simp only [Id.run, pure, firstChild, Bool.not_true, Bool.false_or, Bool.true_and]
  by_cases ho : (st.orbits[tv]! == tv) = true
  · simp only [ho, ite_true]
    rcases (node (tv == tv1) ctx inf tl fuel (level + 1) (nc + 1) (child true level tc tv st)).1 with
      _ | ⟨target, short⟩ | _
    · cases htv : tv == tv1 <;> simp only [htv, ite_true, ite_false, Bool.false_eq_true] <;> rfl
    · by_cases ht : target < level
      · cases htv : tv == tv1 <;> simp [ht, htv]
      · cases htv : tv == tv1 <;> cases short <;> simp only [ht, htv, ite_true, ite_false,
          Bool.false_eq_true, Bool.not_true, Bool.false_and] <;> rfl
    · cases htv : tv == tv1 <;> simp only [htv, ite_true, ite_false, Bool.false_eq_true,
        Bool.not_true, Bool.false_and] <;> rfl
  · simp only [ho, Bool.false_eq_true, ite_false]

/-- `node true` with fuel left, as `firstpathnode0` runs it. -/
theorem node_true_succ (ctx : Ctx n) (inf tl fuel level nc : Nat) (st : Search n) :
    node true ctx inf tl (fuel + 1) level nc st =
      let v := visit ctx level nc st
      let st₁ := recordFirst level v.2.1 v.2.2
      let ct := chooseTarget true ctx tl level v.1 st₁
      if v.1 = n then (.unwind (level - 1) false, firstterminal level ct.2.2.2) else
        let tv := ct.2.1.nextElem none
        let sw := sweep true ctx inf tl fuel (n + 1) level v.1 ct.1.toNat (tv.getD 0) tv ct.2.1 0
          (cheapCheck true level ct.2.2.2)
        match sw.1 with
        | .done => (.unwind (level - 1) false, afterSweep true level ct.2.2.1 sw.2.1 sw.2.2)
        | _ => (sw.1, sw.2.2) := by
  rw [node]
  simp only [Id.run, pure, ite_true]
  by_cases hv : (visit ctx level nc st).1 = n
  · simp [hv]
  · simp only [hv, ite_false, beq_iff_eq]
    split <;> rename_i h <;> simp only [h]

/-! ### For any search policy

The same steps for `Generic.node` and `Generic.sweep` at any policy `P`
(`firstChildG`, `sweep_true_someG`, `node_true_succG`). -/

section Generic

open Generic (Policy)

variable {σ γ : Type} [P : Generic.Policy σ n (γ := γ)]

/-- `firstChild` for the policy `P`. -/
def firstChildG (ctx : γ) (inf tl fuel level nc tc tv1 tv : Nat) (tcell : VSet n) (st : σ) :
    Exit × VSet n × σ :=
  if Policy.orbit (n := n) st tv == tv then
    let r := Generic.node (tv == tv1) ctx inf tl fuel (level + 1) (nc + 1)
      (Policy.child (n := n) true level tc tv st)
    let s := if tv == tv1 then Policy.afterChildFirst (n := n) level tv1 r.2 else r.2
    let s := Policy.leaveChild (n := n) tv s
    match r.1 with
    | .fuel => (.fuel, tcell, s)
    | .unwind target short =>
      if target < level then (.unwind target short, tcell, s) else
        ((.done), (if short then Policy.shortprune (n := n) tcell s else tcell),
          Policy.recover (n := n) inf level s)
    | .done => (.done, tcell, Policy.recover (n := n) inf level s)
  else (.done, tcell, st)

theorem sweep_true_noneG (ctx : γ) (inf tl fuel cfuel level nc tc tv1 index : Nat)
    (tcell : VSet n) (st : σ) :
    Generic.sweep true ctx inf tl fuel cfuel level nc tc tv1 none tcell index st =
      (.done, index, st) := by
  rw [Generic.sweep]

theorem sweep_true_someG (ctx : γ) (inf tl fuel cfuel level nc tc tv1 tv index : Nat)
    (tcell : VSet n) (st : σ) :
    Generic.sweep true ctx inf tl fuel (cfuel + 1) level nc tc tv1 (some tv) tcell index st =
      match firstChildG ctx inf tl fuel level nc tc tv1 tv tcell st with
      | (.done, tcell', st') =>
        Generic.sweep true ctx inf tl fuel cfuel level nc tc tv1 (tcell'.nextElem (some tv)) tcell'
          (if Policy.orbit (n := n) st' tv == tv1 then index + 1 else index) st'
      | (e, _, st') => (e, index, st') := by
  rw [Generic.sweep]
  unfold Generic.sweepStep Generic.advance Generic.resume
  simp only [Id.run, pure, firstChildG, Bool.not_true, Bool.false_or, Bool.true_and,
    Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases ho : (Policy.orbit (n := n) st tv == tv) = true
  · simp only [ho, ite_true]
    rcases (Generic.node (tv == tv1) ctx inf tl fuel (level + 1) (nc + 1)
        (Policy.child (n := n) true level tc tv st)).1 with _ | ⟨target, short⟩ | _
    · cases htv : tv == tv1 <;> simp only [htv, ite_true, ite_false, Bool.false_eq_true] <;> rfl
    · by_cases ht : target < level
      · cases htv : tv == tv1 <;> simp [ht, htv]
      · cases htv : tv == tv1 <;> cases short <;> simp only [ht, htv, ite_true, ite_false,
          Bool.false_eq_true, Bool.not_true, Bool.false_and] <;> rfl
    · cases htv : tv == tv1 <;> simp only [htv, ite_true, ite_false, Bool.false_eq_true,
        Bool.not_true, Bool.false_and] <;> rfl
  · simp only [ho, Bool.false_eq_true, ite_false]

/-- `node true` with fuel left, for the policy `P`. -/
theorem node_true_succG (ctx : γ) (inf tl fuel level nc : Nat) (st : σ) :
    Generic.node true ctx inf tl (fuel + 1) level nc st =
      let v := Policy.visit (n := n) ctx level nc st
      let st₁ := Policy.recordFirst (n := n) level v.2.1 v.2.2
      let ct := Policy.chooseTarget (n := n) true ctx tl level v.1 st₁
      if v.1 = n then (.unwind (level - 1) false, Policy.firstterminal (n := n) level ct.2.2.2) else
        let tv := ct.2.1.nextElem none
        let sw := Generic.sweep true ctx inf tl fuel (n + 1) level v.1 ct.1.toNat (tv.getD 0) tv
          ct.2.1 0 (Policy.cheapCheck (n := n) true level ct.2.2.2)
        match sw.1 with
        | .done => (.unwind (level - 1) false,
            Policy.afterSweep (n := n) true level ct.2.2.1 sw.2.1 sw.2.2)
        | _ => (sw.1, sw.2.2) := by
  rw [Generic.node]
  unfold Generic.nodeStep
  simp only [Id.run, pure, ite_true]
  by_cases hv : (Policy.visit (n := n) ctx level nc st).1 = n
  · simp [hv]
  · simp only [hv, ite_false, beq_iff_eq]
    split <;> rename_i h <;> simp only [h]

end Generic

end NautyVerified.Proofs.Search

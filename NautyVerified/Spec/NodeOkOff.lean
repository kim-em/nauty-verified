import NautyVerified.Spec.NodeOk

/-!
# `NodeOk` along an off-path node

The off-path node, in the order `othernode0` runs it (`node_false_succ`):
`visit`, `compareCodes`, `chooseTarget false`, `classify`, `leafExit`,
`cheapCheck false`, then the sweep of the target cell, each child being
`child false`, a recursive `node false` at `level + 1`, the erasure of the
fixed point, the prunes and `recover` (`otherChild`).

`SweepOkOff G level numcells tc cell cursor st`: the sweep state is the
renamed image of an `(n + 2)`-run state meeting the inf contract's sweep
precondition, past the first leaf. `nodeOk_sweepOff`: an off-path node that
does not return before its sweep starts it in `SweepOkOff`.
`sweepOkOff_child`: each child call satisfies `NodeOk`. `sweepOkOff_next`: a
child step that does not end the sweep leaves `SweepOkOff` for the rest.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {n k : Nat}

/-- The sweep invariant of an off-path node. -/
def SweepOkOff (G : Colored n k) (level numcells tc : Nat) (cell : VSet n) (cursor : Option Nat)
    (st : Search n) : Prop :=
  ∃ t st₂, st = tw (phi (n + 2) nautyInfinity) t st₂ ∧ 1 ≤ level ∧ SearchOk G level numcells st₂ ∧
    Generic.Target (fun st => st) level tc cell st₂ ∧ (∀ v, cursor = some v → cell.mem v = true) ∧
    Inv st₂ ∧ ∃ last, Depth last st₂ ∧ AgreeTo (last + 1) t st₂.firsttc

/-- An off-path node that reaches its sweep starts it in `SweepOkOff`. -/
theorem nodeOk_sweepOff {G : Colored n k} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : NodeOk G false level numcells st)
    (ctx : Ctx n) (tcLevel : Nat) :
    let v := visit ctx level numcells st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := chooseTarget false ctx tcLevel level v.1 st₁
    let cl := classify ctx level v.1 ct.2.2.2
    let lx := leafExit cl.1 level cl.2
    lx.1 = .done →
      SweepOkOff G level v.1 ct.1.toNat ct.2.1 (ct.2.1.nextElem none) (cheapCheck false level lx.2) := by
  obtain ⟨t, st₀, rfl, hlevel, hok, hinv, -, hoff⟩ := h
  obtain ⟨last, hd, ha⟩ := hoff rfl
  have hln := level_le_of_ok hok
  have hL1 : level < n + 2 := by omega
  have hL2 : level < nautyInfinity := by omega
  have R := reachPolicy G ctx tcLevel hn0
  have D := depthPolicy ctx (n + 2) tcLevel last
  have F := referencePolicy ctx (n + 2) tcLevel
  have hrf : ∀ {x y : Search n}, x.reference = y.reference → x.firsttc = y.firsttc ∧
      x.firstcode = y.firstcode := fun h =>
    ⟨congrArg (fun r => r.2.1) h, congrArg (fun r => r.1) h⟩
  have hv := R.visit level numcells st₀ hlevel hok
  have hvd := D.visit level numcells st₀ hd
  have hvf := F.visit level numcells st₀
  have hcode := D.code level numcells st₀
  have hvi : Inv (visit ctx level numcells st₀).2.2 := hinv
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.compareCodes,
    Generic.Policy.chooseTarget, Generic.Policy.classify, Generic.Policy.leafExit,
    Generic.Policy.cheapCheck] at hv hvd hvf hcode ⊢
  rw [visit_tw t ctx level numcells st₀ hL1 hL2]
  generalize visit ctx level numcells st₀ = r at hv hvd hvf hcode hvi ⊢
  obtain ⟨nc, code, s1⟩ := r
  obtain ⟨hok1, -⟩ := hv
  dsimp only at hok1 hvd hvf hcode hvi ⊢
  have hcd := compareCodes_depth (level := level) hvd hcode
  have hcf := F.compare level code s1
  have hcl := R.compare level code nc s1 hok1
  dsimp only [policy, Generic.Policy.compareCodes] at hcf hcl
  have hci : Inv (compareCodes level code s1) :=
    ⟨by rw [compare_noncheap]; exact hvi.1, by rw [(hrf hcf).2]; exact hvi.2⟩
  rw [compareCodes_tw]
  generalize compareCodes level code s1 = s2 at hcd hcf hcl hci ⊢
  have ht : false = false → s2.eqlevFirst = level → t[level]! = s2.firsttc[level]! := by
    intro _ he
    rw [(hrf hcf).1, (hrf hvf).1]
    exact ha.2 level hlevel (by have := hcd.1; omega)
  rw [chooseTarget_tw t false ctx tcLevel level nc s2 hL1 hL2 ht]
  have htd := D.target level nc s2 hcd
  have htf := F.target level nc s2
  have htr := R.target false level nc s2 hlevel hcl.ok
  dsimp only [policy, Generic.Policy.chooseTarget] at htd htf htr
  have hti : Inv (chooseTarget false ctx tcLevel level nc s2).2.2.2 :=
    ⟨by rw [target_noncheap]; exact hci.1, by rw [(hrf htf).2]; exact hci.2⟩
  generalize chooseTarget false ctx tcLevel level nc s2 = c at htd htf htr hti ⊢
  obtain ⟨tc, cell, size, s3⟩ := c
  obtain ⟨htl, htarget⟩ := htr
  dsimp only at htd htf htl htarget hti ⊢
  simp only [Bool.false_eq_true, ite_false]
  rw [classify_tw]
  have hcld := (D.classify level nc s3 htd).1
  have hclf := F.classify level nc s3
  have hclr := R.classify level nc s3 htl.ok
  dsimp only [policy, Generic.Policy.classify] at hcld hclf hclr
  have hcli : Inv (classify ctx level nc s3).2 :=
    ⟨by rw [classify_noncheap]; exact hti.1, by rw [(hrf hclf).2]; exact hti.2⟩
  generalize classify ctx level nc s3 = cl at hcld hclf hclr hcli ⊢
  obtain ⟨leaf, s4⟩ := cl
  dsimp only at hcld hclf hclr hcli ⊢
  rw [leafExit_tw t leaf level s4 (by have := hcli.1; omega) (by have := hcli.1; omega)]
  have hled := D.leaf leaf level s4 trivial hcld
  have hlef := F.leaf leaf level s4
  have hler := R.leaf leaf level nc s4 hclr.ok
  dsimp only [policy, Generic.Policy.leafExit] at hled hlef hler
  have hlei : Inv (leafExit leaf level s4).2 :=
    ⟨by rw [leafExit_noncheap]; exact hcli.1, by rw [(hrf hlef).2]; exact hcli.2⟩
  generalize leafExit leaf level s4 = le at hled hlef hler hlei ⊢
  obtain ⟨exit, s5⟩ := le
  dsimp only at hled hlef hler hlei ⊢
  intro _
  have hf5 : s5.firsttc = s1.firsttc := by
    rw [(hrf hlef).1, (hrf hclf).1, (hrf htf).1, (hrf hcf).1]
  rw [cheapCheck_tw t false level s5 hL1 hL2]
  have hchd := D.cheap false level s5 hled
  have hchf := F.cheap false level s5
  have hchr := R.cheap false level nc s5 hler.ok
  dsimp only [policy, Generic.Policy.cheapCheck] at hchd hchf hchr
  have hchi : Inv (cheapCheck false level s5) := by
    refine ⟨?_, by rw [(hrf hchf).2]; exact hlei.2⟩
    unfold cheapCheck; split
    · show level + 1 ≤ n + 1; omega
    · exact hlei.1
  have htarget6 : Generic.Target (fun st => st) level tc.toNat cell (cheapCheck false level s5) :=
    ((htarget.of_out hclr.effect).of_out hler.effect).of_out hchr.effect
  refine ⟨t, cheapCheck false level s5, rfl, hlevel, hchr.ok, htarget6,
    fun v hv => VSet.nextElem_mem hv, hchi, last, hchd, ?_⟩
  rw [(hrf hchf).1, hf5, (hrf hvf).1]; exact ha

/-- Each child of an off-path sweep is called in `NodeOk`. -/
theorem sweepOkOff_child {G : Colored n k} {level numcells tc tv : Nat} {cell : VSet n}
    {st : Search n} (hn0 : 0 < n) (h : SweepOkOff G level numcells tc cell (some tv) st)
    (ctx : Ctx n) (tcLevel : Nat) :
    NodeOk G false (level + 1) (numcells + 1) (child false level tc tv st) := by
  obtain ⟨t, st₀, rfl, hlevel, hok, htarget, hcur, hinv, last, hd, ha⟩ := h
  have hln := level_le_of_ok hok
  have R := reachPolicy G ctx tcLevel hn0
  have D := depthPolicy ctx (n + 2) tcLevel last
  have F := referencePolicy ctx (n + 2) tcLevel
  have hch := R.child false level numcells tc tv cell st₀ hlevel hok htarget (hcur tv rfl)
  have hcd := D.child false level tc tv st₀ hd
  have hcf := F.child false level tc tv st₀
  dsimp only [policy, Generic.Policy.child] at hch hcd hcf
  rw [child_tw t false level tc tv st₀ (by omega)]
  refine ⟨t, child false level tc tv st₀, rfl, by omega, hch.1, child_inv hinv,
    fun h => absurd h (by decide), fun _ => ⟨last, hcd, ?_⟩⟩
  rw [(ref_fields hcf).1]; exact ha

end NautyVerified.Spec.SearchInf

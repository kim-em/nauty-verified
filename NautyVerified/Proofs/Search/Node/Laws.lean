import NautyVerified.Proofs.Search.Node.Policy
import NautyVerified.Proofs.Search.Node.ProcFacts
import NautyVerified.Proofs.Search.Node.OtherFrame
import NautyVerified.Proofs.Search.Node.Em
import NautyVerified.Spec.NodeBound

/-!
# The HexGraphIso facts nauty.c's nodes need, for any search policy

The node proofs read HexGraphIso's search through a few facts about the states
it reaches: the node precondition `NodeOk` and the sweep invariants, how each
step keeps them, the partition facts the C needs of a refined node, the bounds
on exits, and the emitted words. For the dense policy these are
`Spec/NodeOk.lean`, `Spec/NodeOkOff.lean`, `Node/OkOff.lean`,
`Node/OkFirst.lean`, `Node/ProcFacts.lean`, `Spec/NodeExit.lean`,
`Spec/NodeBound.lean` and `Spec/PartOk.lean`. They rest on HexGraphIso's
soundness of that policy (`SearchInf`: the renamed `n + 2` run, `SearchOk` for
coloured graphs), not on the operations alone, so for a general policy they are
a structure `NodeLaws L G` over the policy link `L`, stated against
`Generic.node`, `firstChildG` and `otherChildG`, with `SInvG`; `denseLaws` is
the dense instance from the dense lemmas. A sparse instance comes from
HexGraphIso's soundness of the sparse policy.

The emitted words have the generic laws `EmLawOffG`/`EmLawFirstG` (with
`sweepEmG`, `sweepEmFirstG`, `procExitG`, `procWordsG`), which are
definitions; `EmLawOff.toG` and `EmLawFirst.toG` give them from the dense laws.

`PartFactsG` and `SRestG` are `PartFacts` and `SRest` for any carried store;
`SInvG.of` builds `SInvG` from them, as `SInv.of` does. The dense `SRest` step
lemmas of `Node/InvSteps.lean` are only used there (the C step lemmas
re-establish `SInv` themselves), so they have no generic counterparts; the steps
that need HexGraphIso's partition facts are the laws `visit_inv`,
`first_broken` and `off_broken`.
-/

namespace NautyVerified.Proofs.Search

open NautyVerified.Proofs.Dispatch (Ops denseOps)
open NautyVerified.Spec NautyVerified.Spec.SearchInf
open Hex.GraphIso Hex.GraphIso.Nauty
open Generic (Policy)

variable {n : Nat}

/-- `PartFacts` for any carried store. -/
structure PartFactsG {κ : Type} (n level numcells : Nat) (st : SearchState n κ) : Prop where
  labSize : st.lab.size = n
  labSmall : ∀ i < n, st.lab[i]! < n
  labSurj : ∀ v < n, ∃ i < n, st.lab[i]! = v
  ptnSize : st.ptn.size = n
  ptnVals : ∀ i < n, st.ptn[i]! ≤ level ∨ st.ptn[i]! = nautyInfinity
  ptnLast : st.ptn[n - 1]! ≤ 1
  count : numcells = bcount st.ptn level n
  levelLe : level ≤ numcells
  numcellsLe : numcells ≤ n

theorem _root_.NautyVerified.Spec.SearchInf.PartFacts.toG {level numcells : Nat} {st : Search n} (h : PartFacts n level numcells st) :
    PartFactsG n level numcells st := { h with }

/-- `SRest` for `O`: the part of `SInvG` that is not about the partition. -/
structure SRestG (O : Ops) (G : O.Gr n) (st : SearchState n (O.Canon n)) : Prop where
  codesSmall : ∀ i < n + 2, st.firstcode[i]! < 32768 ∧ st.canoncode[i]! < 32768
  firsttcRange : ∀ i < n + 2, -1 ≤ st.firsttc[i]! ∧ st.firsttc[i]! < n
  workpermSmall : ∀ i < n, st.workperm[i]! < n
  samerows : st.samerows ≤ n
  workpermSize : st.workperm.size = n
  firstlabSize : st.firstlab.size = n
  canonlabSize : st.canonlab.size = n
  firstcodeSize : st.firstcode.size = n + 2
  canoncodeSize : st.canoncode.size = n + 2
  firsttcSize : st.firsttc.size = n + 2
  canong : O.StoreOk G (O.rows st.canong)
  scalars : st.gcaFirst < 2147483648 ∧ st.gcaCanon < 2147483648 ∧
    st.noncheaplevel < 2147483648 ∧ st.allsamelevel < 2147483648 ∧
    st.eqlevFirst < 2147483648 ∧ -1 ≤ st.eqlevCanon ∧ st.eqlevCanon < 2147483648 ∧
    -1 ≤ st.compCanon ∧ st.compCanon ≤ 1 ∧ st.canonlevel < 2147483648 ∧
    st.stabvertex < 2147483648 ∧ st.cosetindex < 2147483648
  wsCap : st.wsCap = wsPairs
  maxlevelLe : st.maxlevel ≤ n
  numorbitsLe : st.numorbits ≤ n
  orbitsDesc : Hex.GraphIso.Nauty.Orbit.Descending st.orbits n

theorem SInvG.rest {O : Ops} {G : O.Gr n} {st : SearchState n (O.Canon n)} (h : SInvG O G st) :
    SRestG O G st := { h with }

/-- `SInv.of` for `O`. -/
theorem SInvG.of {O : Ops} {G : O.Gr n} {level numcells : Nat} {st : SearchState n (O.Canon n)}
    (hp : PartFactsG n level numcells st) (hr : SRestG O G st) : SInvG O G st :=
  { hr with
    labSize := hp.labSize, labSmall := hp.labSmall, labSurj := hp.labSurj, ptnSize := hp.ptnSize
    ptnVals := fun i hi => by
      rcases hp.ptnVals i hi with h | h
      · have := hp.levelLe; have := hp.numcellsLe; exact .inl (by omega)
      · exact .inr h
    ptnLast := hp.ptnLast
    orbitsSmall := fun i hi => Nat.lt_of_le_of_lt (hr.orbitsDesc.2 i hi) hi
    orbitsSize := hr.orbitsDesc.1 }

/-- `SRestG` reads no field `Same` may change but the store's rows. -/
theorem SRestG.same {O : Ops} {G : O.Gr n} {s t : SearchState n (O.Canon n)} (h : SRestG O G s)
    (hs : Same O s t) : SRestG O G t := by
  obtain ⟨⟨c, o, rfl⟩, r⟩ := hs
  exact { h with canong := r ▸ h.canong }

/-! ### The emitted words -/

section Em

variable {κ γ : Type} [P : Generic.Policy (SearchState n κ) n (γ := γ)]

/-- `procExit` for the policy `P`. -/
abbrev procExitG (G : γ) (level numcells : Nat) (st : SearchState n κ) :
    Exit × SearchState n κ :=
  P.leafExit (P.classify G level numcells st).1 level (P.classify G level numcells st).2

/-- `procWords` for the policy `P`. -/
abbrev procWordsG (G : γ) (level numcells : Nat) (st : SearchState n κ) : List Int :=
  if (procExitG G level numcells st).2.numgenerators = st.numgenerators + 1 then
    genWords (procExitG G level numcells st).2.workperm n else []

/-- `sweepEm` for the policy `P`. -/
def sweepEmG (Em : Bool → Nat → Nat → SearchState n κ → List Int) (G : γ)
    (level nc tc tv1 : Nat) : Nat → Option Nat → VSet n → SearchState n κ → List Int
  | _, none, _, _ => []
  | 0, some _, _, _ => []
  | cfuel + 1, some tv, tcell, st =>
    Em false (level + 1) (nc + 1) (P.child false level tc tv st) ++
      match otherChildG G nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv tcell st with
      | (.done, tcell', st') =>
        sweepEmG Em G level nc tc tv1 cfuel (tcell'.nextElem (some tv)) tcell' st'
      | _ => []

/-- `sweepEmFirst` for the policy `P`. -/
def sweepEmFirstG (Em : Bool → Nat → Nat → SearchState n κ → List Int) (G : γ)
    (level nc tc tv1 : Nat) : Nat → Option Nat → VSet n → SearchState n κ → List Int
  | _, none, _, _ => []
  | 0, some _, _, _ => []
  | cfuel + 1, some tv, tcell, st =>
    (if P.orbit st tv == tv then Em (tv == tv1) (level + 1) (nc + 1) (P.child true level tc tv st)
      else []) ++
      match firstChildG G nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv tcell st with
      | (.done, tcell', st') =>
        sweepEmFirstG Em G level nc tc tv1 cfuel (tcell'.nextElem (some tv)) tcell' st'
      | _ => []

/-- `EmLawOff` for the policy `P`. -/
def EmLawOffG (Em : Bool → Nat → Nat → SearchState n κ → List Int) (G : γ) : Prop :=
  ∀ level nc st, 1 ≤ level → level ≤ n →
    Em false level nc st =
      let v := P.visit G level nc st
      let st₁ := P.compareCodes level v.2.1 v.2.2
      let ct := P.chooseTarget false G 100 level v.1 st₁
      let lx := procExitG G level v.1 ct.2.2.2
      procWordsG G level v.1 ct.2.2.2 ++
        if lx.1 matches .done then
          sweepEmG Em G level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1)
            (ct.2.1.nextElem none) ct.2.1 (P.cheapCheck false level lx.2)
        else []

/-- `EmLawFirst` for the policy `P`. -/
def EmLawFirstG (Em : Bool → Nat → Nat → SearchState n κ → List Int) (G : γ) : Prop :=
  ∀ level nc st, 1 ≤ level → level ≤ n →
    Em true level nc st =
      let v := P.visit G level nc st
      let st₁ := P.recordFirst level v.2.1 v.2.2
      let ct := P.chooseTarget true G 100 level v.1 st₁
      if v.1 = n then [] else
        sweepEmFirstG Em G level v.1 ct.1.toNat ((ct.2.1.nextElem none).getD 0) (n + 1)
          (ct.2.1.nextElem none) ct.2.1 (P.cheapCheck true level ct.2.2.2)

end Em

section Dense

theorem otherChildG_dense (ctx : Ctx n) (inf tl fuel level nc tc tv1 tv : Nat) (tcell : VSet n)
    (st : Search n) :
    otherChildG ctx inf tl fuel level nc tc tv1 tv tcell st =
      otherChild ctx inf tl fuel level nc tc tv1 tv tcell st := by
  unfold otherChildG otherChild
  rw [← node_eq_generic]
  rfl

theorem firstChildG_dense (ctx : Ctx n) (inf tl fuel level nc tc tv1 tv : Nat) (tcell : VSet n)
    (st : Search n) :
    firstChildG ctx inf tl fuel level nc tc tv1 tv tcell st =
      firstChild ctx inf tl fuel level nc tc tv1 tv tcell st := by
  unfold firstChildG firstChild
  rw [← node_eq_generic]
  rfl

theorem sweepEmG_dense (Em : Bool → Nat → Nat → Search n → List Int) (ctx : Ctx n)
    (level nc tc tv1 : Nat) :
    ∀ cfuel tv tcell st, sweepEmG Em ctx level nc tc tv1 cfuel tv tcell st =
      sweepEm Em ctx level nc tc tv1 cfuel tv tcell st
  | _, none, _, _ => by rw [sweepEmG, sweepEm]
  | 0, some _, _, _ => by rw [sweepEmG, sweepEm]
  | cfuel + 1, some tv, tcell, st => by
    rw [sweepEmG, sweepEm, otherChildG_dense]
    generalize otherChild ctx nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv tcell st = r
    rcases r with ⟨_ | _ | _, tcell', st'⟩
    · dsimp only; rw [sweepEmG_dense]; rfl
    all_goals rfl

theorem sweepEmFirstG_dense (Em : Bool → Nat → Nat → Search n → List Int) (ctx : Ctx n)
    (level nc tc tv1 : Nat) :
    ∀ cfuel tv tcell st, sweepEmFirstG Em ctx level nc tc tv1 cfuel tv tcell st =
      sweepEmFirst Em ctx level nc tc tv1 cfuel tv tcell st
  | _, none, _, _ => by rw [sweepEmFirstG, sweepEmFirst]
  | 0, some _, _, _ => by rw [sweepEmFirstG, sweepEmFirst]
  | cfuel + 1, some tv, tcell, st => by
    rw [sweepEmFirstG, sweepEmFirst, firstChildG_dense]
    generalize firstChild ctx nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv tcell st = r
    rcases r with ⟨_ | _ | _, tcell', st'⟩
    · dsimp only; rw [sweepEmFirstG_dense]; rfl
    all_goals rfl

theorem EmLawOff.toG {Em : Bool → Nat → Nat → Search n → List Int} {ctx : Ctx n}
    (h : EmLawOff Em ctx) : EmLawOffG Em ctx := by
  intro level nc st h1 h2
  rw [h level nc st h1 h2]
  dsimp only
  rw [sweepEmG_dense]
  rfl

theorem EmLawFirst.toG {Em : Bool → Nat → Nat → Search n → List Int} {ctx : Ctx n}
    (h : EmLawFirst Em ctx) : EmLawFirstG Em ctx := by
  intro level nc st h1 h2
  rw [h level nc st h1 h2]
  dsimp only
  rw [sweepEmFirstG_dense]
  rfl

end Dense

/-! ### The laws -/

section Laws

variable {O : Ops} [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]

/-- The HexGraphIso facts nauty.c's node proofs need of the policy `P` on the
graph `G`: the node precondition `NodeOk`, the sweep invariants `SweepFirst`
(`SweepOkFirst`) and `SweepOff` (`SweepOkOff`), and how the node's steps keep
them. Every node runs with `inf = nautyInf` and `tcLevel = 100`. -/
structure NodeLaws (L : PolicyLink O n) (G : O.Gr n) where
  NodeOk : Bool → Nat → Nat → SearchState n (O.Canon n) → Prop
  /-- `level numcells tc tv1 cell cursor st`. -/
  SweepFirst : Nat → Nat → Nat → Nat → VSet n → Option Nat → SearchState n (O.Canon n) → Prop
  /-- `level numcells tc cell cursor st`. -/
  SweepOff : Nat → Nat → Nat → VSet n → Option Nat → SearchState n (O.Canon n) → Prop
  level_pos : ∀ {first level nc st}, NodeOk first level nc st → 1 ≤ level
  /-- `level_le_of_ok`: a node's level is at most `n`. -/
  level_le : ∀ {first level nc st}, NodeOk first level nc st → level ≤ n
  /-- The policy's invariant holds at a node and along its sweeps. -/
  inv : ∀ {first level nc st}, NodeOk first level nc st → L.Inv G st.canong
  inv_first : ∀ {level nc tc tv1 cell cursor st}, SweepFirst level nc tc tv1 cell cursor st →
    L.Inv G st.canong
  inv_off : ∀ {level nc tc cell cursor st}, SweepOff level nc tc cell cursor st →
    L.Inv G st.canong
  /-- What the policy's `visit` needs (`L.VisitOk`). -/
  visitOk : ∀ {first level nc st}, NodeOk first level nc st → L.VisitOk G level nc st
  /-- What the policy's `chooseTarget` needs (`L.TargetOk`), after the code step. -/
  targetOk : ∀ {first level nc st}, NodeOk first level nc st →
    L.TargetOk G level (P.visit G level nc st).1
      (if first then P.recordFirst level (P.visit G level nc st).2.1 (P.visit G level nc st).2.2
       else P.compareCodes level (P.visit G level nc st).2.1 (P.visit G level nc st).2.2)
  /-- `visit_code_lt`: the refinement's code fits nauty.c's `short code`. -/
  code_lt : ∀ {first level nc st}, NodeOk first level nc st → (P.visit G level nc st).2.1 < 32768
  /-- `SInv.visitSt`. -/
  visit_inv : ∀ {first level nc st}, NodeOk first level nc st → SInvG O G st →
    SInvG O G (visitStG O G level nc st)
  /-- `PartOk.visit`'s partition facts. -/
  visit_part : ∀ {first level nc st}, NodeOk first level nc st →
    PartFactsG n level (P.visit G level nc st).1 (P.visit G level nc st).2.2
  /-- `Bestcell.targetcell_mem`: the target cell of a refined node with fewer than `n`
  cells is a vertex starting a nontrivial cell (what nautil.c's cell scan in
  `maketargetcell` needs). -/
  target_lt : ∀ {first level nc st}, NodeOk first level nc st → (P.visit G level nc st).1 < n →
    ∀ hint : Int, hint < n →
      O.targetcell G (P.visit G level nc st).2.2.lab (P.visit G level nc st).2.2.ptn level 100 hint < n ∧
        level < (P.visit G level nc st).2.2.ptn[O.targetcell G (P.visit G level nc st).2.2.lab
          (P.visit G level nc st).2.2.ptn level 100 hint]!
  /-- `nodeOk_sweepFirst`. -/
  first_start : ∀ {level nc st}, NodeOk true level nc st →
    let v := P.visit G level nc st
    let st₁ := P.recordFirst level v.2.1 v.2.2
    let ct := P.chooseTarget true G 100 level v.1 st₁
    v.1 ≠ n → ∃ tv1, ct.2.1.nextElem none = some tv1 ∧
      SweepFirst level v.1 ct.1.toNat tv1 ct.2.1 (some tv1) (P.cheapCheck true level ct.2.2.2)
  /-- `sweepOkFirst_child`. -/
  first_child : ∀ {level nc tc tv1 tv cell st}, SweepFirst level nc tc tv1 cell (some tv) st →
    NodeOk (tv == tv1) (level + 1) (nc + 1) (P.child true level tc tv st)
  /-- `sweepOkFirst_next`. -/
  first_next : ∀ {level nc tc tv1 tv cell st} fuel, SweepFirst level nc tc tv1 cell (some tv) st →
    (firstChildG G nautyInf 100 fuel level nc tc tv1 tv cell st).1 = .done →
    SweepFirst level nc tc tv1 (firstChildG G nautyInf 100 fuel level nc tc tv1 tv cell st).2.1
      ((firstChildG G nautyInf 100 fuel level nc tc tv1 tv cell st).2.1.nextElem (some tv))
      (firstChildG G nautyInf 100 fuel level nc tc tv1 tv cell st).2.2
  /-- `SInv.brokenStFirst`. -/
  first_broken : ∀ {level nc tc tv1 tv cell st}, SInvG O G st →
    SweepFirst level nc tc tv1 cell (some tv) st → SInvG O G (brokenSt level tc tv st)
  /-- `breakout`'s arguments in a first-path sweep. -/
  first_args : ∀ {level nc tc tv1 tv cell st}, SweepFirst level nc tc tv1 cell (some tv) st →
    tv < n ∧ tc < n ∧ ∃ j, tc ≤ j ∧ j < n ∧ st.lab[j]! = tv
  /-- `nodeOk_sweepOff`. -/
  off_start : ∀ {level nc st}, NodeOk false level nc st →
    let v := P.visit G level nc st
    let st₁ := P.compareCodes level v.2.1 v.2.2
    let ct := P.chooseTarget false G 100 level v.1 st₁
    let lx := procExitG G level v.1 ct.2.2.2
    lx.1 = .done →
      SweepOff level v.1 ct.1.toNat ct.2.1 (ct.2.1.nextElem none) (P.cheapCheck false level lx.2)
  /-- `sweepOkOff_child`. -/
  off_child : ∀ {level nc tc tv cell st}, SweepOff level nc tc cell (some tv) st →
    NodeOk false (level + 1) (nc + 1) (P.child false level tc tv st)
  /-- `sweepOkOff_next`. -/
  off_next : ∀ {level nc tc tv1 tv cell st} fuel, SweepOff level nc tc cell (some tv) st →
    (otherChildG G nautyInf 100 fuel level nc tc tv1 tv cell st).1 = .done →
    SweepOff level nc tc (otherChildG G nautyInf 100 fuel level nc tc tv1 tv cell st).2.1
      ((otherChildG G nautyInf 100 fuel level nc tc tv1 tv cell st).2.1.nextElem (some tv))
      (otherChildG G nautyInf 100 fuel level nc tc tv1 tv cell st).2.2
  /-- `SInv.brokenSt`. -/
  off_broken : ∀ {level nc tc tv cell st}, SInvG O G st →
    SweepOff level nc tc cell (some tv) st → SInvG O G (brokenSt level tc tv st)
  /-- `sweepOkOff_breakArgs`. -/
  off_args : ∀ {level nc tc tv cell st}, SweepOff level nc tc cell (some tv) st →
    tv < n ∧ tc < n ∧ ∃ j, tc ≤ j ∧ j < n ∧ st.lab[j]! = tv
  /-- `nodeOk_noFuel`. -/
  noFuel : ∀ {first level nc st}, NodeOk first level nc st → level ≤ n →
    (hexNodeG first G level nc st).1 ≠ .fuel
  /-- `nodeOk_unwind_lt`. -/
  unwind_lt : ∀ {level nc st}, NodeOk false level nc st → ∀ fuel tg s,
    (Generic.node false G nautyInf 100 fuel level nc st).1 = .unwind tg s → tg < level
  /-- `node_hlt`. -/
  leaf_lt : ∀ {level nc st}, NodeOk false level nc st →
    let v := P.visit G level nc st
    let st₁ := P.compareCodes level v.2.1 v.2.2
    let ct := P.chooseTarget false G 100 level v.1 st₁
    ∀ tg s, (procExitG G level v.1 ct.2.2.2).1 = .unwind tg s → tg < level
  /-- `node_hDone`. -/
  leaf_done : ∀ {level nc st}, NodeOk false level nc st →
    let v := P.visit G level nc st
    let st₁ := P.compareCodes level v.2.1 v.2.2
    let ct := P.chooseTarget false G 100 level v.1 st₁
    (procExitG G level v.1 ct.2.2.2).1 = .done →
      v.1 < n ∧ (st₁.eqlevFirst = level ∨ 0 ≤ st₁.compCanon)
  /-- `proc_leafOk`. -/
  leafOk : ∀ {level nc st}, NodeOk false level nc st →
    let v := P.visit G level nc st
    let st₁ := P.compareCodes level v.2.1 v.2.2
    let ct := P.chooseTarget false G 100 level v.1 st₁
    LeafOkG ct.2.2.2
  /-- At a leaf with `compCanon = 0` the canonical rows below `samerows` are `G`
  relabelled by `canonlab`, so `updatecan` fits the store (`processnodeSpecG`). -/
  leafFits : ∀ {level nc st}, NodeOk false level nc st →
    let v := P.visit G level nc st
    let st₁ := P.compareCodes level v.2.1 v.2.2
    let ct := P.chooseTarget false G 100 level v.1 st₁
    ct.2.2.2.compCanon = 0 → O.Fits G (O.rows ct.2.2.2.canong) ct.2.2.2.canonlab ct.2.2.2.samerows
  /-- `node_short_autos`. -/
  short_autos : ∀ first fuel level nc (st : SearchState n (O.Canon n)) {tg},
    0 < (Generic.node first G nautyInf 100 fuel level nc st).2.wsCap →
    (Generic.node first G nautyInf 100 fuel level nc st).1 = .unwind tg true →
    0 < (Generic.node first G nautyInf 100 fuel level nc st).2.autos.size

end Laws

/-! ### The dense instance -/

section DenseLaws

variable {k : Nat}

/-- The dense laws, on the coloured graph `G` with its rows `ctx`. -/
def denseLaws (G : Colored n k) (ctx : Ctx n) (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) :
    NodeLaws (denseLink (n := n)) ctx where
  NodeOk := NodeOk G
  SweepFirst := SweepOkFirst G
  SweepOff := SweepOkOff G
  level_pos h := by obtain ⟨⟨_, _, _, h1, _⟩, _⟩ := h; exact h1
  level_le h := by obtain ⟨⟨_, _, _, _, hso, _⟩, _⟩ := h; exact SearchInf.level_le_of_ok hso
  inv _ := trivial
  inv_first _ := trivial
  inv_off _ := trivial
  visitOk _ := trivial
  targetOk _ := trivial
  code_lt {_ level nc st} _ := Nat.lt_trans (visit_code_lt ctx level nc st) (by decide)
  visit_inv h hs := (SInv.visitSt hn0 hn hs.dense h ctx).toG
  visit_part h := ((PartOk.visit hn0 hn
    (by obtain ⟨⟨_, _, _, h1, _⟩, _⟩ := h; exact h1) (PartOk.of_nodeOk hn h) ctx).facts hn0 hn).toG
  target_lt {_ level _ _} h hlt hint hh := by
    have h1 : 1 ≤ level := by obtain ⟨⟨_, _, _, h1, _⟩, _⟩ := h; exact h1
    have hp := (PartOk.visit hn0 hn h1 (PartOk.of_nodeOk hn h) ctx).facts hn0 hn
    obtain ⟨x, hx, hgt⟩ := exists_gt_of_bcount (hp.count ▸ hlt)
    exact Bestcell.targetcell_mem ctx _ _ _ 100 hint hp.ptnSize (Nat.le_trans hp.ptnLast h1) hh hx hgt
  first_start h := nodeOk_sweepFirst hn0 hn h ctx 100
  first_child h := sweepOkFirst_child hn0 h ctx 100
  first_next fuel h hd := by
    rw [firstChildG_dense] at hd ⊢
    exact sweepOkFirst_next hn0 hn h ctx 100 fuel hd
  first_broken hs h := (SInv.brokenStFirst hn0 hn ctx 100 hs.dense h.1).toG
  first_args {level nc tc tv1 tv cell st} h := by
    have hm : cell.mem tv = true := h.1.choose_spec.choose_spec.2.2.2.2.1 tv rfl
    obtain ⟨st₂, ⟨len, hc, hseg⟩, hlab⟩ := SweepOkFirst.target h
    have hne : cell ≠ VSet.empty := fun he => by
      rw [he, VSet.mem_empty] at hm; cases hm
    obtain ⟨-, h2, h3⟩ := hc hne
    have hs := hseg _ hm
    rw [segN, List.mem_map] at hs
    obtain ⟨o, ho, e⟩ := hs
    rw [List.mem_range] at ho
    exact ⟨VSet.mem_lt hm, by omega, tc + o, by omega, by omega, by rw [← hlab]; exact e⟩
  off_start h := nodeOk_sweepOff hn0 hn h ctx 100
  off_child h := sweepOkOff_child hn0 h ctx 100
  off_next fuel h hd := by
    rw [otherChildG_dense] at hd ⊢
    exact sweepOkOff_next hn0 hn h ctx 100 fuel hd
  off_broken hs h := (SInv.brokenSt hn0 hn ctx 100 hs.dense h.1).toG
  off_args h := sweepOkOff_breakArgs h
  noFuel h hl := by
    rw [hexNodeG_dense]
    exact nodeOk_noFuel hn0 hn h ctx 100 hl
  unwind_lt h fuel tg s he := by
    rw [← node_eq_generic] at he
    exact nodeOk_unwind_lt h ctx nautyInf 100 fuel tg s he
  leaf_lt h := node_hlt h ctx 100
  leaf_done h := node_hDone hn0 hn h ctx 100
  leafOk h := (proc_leafOk h ctx 100).toG
  leafFits _ _ := trivial
  short_autos first fuel level nc st _ hcap he := by
    rw [← node_eq_generic] at hcap he ⊢
    exact node_short_autos first ctx nautyInf 100 fuel level nc st hcap he

end DenseLaws

end NautyVerified.Proofs.Search

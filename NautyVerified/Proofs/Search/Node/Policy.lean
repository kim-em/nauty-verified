import NautyVerified.Proofs.Search.Node.Visit
import NautyVerified.Proofs.Search.Node.Spec
import NautyVerified.Proofs.Search.Processnode.Classifier
import NautyVerified.Proofs.Maketargetcell.Satisfies

/-!
# How a search policy runs nauty.c's node operations

nauty.c's search nodes are HexGraphIso's `Generic.node` for a policy `P` on the
search state `SearchState n (O.Canon n)` of the dispatch operations `O`
(`nodeSpecG`). `PolicyLink O n` says what the node proofs need of `P`:

- `visit` is `O.refine` (`visitStG`, after counting the node), `chooseTarget`
  is `chooseTargetG`, HexGraphIso's `chooseTarget` with `maketargetcell` given
  by `O.targetcell` and nautil.c's cell scan `mtcOf`, and `classify` is
  `O.classify` (which `Classifier O` relates to `O`'s procedures);
- the transitions nauty.c shares between dense and sparse graphs
  (`recordFirst`, `compareCodes`, `firstterminal`, `leafExit`, `cheapCheck`,
  `afterChildFirst`, `leaveChild`, `orbit`, `shortprune`, `longprune`) are
  HexGraphIso's;
- `child`, `recover` and `afterSweep` are HexGraphIso's up to `Same`: equal
  except in the carried store (whose rows agree) and the exact group order,
  neither of which nauty.c's search stores beyond `O.rows`;
- `O.cheapautom` is HexGraphIso's `cheapautom` (for `wp_cheapG`).

`visit` and `chooseTarget` may need more than the state's fields: a
policy-specific invariant `Inv` of the carried store (sparse: bounded
refinement scratch), kept by every transition that changes the store, and the
conditions `VisitOk` and `TargetOk` on the node (sparse: the partition shape
`refineWith_refine` and `maketargetCached_eq` need). For the dense policy all
three are `True` (`denseLink`).

`SearchAtG.same`/`SInvG.same`: `SearchAtG` and `SInvG` only read what `Same`
keeps.
-/

namespace NautyVerified.Proofs.Search

open NautyVerified.Proofs.Dispatch (Ops DispatchRep denseOps)
open NautyVerified.Proofs.Maketargetcell (mtcOf)
open Hex.GraphIso.Nauty

variable {n : Nat}

/-- `s` and `t` agree on every field except the carried store and `order`, and
the stores have the same rows. -/
structure Same (O : Ops) (s t : SearchState n (O.Canon n)) : Prop where
  eq : ∃ c o, t = { s with canong := c, order := o }
  rows : O.rows s.canong = O.rows t.canong

theorem Same.refl {O : Ops} (s : SearchState n (O.Canon n)) : Same O s s :=
  ⟨⟨s.canong, s.order, rfl⟩, rfl⟩

theorem Same.symm {O : Ops} {s t : SearchState n (O.Canon n)} (h : Same O s t) : Same O t s := by
  obtain ⟨⟨c, o, rfl⟩, r⟩ := h
  exact ⟨⟨s.canong, s.order, rfl⟩, r.symm⟩

theorem Same.trans {O : Ops} {s t u : SearchState n (O.Canon n)} (h : Same O s t)
    (h' : Same O t u) : Same O s u := by
  obtain ⟨⟨c, o, rfl⟩, r⟩ := h
  obtain ⟨⟨c', o', rfl⟩, r'⟩ := h'
  exact ⟨⟨c', o', rfl⟩, r.trans r'⟩

/-- A field `Same` keeps. -/
theorem Same.field {O : Ops} {s t : SearchState n (O.Canon n)} (h : Same O s t) {α : Type}
    (f : SearchState n (O.Canon n) → α)
    (hf : ∀ c o, f { s with canong := c, order := o } = f s) : f t = f s := by
  obtain ⟨⟨c, o, rfl⟩, -⟩ := h
  exact hf c o

/-- `chooseTarget` with `maketargetcell` given by `O.targetcell` and the cell scan `mtcOf`. -/
def chooseTargetG (O : Ops) (first : Bool) (G : O.Gr n) (tcLevel level numcells : Nat)
    (st : SearchState n (O.Canon n)) : Int × VSet n × Nat × SearchState n (O.Canon n) := Id.run do
  let mut st := st
  let mut tc : Int := -1
  let mut tcell := VSet.empty
  let mut size := 0
  if (if first then numcells != n
      else numcells < n && (st.eqlevFirst == level || st.compCanon >= 0)) then
    let hinted := !first && st.compCanon < 0
    let hint := if hinted then st.firsttc[level]! else -1
    let (pos, cell, count) :=
      mtcOf n st.lab st.ptn level (O.targetcell G st.lab st.ptn level tcLevel hint)
    tc := Int.ofNat pos
    tcell := cell
    size := count
    if hinted && tc != st.firsttc[level]! then
      st := { st with eqlevFirst := level - 1 }
    st := { st with tctotal := st.tctotal + size }
  if first then
    st := { st with firsttc := st.firsttc.set! level tc }
  return (tc, tcell, size, st)

theorem chooseTargetG_dense (first : Bool) (ctx : Ctx n) (tcLevel level numcells : Nat)
    (st : Search n) :
    chooseTargetG denseOps first ctx tcLevel level numcells st =
      chooseTarget first ctx tcLevel level numcells st := rfl

/-- What nauty.c's node proofs need of a search policy `P` on `O`'s search state. -/
structure PolicyLink (O : Ops) (n : Nat)
    [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)] where
  /-- The policy's invariant of the carried store (dense: `True`). -/
  Inv : O.Gr n → O.Canon n → Prop
  /-- What `visit G level numcells st` needs besides `Inv` (dense: `True`). -/
  VisitOk : O.Gr n → Nat → Nat → SearchState n (O.Canon n) → Prop
  /-- What `chooseTarget _ G _ level numcells st` needs besides `Inv` (dense: `True`). -/
  TargetOk : O.Gr n → Nat → Nat → SearchState n (O.Canon n) → Prop
  visit_numcells : ∀ (G : O.Gr n) level numcells st, Inv G st.canong →
    VisitOk G level numcells st →
    (P.visit G level numcells st).1 = (O.refine G level st.lab st.ptn st.active numcells).numcells
  visit_code : ∀ (G : O.Gr n) level numcells st, Inv G st.canong → VisitOk G level numcells st →
    (P.visit G level numcells st).2.1 = (O.refine G level st.lab st.ptn st.active numcells).longcode
  visit_same : ∀ (G : O.Gr n) level numcells st, Inv G st.canong → VisitOk G level numcells st →
    Same O (visitStG O G level numcells { st with numnodes := st.numnodes + 1 })
      (P.visit G level numcells st).2.2
  visit_inv : ∀ (G : O.Gr n) level numcells st, Inv G st.canong → VisitOk G level numcells st →
    Inv G (P.visit G level numcells st).2.2.canong
  recordFirst_eq : ∀ level code st, P.recordFirst level code st = recordFirst level code st
  compareCodes_eq : ∀ level code st, P.compareCodes level code st = compareCodes level code st
  target_eq : ∀ first (G : O.Gr n) tcLevel level numcells st, Inv G st.canong →
    TargetOk G level numcells st →
    (P.chooseTarget first G tcLevel level numcells st).1 =
        (chooseTargetG O first G tcLevel level numcells st).1 ∧
      (P.chooseTarget first G tcLevel level numcells st).2.1 =
        (chooseTargetG O first G tcLevel level numcells st).2.1 ∧
      (P.chooseTarget first G tcLevel level numcells st).2.2.1 =
        (chooseTargetG O first G tcLevel level numcells st).2.2.1
  target_same : ∀ first (G : O.Gr n) tcLevel level numcells st, Inv G st.canong →
    TargetOk G level numcells st →
    Same O (chooseTargetG O first G tcLevel level numcells st).2.2.2
      (P.chooseTarget first G tcLevel level numcells st).2.2.2
  target_inv : ∀ first (G : O.Gr n) tcLevel level numcells st, Inv G st.canong →
    TargetOk G level numcells st →
    Inv G (P.chooseTarget first G tcLevel level numcells st).2.2.2.canong
  firstterminal_eq : ∀ level st, P.firstterminal level st = firstterminal level st
  classify_eq : ∀ (G : O.Gr n) level numcells st,
    P.classify G level numcells st = O.classify G level numcells st
  classify_inv : ∀ (G : O.Gr n) level numcells st, Inv G st.canong →
    Inv G (O.classify G level numcells st).2.canong
  leafExit_eq : ∀ leaf level st, P.leafExit leaf level st = leafExit leaf level st
  cheapCheck_eq : ∀ first level st, P.cheapCheck first level st = cheapCheck first level st
  cheapautom_eq : ∀ (ptn : Array Nat) level, O.cheapautom ptn level n = cheapautom ptn level n
  child_same : ∀ first level tc tv st,
    Same O (child first level tc tv st) (P.child first level tc tv st)
  child_inv : ∀ (G : O.Gr n) first level tc tv st, Inv G st.canong →
    Inv G (P.child first level tc tv st).canong
  afterChildFirst_eq : ∀ level tv1 st, P.afterChildFirst level tv1 st = afterChildFirst level tv1 st
  leaveChild_eq : ∀ tv st, P.leaveChild tv st = { st with fixedpts := st.fixedpts.erase tv }
  orbit_eq : ∀ st tv, P.orbit st tv = st.orbits[tv]!
  shortprune_eq : ∀ cell st, P.shortprune cell st = shortprune cell st
  longprune_eq : ∀ cell st, P.longprune cell st = longprune cell st.fixedpts st.autos
  recover_same : ∀ inf level st, Same O (recover inf level st) (P.recover inf level st)
  recover_inv : ∀ (G : O.Gr n) inf level st, Inv G st.canong →
    Inv G (P.recover inf level st).canong
  afterSweep_same : ∀ first level size index st,
    Same O (afterSweep first level size index st) (P.afterSweep first level size index st)
  afterSweep_inv : ∀ (G : O.Gr n) first level size index st, Inv G st.canong →
    Inv G (P.afterSweep first level size index st).canong

/-- Dense nauty's policy: every operation is HexGraphIso's (`node_eq_generic`). -/
def denseLink : PolicyLink denseOps n where
  Inv _ _ := True
  VisitOk _ _ _ _ := True
  TargetOk _ _ _ _ := True
  visit_numcells _ _ _ _ _ _ := rfl
  visit_code _ _ _ _ _ _ := rfl
  visit_same _ _ _ _ _ _ := Same.refl _
  visit_inv _ _ _ _ _ _ := trivial
  recordFirst_eq _ _ _ := rfl
  compareCodes_eq _ _ _ := rfl
  target_eq _ _ _ _ _ _ _ _ := ⟨rfl, rfl, rfl⟩
  target_same _ _ _ _ _ _ _ _ := Same.refl _
  target_inv _ _ _ _ _ _ _ _ := trivial
  firstterminal_eq _ _ := rfl
  classify_eq _ _ _ _ := rfl
  classify_inv _ _ _ _ _ := trivial
  leafExit_eq _ _ _ := rfl
  cheapCheck_eq _ _ _ := rfl
  cheapautom_eq _ _ := rfl
  child_same _ _ _ _ _ := Same.refl _
  child_inv _ _ _ _ _ _ _ := trivial
  afterChildFirst_eq _ _ _ := rfl
  leaveChild_eq _ _ := rfl
  orbit_eq _ _ := rfl
  shortprune_eq _ _ := rfl
  longprune_eq _ _ := rfl
  recover_same _ _ _ := Same.refl _
  recover_inv _ _ _ _ _ := trivial
  afterSweep_same _ _ _ _ _ := Same.refl _
  afterSweep_inv _ _ _ _ _ _ _ := trivial

/-! ### What `Same` keeps -/

section Generic

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
  {O : Ops} {D : DispatchRep ge O}

theorem SInvG.same {G : O.Gr n} {s t : SearchState n (O.Canon n)} (h : SInvG O G s)
    (hs : Same O s t) : SInvG O G t := by
  obtain ⟨⟨c, o, rfl⟩, r⟩ := hs
  exact { h with canong := r ▸ h.canong }

theorem SearchAtG.same {m : CompCert4Lean.Common.Memory.mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {s t : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G s pre nsp) (hs : Same O s t) :
    SearchAtG D m S gl cl G t pre nsp := by
  have hi := h.inv.same hs
  obtain ⟨⟨c, o, rfl⟩, r⟩ := hs
  have ha : ArraysG D m S gl cl G { s with canong := c, order := o } :=
    { h.arrays with canong := r ▸ h.arrays.canong }
  exact { h with scalars := { h.scalars with }, stats := { h.stats with }, arrays := ha, inv := hi }

end Generic

end NautyVerified.Proofs.Search

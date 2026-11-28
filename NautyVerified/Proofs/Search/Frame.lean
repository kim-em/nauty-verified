import NautyVerified.Proofs.Search.Spec
import NautyVerified.Proofs.Alloc.Slots

/-!
# Moving `SearchAt` across memory changes

`sep_ne hd`: closes `a ≠ b` for two entries of a pairwise-distinct block list
(`hd : l.Pairwise (· ≠ ·)`, `l` unfolding to a list literal), by locating
both and applying `pw_ne`; blocks that are not in the list are compared by `env_ne` (two blocks
of the `NautyEnv`) or `decide`.

`FieldAt.unch` and the component lemmas move each part of `SearchAt` across an
`Unch m m' W` whose blocks avoid that part's block.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty

open Lean Meta Elab Tactic in
/-- The entries of a list literal, after unfolding. -/
partial def listEntries (e : Expr) : MetaM (Array Expr) := do
  let e ← whnfD e
  match e.getAppFnArgs with
  | (``List.cons, #[_, a, rest]) => return #[a] ++ (← listEntries rest)
  | (``List.nil, _) => return #[]
  | _ => throwError "sep_ne: not a list literal: {e}"

open Lean Meta Elab Tactic in
/-- `a ≠ b` for distinct entries of a pairwise-distinct block list. -/
elab "sep_ne " hd:term : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, a, b) := (← whnfR ty).not?.bind (·.eq?) |>.orElse fun _ =>
      (ty.app3? ``Ne).map fun (α, a, b) => (α, a, b)
    | throwError "sep_ne: goal is not a disequality"
  let hdE ← elabTerm hd none
  let hdT ← whnf (← inferType hdE)
  let l := hdT.appArg!
  let es ← listEntries l
  let idx (x : Expr) : MetaM (Option Nat) := do
    for i in [0:es.size] do
      if ← withReducibleAndInstances (isDefEq es[i]! x) then return some i
    return none
  match ← idx a, ← idx b with
  | some i, some j =>
    if i < j then
      evalTactic (← `(tactic| exact NautyVerified.Proofs.Refine.pw_ne $hd $(Syntax.mkNumLit (toString i))
        $(Syntax.mkNumLit (toString j)) (by decide) (by simp [SLoc.blocks, SLoc.litG])))
    else if j < i then
      evalTactic (← `(tactic| exact Ne.symm (NautyVerified.Proofs.Refine.pw_ne $hd $(Syntax.mkNumLit (toString j))
        $(Syntax.mkNumLit (toString i)) (by decide) (by simp [SLoc.blocks, SLoc.litG]))))
    else throwError "sep_ne: both sides are entry {i}"
  | _, _ => evalTactic (← `(tactic| first | env_ne | decide))

theorem pw_ne {l : List block} (h : l.Pairwise (· ≠ ·)) (i j : Nat) (hij : i < j)
    (hj : j < l.length) : l[i]'(Nat.lt_trans hij hj) ≠ l[j] :=
  Refine.pw_ne h i j hij hj

theorem FieldAt.unch {m m' : mem} {W : block → Prop} {chunk : memory_chunk} {b : block} {off : Int}
    {v : val} (h : FieldAt m chunk b off v) (hu : Unch m m' W) (hb : ¬ W b) : FieldAt m' chunk b off v :=
  ⟨by rw [hu.load _ _ _ hb]; exact h.load, hu.access _ _ _ _ hb h.writable⟩

/-- `∀ z ∈ [b₁, …], ¬ W z` for `W` a disjunction of equalities with blocks of the
same distinct list. -/
macro "sep_all " hd:term : tactic =>
  `(tactic| (simp only [List.forall_mem_cons] <;>
    simp only [List.mem_nil_iff, false_implies, implies_true, and_true, not_or, List.mem_cons,
      or_false] <;> (repeat' constructor) <;> sep_ne $hd))

/-- `¬ b ∈ [b₁, …]` for distinct blocks. -/
macro "sep_notin " hd:term : tactic =>
  `(tactic| (simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] <;>
    (repeat' constructor) <;> sep_ne $hd))

theorem _root_.NautyVerified.Logic.Unch.snoc {m m₁ m₂ : mem} {w : List block} {b : block} (h : Unch m m₁ (· ∈ w))
    (hu : Unch m₁ m₂ (· = b)) : Unch m m₂ (· ∈ b :: w) :=
  (h.mono fun _ hz => List.mem_cons_of_mem _ hz).trans
    (hu.mono fun _ hz => by rw [hz]; exact List.mem_cons_self)

theorem _root_.NautyVerified.Logic.Unch.sub {m m' : mem} {l l' : List block}
    (h : Unch m m' (· ∈ l)) (hs : ∀ z ∈ l, z ∈ l') : Unch m m' (· ∈ l') :=
  h.mono fun z hz => hs z hz

/-- Carry facts `h₁ …` across `hu : Unch m m' (· = b)`, each about a block other than `b`
(distinctness from `hd`). -/
macro "fwd " hd:ident ppSpace hu:ident " [" hs:ident* "]" : tactic => do
  let tacs ← hs.mapM fun h =>
    `(tactic| replace $h:ident := ($h).unch $hu (fun e => absurd e (by sep_ne $hd)))
  `(tactic| ($[$tacs]*))

/-- Carry `Keep` facts `h₁ …` across `hu : Unch m m' (· = b)`. -/
macro "fwdK " hd:ident ppSpace hu:ident " [" hs:ident* "]" : tactic => do
  let tacs ← hs.mapM fun h =>
    `(tactic| replace $h:ident := ($h).trans (Keep.unch $hu (fun e => absurd e (by sep_ne $hd))))
  `(tactic| ($[$tacs]*))

theorem Fixed.unch {n : Nat} {m m' : mem} {S : SLoc} {W : block → Prop} (h : Fixed n m S)
    (hu : Unch m m' W)
    (hW : ∀ z ∈ [Block.g, Block.canong, Block.orbits, Block.stats, Block.workspace, Block.worktop,
      Block.m, Block.n, Block.getcanon, Block.digraph, Block.writeautoms, Block.domarkers,
      Block.doschreier, Block.tcLevel, Block.invarproc, Block.usernodeproc, Block.userlevelproc,
      Block.usercanonproc, Block.userautomproc, Block.dispatch, Block.killRequest, Block.allocM,
      Block.mininvarlevel, Block.maxinvarlevel, Block.invararg],
      ¬ W z) : Fixed n m' S := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, -⟩ := hW
  obtain ⟨v1, f1⟩ := h.mininv
  obtain ⟨v2, f2⟩ := h.maxinv
  obtain ⟨v3, f3⟩ := h.invarg
  exact ⟨h.g.unch hu h1, h.canong.unch hu h2, h.orbits.unch hu h3, h.stats.unch hu h4,
    h.workspace.unch hu h5, h.worktop.unch hu h6, h.mm.unch hu h7, h.nn.unch hu h8,
    h.getcanon.unch hu h9, h.digraph.unch hu h10, h.writeautoms.unch hu h11,
    h.domarkers.unch hu h12, h.doschreier.unch hu h13, h.tcLevel.unch hu h14,
    h.invarproc.unch hu h15, h.usernodeproc.unch hu h16, h.userlevelproc.unch hu h17,
    h.usercanonproc.unch hu h18, h.userautomproc.unch hu h19, h.dIsautom.unch hu h20,
    h.dTestcanlab.unch hu h20, h.dUpdatecan.unch hu h20, h.dRefine.unch hu h20,
    h.dRefine1.unch hu h20, h.dCheapautom.unch hu h20, h.dTargetcell.unch hu h20,
    hu.access _ _ _ _ h21 h.kill, h.allocM.unch hu h22, ⟨v1, f1.unch hu h23⟩, ⟨v2, f2.unch hu h24⟩,
    ⟨v3, f3.unch hu h25⟩, h.dFreedyn.unch hu h20, h.dCleanup.unch hu h20⟩

theorem Tables.unch {m m' : mem} {W : block → Prop} (h : Tables m) (hu : Unch m m' W)
    (hW : ∀ z ∈ [Program.Block.nautyBit, Block.naugraphBit, Block.nautilBit,
      Block.naugraphBytecount, Block.leftbit], ¬ W z) : Tables m' := by
  simp only [List.forall_mem_cons] at hW
  exact ⟨h.nautyBit.unch hu hW.1, h.naugraphBit.unch hu hW.2.1, h.nautilBit.unch hu hW.2.2.1,
    Refine.LeftbitTable.unch h.left hu hW.2.2.2.2.1, Refine.BytecountTable.unch h.bytes hu hW.2.2.2.1⟩

theorem Scalars.unch {n : Nat} {m m' : mem} {st : Search n} {nsp : Bool} {W : block → Prop}
    (h : Scalars m st nsp) (hu : Unch m m' W)
    (hW : ∀ z ∈ [Block.gcaFirst, Block.gcaCanon, Block.noncheaplevel, Block.allsamelevel,
      Block.eqlevFirst, Block.eqlevCanon, Block.compCanon, Block.samerows, Block.canonlevel,
      Block.stabvertex, Block.cosetindex, Block.needshortprune], ¬ W z) : Scalars m' st nsp := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := hW
  exact ⟨h.gcaFirst.unch hu h1, h.gcaCanon.unch hu h2, h.noncheaplevel.unch hu h3,
    h.allsamelevel.unch hu h4, h.eqlevFirst.unch hu h5, h.eqlevCanon.unch hu h6,
    h.compCanon.unch hu h7, h.samerows.unch hu h8, h.canonlevel.unch hu h9,
    h.stabvertex.unch hu h10, h.cosetindex.unch hu h11, h.needshortprune.unch hu h12⟩

theorem Stats.unch {n : Nat} {m m' : mem} {S : SLoc} {st : Search n} {pre : Bool}
    {W : block → Prop} (h : Stats m S st pre) (hu : Unch m m' W) (hW : ¬ W S.bst) :
    Stats m' S st pre :=
  ⟨h.numorbits.unch hu hW, h.numgenerators.unch hu hW, h.numnodes.unch hu hW,
    h.numbadleaves.unch hu hW, fun hp => (h.maxlevel hp).unch hu hW,
    hu.access _ _ _ _ hW h.maxlevelW, h.tctotal.unch hu hW, h.canupdates.unch hu hW, h.fits,
    fun o ho => (Keep.unch hu hW).perm _ _ (h.perm o ho), h.errstatus.unch hu hW,
    let ⟨x, hx⟩ := h.grpsize1; ⟨x, hx.unch hu hW⟩, let ⟨i, hi⟩ := h.grpsize2; ⟨i, hi.unch hu hW⟩⟩

theorem StatsFix.unch {m m' : mem} {S : SLoc} {W : block → Prop} (h : StatsFix m S)
    (hu : Unch m m' W) (hW : ¬ W S.bst) : StatsFix m' S :=
  ⟨fun o ho => (Keep.unch hu hW).perm _ _ (h.perm o ho), h.errstatus.unch hu hW,
    let ⟨x, hx⟩ := h.grpsize1; ⟨x, hx.unch hu hW⟩, let ⟨i, hi⟩ := h.grpsize2; ⟨i, hi.unch hu hW⟩⟩

theorem CanongAt.unch {n : Nat} {m m' : mem} {S : SLoc} {rows : Array (VSet n)} {sr : Nat}
    {W : block → Prop} (h : CanongAt m S rows sr) (hu : Unch m m' W) (hW : ¬ W S.bc) :
    CanongAt m' S rows sr :=
  let ⟨cw, ha, hr⟩ := h.arr
  ⟨cw, ha.unch hu hW, hr⟩

theorem AutosAt.unch {n : Nat} {m m' : mem} {S : SLoc} {autos : Array (VSet n × VSet n)}
    {W : block → Prop} (h : AutosAt m S autos) (hu : Unch m m' W) (hW : ¬ W S.bws)
    (hF : ¬ W Block.fmptr) : AutosAt m' S autos :=
  let ⟨ww, ha, hr⟩ := h.arr
  ⟨h.size, ⟨ww, ha.unch hu hW, hr⟩, h.fmptr.unch hu hF⟩

theorem Arrays.unch {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {W : block → Prop} (h : Arrays m S ctx st) (hu : Unch m m' W)
    (hW : ∀ z ∈ [S.bl, S.bp, S.bo, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bc,
      S.bws, Block.fmptr, S.bg], ¬ W z) : Arrays m' S ctx st := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hW
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu h1, h.ptn.unch hu h2, h.orbits.unch hu h3, ⟨aw, ha.unch hu h4, har⟩,
    ⟨fw, hf.unch hu h5, hfr⟩, ⟨wv, hwv.unch hu h6⟩, h.firstlab.unch hu h7,
    h.canonlab.unch hu h8, h.firstcode.unch hu h9, h.canoncode.unch hu h10,
    h.firsttc.unch hu h11, h.canong.unch hu h12, h.autos.unch hu h13 h14,
    ⟨h.graph.arr.unch hu h15, h.graph.rep⟩⟩

theorem Dyns.unch {n : Nat} {m m' : mem} {S : SLoc} {W : block → Prop} (h : Dyns n m S)
    (hu : Unch m m' W)
    (hW : ∀ z ∈ [Program.Block.nautyActive, Program.Block.nautyActiveSz,
      Program.Block.nautyFixedpts, Program.Block.nautyFixedptsSz, Program.Block.nautyWorkperm,
      Program.Block.nautyWorkpermSz, Program.Block.nautyFirstlab, Program.Block.nautyFirstlabSz,
      Program.Block.nautyCanonlab, Program.Block.nautyCanonlabSz, Program.Block.nautyFirstcode,
      Program.Block.nautyFirstcodeSz, Program.Block.nautyCanoncode,
      Program.Block.nautyCanoncodeSz, Program.Block.nautyFirsttc, Program.Block.nautyFirsttcSz,
      S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC,
      Block.naugraphDnwork, Block.naugraphDnworkSz, S.bws], ¬ W z) : Dyns n m' S := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16,
    b1, b2, b3, b4, b5, b6, b7, b8, g17, g18, b9, -⟩ := hW
  exact { h with
    workspace := h.workspace.keep hu g17 g18 fun _ => Keep.unch hu b9
    active := h.active.keep hu g1 g2 fun _ => Keep.unch hu b1
    fixedpts := h.fixedpts.keep hu g3 g4 fun _ => Keep.unch hu b2
    workperm := h.workperm.keep hu g5 g6 fun _ => Keep.unch hu b3
    firstlab := h.firstlab.keep hu g7 g8 fun _ => Keep.unch hu b4
    canonlab := h.canonlab.keep hu g9 g10 fun _ => Keep.unch hu b5
    firstcode := h.firstcode.keep hu g11 g12 fun _ => Keep.unch hu b6
    canoncode := h.canoncode.keep hu g13 g14 fun _ => Keep.unch hu b7
    firsttc := h.firsttc.keep hu g15 g16 fun _ => Keep.unch hu b8 }

theorem WorkAt.unch {n : Nat} {m m' : mem} {S : SLoc} {L : List block} {W : block → Prop}
    (h : WorkAt n m S L) (hu : Unch m m' W)
    (hG : ∀ z ∈ [Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
      Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
      Block.nautilWorkperm, Block.nautilWorkpermSz], ¬ W z)
    (hwk : ∀ z, IsWork m z → ¬ W z) : WorkAt n m' S L := by
  simp only [List.forall_mem_cons] at hG
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, -⟩ := hG
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, rest⟩ := h.arr
  exact ⟨⟨cW, bW, cS, bS, cB, bB, cN, bN,
    dW.keep hu g1 g2 fun hc => Keep.unch hu (hwk _ (.inl ⟨cW, hc, dW⟩)),
    dS.keep hu g3 g4 fun hc => Keep.unch hu (hwk _ (.inr (.inl ⟨cS, hc, dS⟩))),
    dB.keep hu g5 g6 fun hc => Keep.unch hu (hwk _ (.inr (.inr (.inl ⟨cB, hc, dB⟩)))),
    dN.keep hu g7 g8 fun hc => Keep.unch hu (hwk _ (.inr (.inr (.inr ⟨cN, hc, dN⟩)))), rest⟩⟩

/-- `SearchAt` across a change avoiding every block of `S` and the work blocks in use. -/
theorem SearchAt.unch {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} {W : block → Prop} (h : SearchAt m S ctx st pre nsp) (hu : Unch m m' W)
    (hS : ∀ z ∈ S.blocks, ¬ W z) (hwk : ∀ z, IsWork m z → ¬ W z) :
    SearchAt m' S ctx st pre nsp :=
  { h with
    fixed := h.fixed.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks])
    scalars := h.scalars.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks])
    stats := h.stats.unch hu (hS _ (by simp [SLoc.blocks, SLoc.litG]))
    arrays := h.arrays.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks])
    dyns := h.dyns.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks])
    work := h.work.unch hu (fun z hz => hS z (by revert z; simp [SLoc.blocks])) hwk
    tables := h.tables.unch hu fun z hz => hS z (by revert z; simp [SLoc.blocks]) }

/-! ### For any dispatch representation

The component lemmas for `SearchAtG D`. Moving `D`'s scratch state needs the
step to keep blocks valid (`DispatchRep.work_unch`). -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep ETables)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} (D : DispatchRep ge O)

/-- The shared globals `FixedG` reads. -/
abbrev fixedBlocks : List block :=
  [E.g, E.canong, E.orbits, E.stats, E.workspace, E.worktop, E.m, E.n, E.getcanon, E.digraph,
   E.writeautoms, E.domarkers, E.doschreier, E.tcLevel, E.invarproc, E.usernodeproc,
   E.userlevelproc, E.usercanonproc, E.userautomproc, E.dispatch, E.killRequest, E.allocM,
   E.mininvarlevel, E.maxinvarlevel, E.invararg]

theorem FixedG.unch {D : DispatchRep ge O} {n : Nat} {m m' : mem} {S : SLoc} {W : block → Prop}
    (h : FixedG D n m S) (hu : Unch m m' W) (hW : ∀ z ∈ fixedBlocks, ¬ W z) : FixedG D n m' S := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, -⟩ := hW
  obtain ⟨v1, f1⟩ := h.mininv
  obtain ⟨v2, f2⟩ := h.maxinv
  obtain ⟨v3, f3⟩ := h.invarg
  exact ⟨h.g.unch hu h1, h.canong.unch hu h2, h.orbits.unch hu h3, h.stats.unch hu h4,
    h.workspace.unch hu h5, h.worktop.unch hu h6, h.mm.unch hu h7, h.nn.unch hu h8,
    h.getcanon.unch hu h9, h.digraph.unch hu h10, h.writeautoms.unch hu h11,
    h.domarkers.unch hu h12, h.doschreier.unch hu h13, h.tcLevel.unch hu h14,
    h.invarproc.unch hu h15, h.usernodeproc.unch hu h16, h.userlevelproc.unch hu h17,
    h.usercanonproc.unch hu h18, h.userautomproc.unch hu h19, h.dIsautom.unch hu h20,
    h.dTestcanlab.unch hu h20, h.dUpdatecan.unch hu h20, h.dRefine.unch hu h20,
    h.dRefine1.unch hu h20, h.dCheapautom.unch hu h20, h.dTargetcell.unch hu h20,
    hu.access _ _ _ _ h21 h.kill, h.allocM.unch hu h22, ⟨v1, f1.unch hu h23⟩, ⟨v2, f2.unch hu h24⟩,
    ⟨v3, f3.unch hu h25⟩, h.dFreedyn.unch hu h20, h.dCleanup.unch hu h20⟩

/-- nauty.c's static scalars. -/
abbrev scalarBlocks : List block :=
  [E.gcaFirst, E.gcaCanon, E.noncheaplevel, E.allsamelevel, E.eqlevFirst, E.eqlevCanon,
   E.compCanon, E.samerows, E.canonlevel, E.stabvertex, E.cosetindex, E.needshortprune]

theorem ScalarsG.unch {n : Nat} {κ : Type} {m m' : mem} {st : SearchState n κ} {nsp : Bool}
    {W : block → Prop} (h : ScalarsG m st nsp) (hu : Unch m m' W)
    (hW : ∀ z ∈ scalarBlocks, ¬ W z) : ScalarsG m' st nsp := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := hW
  exact ⟨h.gcaFirst.unch hu h1, h.gcaCanon.unch hu h2, h.noncheaplevel.unch hu h3,
    h.allsamelevel.unch hu h4, h.eqlevFirst.unch hu h5, h.eqlevCanon.unch hu h6,
    h.compCanon.unch hu h7, h.samerows.unch hu h8, h.canonlevel.unch hu h9,
    h.stabvertex.unch hu h10, h.cosetindex.unch hu h11, h.needshortprune.unch hu h12⟩

theorem StatsG.unch {n : Nat} {κ : Type} {m m' : mem} {S : SLoc} {st : SearchState n κ}
    {pre : Bool} {W : block → Prop} (h : StatsG m S st pre) (hu : Unch m m' W) (hW : ¬ W S.bst) :
    StatsG m' S st pre :=
  ⟨h.numorbits.unch hu hW, h.numgenerators.unch hu hW, h.numnodes.unch hu hW,
    h.numbadleaves.unch hu hW, fun hp => (h.maxlevel hp).unch hu hW,
    hu.access _ _ _ _ hW h.maxlevelW, h.tctotal.unch hu hW, h.canupdates.unch hu hW, h.fits,
    fun o ho => (Keep.unch hu hW).perm _ _ (h.perm o ho), h.errstatus.unch hu hW,
    let ⟨x, hx⟩ := h.grpsize1; ⟨x, hx.unch hu hW⟩, let ⟨i, hi⟩ := h.grpsize2; ⟨i, hi.unch hu hW⟩⟩

theorem AutosAtG.unch {n : Nat} {m m' : mem} {S : SLoc} {autos : Array (VSet n × VSet n)}
    {W : block → Prop} (h : AutosAtG m S autos) (hu : Unch m m' W) (hW : ¬ W S.bws)
    (hF : ¬ W E.fmptr) : AutosAtG m' S autos :=
  let ⟨ww, ha, hr⟩ := h.arr
  ⟨h.size, ⟨ww, ha.unch hu hW, hr⟩, h.fmptr.unch hu hF⟩

theorem ArraysG.unch {D : DispatchRep ge O} {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {W : block → Prop}
    (h : ArraysG D m S gl cl G st) (hu : Unch m m' W)
    (hW : ∀ z ∈ [S.bl, S.bp, S.bo, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws,
      E.fmptr], ¬ W z)
    (hg : ∀ z ∈ D.graphBlocks gl S.bg, ¬ W z) (hc : ∀ z ∈ D.canonBlocks cl S.bc, ¬ W z) :
    ArraysG D m' S gl cl G st := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14, -⟩ := hW
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu h1, h.ptn.unch hu h2, h.orbits.unch hu h3, ⟨aw, ha.unch hu h4, har⟩,
    ⟨fw, hf.unch hu h5, hfr⟩, ⟨wv, hwv.unch hu h6⟩, h.firstlab.unch hu h7,
    h.canonlab.unch hu h8, h.firstcode.unch hu h9, h.canoncode.unch hu h10,
    h.firsttc.unch hu h11, D.canon_unch h.canong hu hc, h.autos.unch hu h13 h14,
    D.graph_unch h.graph hu hg⟩

theorem DynsG.unch {D : DispatchRep ge O} {n : Nat} {m m' : mem} {S : SLoc} {W : block → Prop}
    (h : DynsG D n m S) (hu : Unch m m' W)
    (hW : ∀ z ∈ [E.nautyActive, E.nautyActiveSz, E.nautyFixedpts, E.nautyFixedptsSz,
      E.nautyWorkperm, E.nautyWorkpermSz, E.nautyFirstlab, E.nautyFirstlabSz, E.nautyCanonlab,
      E.nautyCanonlabSz, E.nautyFirstcode, E.nautyFirstcodeSz, E.nautyCanoncode,
      E.nautyCanoncodeSz, E.nautyFirsttc, E.nautyFirsttcSz,
      S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, D.wsP, D.wsS, S.bws], ¬ W z) :
    DynsG D n m' S := by
  simp only [List.forall_mem_cons] at hW
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16,
    b1, b2, b3, b4, b5, b6, b7, b8, g17, g18, b9, -⟩ := hW
  exact { h with
    workspace := h.workspace.keep hu g17 g18 fun _ => Keep.unch hu b9
    active := h.active.keep hu g1 g2 fun _ => Keep.unch hu b1
    fixedpts := h.fixedpts.keep hu g3 g4 fun _ => Keep.unch hu b2
    workperm := h.workperm.keep hu g5 g6 fun _ => Keep.unch hu b3
    firstlab := h.firstlab.keep hu g7 g8 fun _ => Keep.unch hu b4
    canonlab := h.canonlab.keep hu g9 g10 fun _ => Keep.unch hu b5
    firstcode := h.firstcode.keep hu g11 g12 fun _ => Keep.unch hu b6
    canoncode := h.canoncode.keep hu g13 g14 fun _ => Keep.unch hu b7
    firsttc := h.firsttc.keep hu g15 g16 fun _ => Keep.unch hu b8 }

/-- Moving `WorkG` needs the written globals, nautil.c's pair and the blocks in use
unchanged and the valid blocks kept valid. -/
theorem WorkG.unch {D : DispatchRep ge O} {m m' : mem} {L : List block} {W : block → Prop}
    (h : WorkG D m L) (hu : Unch m m' W) (hG : ∀ z ∈ D.wglobs, ¬ W z)
    (hN : ¬ W E.nautilWorkperm ∧ ¬ W E.nautilWorkpermSz)
    (hwk : ∀ z, IsWorkG D m z → ¬ W z) (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) :
    WorkG D m' L ∧ ∀ z, IsWorkG D m' z → IsWorkG D m z := by
  obtain ⟨cN, bN, dN, nN, uN⟩ := h.nautil
  obtain ⟨hw', back⟩ := D.work_unch h.disp hu hG (fun z hz => hwk z (.inl hz)) hv
  have dN' := dN.keep hu hN.1 hN.2 fun hc => Keep.unch hu (hwk _ (.inr ⟨cN, hc, dN⟩))
  refine ⟨⟨hw', ⟨cN, bN, dN', nN, fun hc hb => uN hc (back _ hb)⟩,
    fun z hz => h.notin z (back z hz)⟩, ?_⟩
  rintro z (hz | ⟨c, hc, d⟩)
  · exact .inl (back z hz)
  · have e := d.same_block dN' hc
    have hcc := d.same_cap dN'
    subst e; subst hcc
    exact .inr ⟨_, hc, dN⟩

theorem TablesG.unch {D : DispatchRep ge O} {m m' : mem} {W : block → Prop} (h : TablesG D m)
    (hu : Unch m m' W) (h1 : ¬ W E.nautyBit) (h2 : ¬ W E.nautilBit) (h3 : ¬ W E.leftbit)
    (hg : ∀ z ∈ D.globs, z ∉ D.wglobs → ¬ W z) : TablesG D m' :=
  ⟨h.env.unch hu h1 h2 h3, D.tables_unch h.disp hu hg⟩

/-- A scratch block in use is none of the blocks of `S`. -/
theorem SearchAtG.work_not {D : DispatchRep ge O} {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {z : block} (hz : IsWorkG D m z) :
    z ∉ S.blocksG D gl cl := by
  rcases hz with hz | ⟨c, hc, d⟩
  · exact h.work.notin z hz
  · obtain ⟨cN, bN, dN, nN, -⟩ := h.work.nautil
    have e := d.same_block dN hc
    have hcc := d.same_cap dN
    subst e; subst hcc
    exact nN hc

/-! ### Distinctness of the blocks of `S.blocksG`

`SearchAtG.lit`: the list entries of `S.blocksG` (`SLoc.litG`) are pairwise
distinct, for `sep_ne h.lit`. `SearchAtG.graph_ne`, `canon_ne`, `globs_ne`:
a block of the graph's or the store's representation, or one of `D`'s
globals, differs from every block of the other parts of `S.blocksG`. -/

theorem SearchAtG.lit {D : DispatchRep ge O} {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) : S.litG.Pairwise (· ≠ ·) :=
  h.distinct.sublist (S.litG_sub D gl cl)

theorem ne_of_split {l₁ l₂ l₃ : List block} (h : (l₁ ++ l₂ ++ l₃).Pairwise (· ≠ ·)) {a b : block}
    (ha : a ∈ l₂) (hb : b ∈ l₁ ∨ b ∈ l₃) : a ≠ b := by
  have h1 := List.pairwise_append.1 h
  have h2 := List.pairwise_append.1 h1.1
  rcases hb with hb | hb
  · exact (h2.2.2 b hb a ha).symm
  · exact h1.2.2 a (List.mem_append_right _ ha) b hb

theorem SearchAtG.graph_ne {D : DispatchRep ge O} {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {z y : block} (hz : z ∈ D.graphBlocks gl S.bg)
    (hy : y ∈ [S.bl, S.bp, S.bo, S.bst] ∨ y ∈ D.canonBlocks cl S.bc ∨
      y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ∨ y ∈ envSearch ∨
      y ∈ D.globs) : z ≠ y := by
  have hd : ([] ++ D.graphBlocks gl S.bg ++ ([S.bl, S.bp, S.bo, S.bst] ++ D.canonBlocks cl S.bc ++
      [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ++ envSearch ++
      D.globs)).Pairwise (· ≠ ·) := by
    have := h.distinct; simp only [SLoc.blocksG, List.append_assoc] at this ⊢; exact this
  refine ne_of_split hd hz (.inr ?_)
  simp only [List.mem_append]
  rcases hy with hy | hy | hy | hy | hy
  · exact .inl (.inl (.inl (.inl hy)))
  · exact .inl (.inl (.inl (.inr hy)))
  · exact .inl (.inl (.inr hy))
  · exact .inl (.inr hy)
  · exact .inr hy

theorem SearchAtG.canon_ne {D : DispatchRep ge O} {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {z y : block} (hz : z ∈ D.canonBlocks cl S.bc)
    (hy : y ∈ D.graphBlocks gl S.bg ∨ y ∈ [S.bl, S.bp, S.bo, S.bst] ∨
      y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ∨ y ∈ envSearch ∨
      y ∈ D.globs) : z ≠ y := by
  have hd : (D.graphBlocks gl S.bg ++ [S.bl, S.bp, S.bo, S.bst] ++ D.canonBlocks cl S.bc ++
      ([S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ++ envSearch ++
      D.globs)).Pairwise (· ≠ ·) := by
    have := h.distinct; simp only [SLoc.blocksG, List.append_assoc] at this ⊢; exact this
  refine ne_of_split hd hz ?_
  simp only [List.mem_append]
  rcases hy with hy | hy | hy | hy | hy
  · exact .inl (.inl hy)
  · exact .inl (.inr hy)
  · exact .inr (.inl (.inl hy))
  · exact .inr (.inl (.inr hy))
  · exact .inr (.inr hy)

theorem SearchAtG.globs_ne {D : DispatchRep ge O} {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {z y : block} (hz : z ∈ D.globs)
    (hy : y ∈ D.graphBlocks gl S.bg ∨ y ∈ [S.bl, S.bp, S.bo, S.bst] ∨ y ∈ D.canonBlocks cl S.bc ∨
      y ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ∨ y ∈ envSearch) :
    z ≠ y := by
  have hd : (D.graphBlocks gl S.bg ++ [S.bl, S.bp, S.bo, S.bst] ++ D.canonBlocks cl S.bc ++
      [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ++ envSearch ++
      D.globs ++ []).Pairwise (· ≠ ·) := by
    rw [List.append_nil]; exact h.distinct
  refine ne_of_split hd hz (.inl ?_)
  simp only [List.mem_append]
  rcases hy with hy | hy | hy | hy | hy
  · exact .inl (.inl (.inl (.inl hy)))
  · exact .inl (.inl (.inl (.inr hy)))
  · exact .inl (.inl (.inr hy))
  · exact .inl (.inr hy)
  · exact .inr hy

theorem SLoc.mem_blocksG_of {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {z : block}
    (h : z ∈ D.graphBlocks gl S.bg ∨ z ∈ [S.bl, S.bp, S.bo, S.bst] ∨ z ∈ D.canonBlocks cl S.bc ∨
      z ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ∨
      z ∈ envSearch ∨ z ∈ D.globs) : z ∈ S.blocksG D gl cl := by
  simp only [SLoc.blocksG, List.mem_append]
  rcases h with h | h | h | h | h | h
  · exact .inl (.inl (.inl (.inl (.inl h))))
  · exact .inl (.inl (.inl (.inl (.inr h))))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · exact .inr h

/-- `SearchAtG` across a change avoiding every block of `S` and the scratch blocks
in use, keeping valid blocks valid. -/
theorem SearchAtG.unch {D : DispatchRep ge O} {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc}
    {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {W : block → Prop} (h : SearchAtG D m S gl cl G st pre nsp) (hu : Unch m m' W)
    (hS : ∀ z ∈ S.blocksG D gl cl, ¬ W z) (hwk : ∀ z, IsWorkG D m z → ¬ W z)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) :
    SearchAtG D m' S gl cl G st pre nsp :=
  have hE : ∀ z ∈ envSearch, ¬ W z := fun z hz => hS z (SLoc.mem_blocksG_of D (by simp [hz]))
  have hV : ∀ z ∈ [S.bl, S.bp, S.bo, S.bst], ¬ W z := fun z hz =>
    hS z (SLoc.mem_blocksG_of D (.inr (.inl hz)))
  have hV' : ∀ z ∈ [S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA], ¬ W z :=
    fun z hz => hS z (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inl hz)))))
  have hD : ∀ z ∈ D.globs, ¬ W z := fun z hz =>
    hS z (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inr hz))))))
  { h with
    fixed := h.fixed.unch hu fun z hz => hE z (by revert z; simp)
    scalars := h.scalars.unch hu fun z hz => hE z (by revert z; simp)
    stats := h.stats.unch hu (hV _ (by simp))
    arrays := h.arrays.unch hu (fun z hz => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        iterate 3 exact hV _ (by simp)
        iterate 9 exact hV' _ (by simp)
        exact hE _ (by simp))
      (fun z hz => hS z (SLoc.mem_blocksG_of D (.inl hz)))
      (fun z hz => hS z (SLoc.mem_blocksG_of D (.inr (.inr (.inl hz)))))
    dyns := h.dyns.unch hu fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 16 exact hE _ (by simp)
      iterate 8 exact hV' _ (by simp)
      exact hD _ D.wsP_mem
      exact hD _ D.wsS_mem
      exact hV' _ (by simp)
    work := (h.work.unch hu (fun z hz => hD z (D.wglobs_sub z hz))
      ⟨hE _ (by simp), hE _ (by simp)⟩ hwk hv).1
    tables := h.tables.unch hu (hE _ (by simp)) (hE _ (by simp)) (hE _ (by simp))
      fun z hz _ => hD z hz }

end Generic

/-- A work block in use is none of the blocks of `S` (from `SearchAtG.work_not`). -/
theorem SearchAt.work_not {n : Nat} {m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) {z : block} (hz : IsWork m z) :
    z ∉ S.blocks := fun hm =>
  h.toG.work_not (isWork_dense.2 hz) (SLoc.mem_blocksG.2 hm)

end NautyVerified.Proofs.Search

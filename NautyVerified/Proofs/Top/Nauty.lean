import NautyVerified.Proofs.Top.NautyEntry
import NautyVerified.Proofs.Top.Densenauty
import NautyVerified.Proofs.Top.NautyFree
import NautyVerified.Proofs.Top.NautyRoot
import NautyVerified.Proofs.Search.Node.FirstBody
import NautyVerified.Proofs.Search.Node.Nodes
import NautyVerified.Spec.SearchInfRun
import NautyVerified.Proofs.Search.Emit
import NautyVerified.Proofs.Harness.Main

/-!
# `nauty()` satisfies `nautySpec`

`nauty_satisfies`: for an emission `Em` obeying both laws (`EmLawOff`,
`EmLawFirst`) whose root value is the words of `gens`, `nauty()` satisfies
`nautySpec`, the specification `densenauty` calls it with. The proof enters
the function (`nauty_entry`), runs the stages of `Top/NautySyntax.lean` in
order, establishes the root search state `SearchAt … (initialC …) true false`
from what the stages and the initial memory leave, calls the root node
(`root_satisfies`, from `nodes_satisfies` and `firstpathnode_body`), and reads
the result off HexGraphIso's run (`SearchInf.runTraced_inf`, `orbits_inf`).
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search
open NautyVerified.Proofs.Alloc (DynAt Keep Zeros)
open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-- The root `firstpathnode0` call meets its specification. -/
theorem root_satisfies {k : Nat} (G : Colored n k) (Em : Bool → Nat → Nat → Search n → List Int)
    (hOff : EmLawOff Em ⟨rowsOf G⟩) (hFirst : EmLawFirst Em ⟨rowsOf G⟩) (S : SLoc) :
    ∀ st nc ch, Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpecG xi G Em S st 1 nc ch) := by
  have hRef : Refine.RefineFn xi S.M (.Vptr S.refineBlock Ptrofs.zero) := by
    unfold SLoc.refineBlock
    split
    · rename_i h; rw [h]; exact Refine.refineFn_refine1'
    · exact Refine.refineFn_refine' _
  exact fun st nc ch => (nodes_satisfies G Em hOff S hRef
    (fun level hF hO => firstpathnode_body G Em hFirst S level hRef hF hO) 1 st nc ch).1

/-- A change outside `b` keeps its permissions over a range. -/
theorem rperm_unch {m m' : mem} {W : block → Prop} (hu : Unch m m' W) {b : block} (hb : ¬ W b)
    {lo hi : Z} {p : Common.Memtype.permission} (h : Mem.range_perm m b lo hi .Cur p) :
    Mem.range_perm m' b lo hi .Cur p :=
  fun o ho => (Keep.unch hu hb).perm _ _ (h o ho)

/-- Kept accesses keep permissions. -/
theorem rperm_acc {m m' : mem} {b : block}
    (h : ∀ c o p, Mem.valid_access m c b o p → Mem.valid_access m' c b o p)
    {lo hi : Z} {p : Common.Memtype.permission} (hr : Mem.range_perm m b lo hi .Cur p) :
    Mem.range_perm m' b lo hi .Cur p := by
  intro ofs hofs
  have hva : Mem.valid_access m .Mint8unsigned b ofs p := by
    refine ⟨fun o ho => ?_, ⟨ofs, by
      apply intOfZ_injective
      simp [show intOfZ (Common.Memdata.align_chunk .Mint8unsigned) = 1 from rfl]⟩⟩
    have h1 : intOfZ ofs ≤ intOfZ o := ho.1
    have h2 : intOfZ o < intOfZ ofs + 1 := by
      have := ho.2; change intOfZ _ < intOfZ _ at this
      simpa [intOfZ_add, show intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 from rfl] using this
    rw [show o = ofs by apply intOfZ_injective; omega]
    exact hr ofs hofs
  exact (h _ _ _ hva).1 ofs ⟨by change intOfZ _ ≤ intOfZ _; exact Int.le_refl _, by
    change intOfZ _ < intOfZ _
    simp only [intOfZ_add, show intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 from rfl]; omega⟩

/-- A `DYNALLSTAT` pair at capacity 0 has no block in use. -/
theorem dyn_zero_ne {m : mem} {bp bs : block} {c cap : Nat} {b₀ b : block}
    (h0 : DynAt m bp bs c 0 b₀) (h : DynAt m bp bs c cap b) (hc : 0 < cap) : False := by
  have := h0.capLd.symm.trans h.capLd
  simp only [Option.some.injEq, val.Vlong.injEq] at this
  have := lr_nat_inj h0.capLt h.capLt this
  omega

/-- With all four work pairs at capacity 0, no block is a work block. -/
theorem noWork {m : mem}
    (h1 : DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 0 Block.n)
    (h2 : DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 0 Block.n)
    (h3 : DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 0 Block.n)
    (h4 : DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 0 Block.n) (z : block) :
    ¬ IsWork m z := by
  rintro (⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩ | ⟨c, hc, d⟩)
  · exact dyn_zero_ne h1 d hc
  · exact dyn_zero_ne h2 d hc
  · exact dyn_zero_ne h3 d hc
  · exact dyn_zero_ne h4 d hc

/-- The initial partition's cell ends. -/
theorem part_facts {k : Nat} (G : Colored n k) (hn0 : 0 < n) :
    (initialPartition G).2.Pairwise (· < ·) ∧ (∀ e ∈ (initialPartition G).2, e < n) ∧
      n - 1 ∈ (initialPartition G).2 ∧ (initialPartition G).2.length ≤ n := by
  have hEnds := initialPartition_snd_eq G
  refine ⟨by rw [hEnds]; exact endsOf_pairwise _ 0, fun e he => ?_, ?_, ?_⟩
  · have h1 := endsOf_lt _ 0 e (hEnds ▸ he)
    have h2 := totalOf_classes G
    omega
  · have htotal := totalOf_classes G
    rw [hEnds]
    have hm := endsOf_last_mem ((List.range k).map (colorClass G)) 0 (by omega)
    rw [htotal] at hm
    simpa using hm
  · rw [← bcount_initPtn G]; exact bcount_le _ _ _

/-- Zero bytes read as the `short` 0. -/
theorem decode_short0 :
    Common.Memdata.decode_val .Mint16signed (List.replicate 2 Alloc.zb) = .Vint (ir 0) := rfl

kernel_rfl info_dummyfile :
  Init.info Harness.Block.dummyfile = some ([.Init_space (zOfInt 1)], false, false)

/-- An array's block has a permission at its start. -/
theorem perm0_of_array {m : mem} {c : memory_chunk} {b : block} {v : Nat → val} {N : Nat}
    (h : ArrayAt m c b 0 v N) (hN : 0 < N) : Mem.perm m b (zOfInt 0) .Cur .Nonempty := by
  have hw := h.writable 0 hN
  have : elemOfs c 0 0 = zOfInt 0 := by simp [elemOfs]
  rw [this] at hw
  exact Mem.perm_implies _ _ _ _ _ _ (hw.1 (zOfInt 0) ⟨by change intOfZ _ ≤ intOfZ _; exact Int.le_refl _,
    by change intOfZ _ < intOfZ _; rw [intOfZ_add]; have := csize_pos c
       simp only [intOfZ_zOfInt]; exact Int.lt_add_of_pos_right _ this⟩) (.perm_any_N _)

/-- A zero-filled `DYNALLSTAT` block as an array of zeros. -/
theorem arr_of_dyn {m : mem} {bp bs : block} {c cap : Nat} {b : block} (hd : DynAt m bp bs c cap b)
    (hz : Zeros m b (c * cap)) (hc : 0 < cap) (chunk : memory_chunk) (hcs : csize chunk = c)
    (ha : intOfZ (Common.Memdata.align_chunk chunk) = c) (v : val)
    (hv : Common.Memdata.decode_val chunk (List.replicate c Alloc.zb) = v) (k : Nat) (hk : k ≤ cap) :
    ArrayAt m chunk b 0 (fun _ => v) k :=
  hz.array (fun ofs h0 h1 => (hd.mal hc).perm ofs (by omega) h1) (by have := hd.small; omega)
    chunk c hcs ha v hv k (Nat.mul_le_mul_left c hk)

/-- `S.blocks` is pairwise distinct when its fifteen data blocks are, and lie apart
from the globals (`userautomproc`'s block is `emit_generator`'s). -/
theorem blocks_pairwise (S : SLoc) (hU : S.bUA = Harness.Block.emitGenerator)
    (h1 : [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC,
      S.bTC].Pairwise (· ≠ ·))
    (h2 : ∀ x ∈ [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC,
      S.bCC, S.bTC], ∀ g : block, posToNat g < 313 → x ≠ g) :
    S.blocks.Pairwise (· ≠ ·) := by
  have hl : S.blocks = [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL,
      S.bFC, S.bCC, S.bTC] ++ (S.blocks.drop 15) := rfl
  have hd : S.blocks.drop 15 = Harness.Block.emitGenerator :: (S.blocks.drop 16) := by
    rw [← hU]; rfl
  have hc : (Harness.Block.emitGenerator :: (S.blocks.drop 16)).Pairwise (· ≠ ·) ∧
      ∀ g ∈ Harness.Block.emitGenerator :: (S.blocks.drop 16), posToNat g < 313 := by
    simp only [SLoc.blocks, List.drop_succ_cons, List.drop_zero]
    decide
  rw [hl, List.pairwise_append, hd]
  exact ⟨h1, hc.1, fun x hx y hy => h2 x hx y (hc.2 y hy)⟩

/-- The globals among the search's blocks. -/
def consts : List block :=
  [Search.Block.getcanon,
   Search.Block.digraph,
   Search.Block.writeautoms,
   Search.Block.domarkers,
   Search.Block.doschreier,
   Search.Block.tcLevel,
   Search.Block.invarproc,
   Search.Block.usernodeproc,
   Search.Block.userlevelproc,
   Search.Block.usercanonproc,
   Search.Block.userautomproc,
   Search.Block.dispatch,
   Search.Block.orbits,
   Search.Block.m,
   Search.Block.n,
   Search.Block.g,
   Search.Block.canong,
   Search.Block.stats,
   Search.Block.gcaFirst,
   Search.Block.gcaCanon,
   Search.Block.noncheaplevel,
   Search.Block.allsamelevel,
   Search.Block.eqlevFirst,
   Search.Block.eqlevCanon,
   Search.Block.compCanon,
   Search.Block.samerows,
   Search.Block.canonlevel,
   Search.Block.stabvertex,
   Search.Block.cosetindex,
   Search.Block.needshortprune,
   Search.Block.tcnode0,
   Search.Block.allocM,
   Search.Block.workspace,
   Search.Block.worktop,
   Search.Block.fmptr,
   Search.Block.killRequest,
   Program.Block.nautyActive,
   Program.Block.nautyActiveSz,
   Program.Block.nautyFixedpts,
   Program.Block.nautyFixedptsSz,
   Program.Block.nautyWorkperm,
   Program.Block.nautyWorkpermSz,
   Program.Block.nautyFirstlab,
   Program.Block.nautyFirstlabSz,
   Program.Block.nautyCanonlab,
   Program.Block.nautyCanonlabSz,
   Program.Block.nautyFirstcode,
   Program.Block.nautyFirstcodeSz,
   Program.Block.nautyCanoncode,
   Program.Block.nautyCanoncodeSz,
   Program.Block.nautyFirsttc,
   Program.Block.nautyFirsttcSz,
   Program.Block.naugraphWorkperm,
   Program.Block.naugraphWorkpermSz,
   Program.Block.naugraphWorkset,
   Program.Block.naugraphWorksetSz,
   Program.Block.naugraphBucket,
   Program.Block.naugraphBucketSz,
   Program.Block.nautilWorkperm,
   Program.Block.nautilWorkpermSz,
   Program.Block.nautyBit,
   Program.Block.naugraphBit,
   Program.Block.nautilBit,
   Program.Block.naugraphBytecount,
   Program.Block.leftbit,
   Search.Block.mininvarlevel,
   Search.Block.maxinvarlevel,
   Search.Block.invararg,
   Program.Block.naugraphDnwork,
   Program.Block.naugraphDnworkSz]

theorem blocks_eq (S : SLoc) : S.blocks = [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF,
    S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] ++ consts := rfl

theorem consts_small : ∀ g ∈ Harness.Block.emitGenerator :: consts, posToNat g < 313 := by decide

/-- A block of `S` is one of its fifteen data blocks or a global. -/
theorem mem_blocks {S : SLoc} (hU : S.bUA = Harness.Block.emitGenerator) {z : block}
    (h : z ∈ S.blocks) : z ∈ [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL,
      S.bCL, S.bFC, S.bCC, S.bTC] ∨ z ∈ Harness.Block.emitGenerator :: consts := by
  rw [blocks_eq, hU, show ∀ l : List block, [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF,
    S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, Harness.Block.emitGenerator] ++ l =
    [S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC,
      S.bTC] ++ (Harness.Block.emitGenerator :: l) from fun _ => rfl, List.mem_append] at h
  exact h

/-- Extending a frame by one more step. -/
theorem fam {m₀ m m' : mem} {X : block → Prop} {G G' : List block} {P : block → Prop}
    (h : Unch m₀ m (fun z => X z ∨ z ∈ G)) (hu : Unch m m' P) (hP : ∀ z, P z → X z ∨ z ∈ G') :
    Unch m₀ m' (fun z => X z ∨ z ∈ G ++ G') :=
  (h.mono fun _ hz => hz.elim .inl fun h => .inr (List.mem_append_left _ h)).trans
    (hu.mono fun z hz => (hP z hz).elim .inl fun h => .inr (List.mem_append_right _ h))

/-- The globals of nauty.c's nine `DYNALLOC1`s. -/
def allocG : List block :=
  [Block.nautyDefltworkSz, Block.nautyDefltwork, Block.nautyFixedptsSz, Block.nautyFixedpts,
   Block.nautyActiveSz, Block.nautyActive, Block.nautyWorkpermSz, Block.nautyWorkperm,
   Block.nautyFirstlabSz, Block.nautyFirstlab, Block.nautyCanonlabSz, Block.nautyCanonlab,
   Block.nautyFirstcodeSz, Block.nautyFirstcode, Block.nautyCanoncodeSz, Block.nautyCanoncode,
   Block.nautyFirsttcSz, Block.nautyFirsttc]

theorem allocDs_globals (M n : Nat) : Alloc.DynD.globals (allocDs M n) = allocG := rfl

set_option hygiene false in
/-- `¬ (¬ valid z ∨ z ∈ G)` and similar side conditions, for a block `z` that is a
global (below 313) or one of the blocks of the lists `P0`/`P` (pairwise distinct,
`hP0`/`hP`, and apart from the globals, `hPg0`/`hPg`). -/
macro "nb" : tactic => `(tactic| (
  (try dsimp only [S]) <;>
  (try simp only [_root_.not_or, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
    Classical.not_not, List.not_mem_nil, not_false_eq_true, and_true, true_and, allocG, optTargets,
    List.map_cons, List.map_nil, false_or, or_false]) <;>
  (repeat' (apply And.intro)) <;>
  first
  | decide
  | assumption
  | (apply valid_init hm0; decide)
  | (apply hv01; apply valid_init hm0; decide)
  | (apply hvb; simp; done)
  | (apply hv03; apply valid_init hm0; decide)
  | (apply hv13; apply hvb; simp; done)
  | (apply hPg0 <;> first | (simp; done) | decide)
  | (apply Ne.symm; apply hPg0 <;> first | (simp; done) | decide)
  | (apply hPg <;> first | (simp; done) | decide)
  | (apply Ne.symm; apply hPg <;> first | (simp; done) | decide)
  | sep_ne hP0
  | sep_ne hP))

/-- `¬ (z = options ∨ z = dnwork ∨ z = dnworkSz ∨ ¬ valid m₀ z)` for a global `z`. -/
macro "nG " hm:term : tactic =>
  `(tactic| exact fun h => by
    rcases h with h | h | h | h
    all_goals first | exact absurd h (by decide) | exact h (valid_init $hm (by decide)))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem nauty_satisfies {k : Nat} (G : Colored n k) (gens : List (Array Nat))
    (Em : Bool → Nat → Nat → Search n → List Int)
    (hOff : EmLawOff Em ⟨rowsOf G⟩) (hFirst : EmLawFirst Em ⟨rowsOf G⟩)
    (hEm : Em true 1 (initialPartition G).2.length
      (SearchInf.initialC n (initialPartition G).1 (initialPartition G).2) = gensWords gens n)
    (hAut : AutomCb xi Harness.Block.emitGenerator)
    (bg bl bp bo bst bc : block) (capD : Nat) (bD : block) :
    Satisfies xi ge (.Internal dense.fn.nauty) (nautySpec G gens bg bl bp bo bst bc capD bD) := by
  refine satisfies_internal (Entry := fun _ m e le m₁ => ∃ bI, e = nEnv bI ∧
    le = nTemps bg bl bp bo bst bD bc (2 * 500 * Harness.wordsOf n) (Harness.wordsOf n) n ∧
    ¬ Mem.valid_block m bI ∧ Mem.valid_access m₁ .Mint32 bI (zOfInt 0) .Freeable ∧
    Unch m m₁ (fun z => ¬ Mem.valid_block m z) ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m₁ z))
    ?_ ?_
  · rintro args m ⟨rfl, -⟩
    obtain ⟨e, le, m₁, hfe, bI, he, hle, h⟩ := nauty_entry bg bl bp bo bst bD bc
      (2 * 500 * Harness.wordsOf n) (Harness.wordsOf n) n m
    exact ⟨e, le, m₁, hfe, bI, he, hle, h⟩
  rintro args mE ⟨rfl, ⟨m₀, hm0, hu0, hgrow0, hfresh, hbD0, hbDn⟩, hDW, hcapD, hZD, hopt,
    ⟨gw, hg⟩, hlab, hptn, ⟨ov, hob⟩, ⟨cw0, hcg⟩, hstR, hpw, hn0, hnmax⟩
  rw [triple_iff_wp]
  rintro e le m1 ⟨bI, rfl, rfl, hbI, hfI, hu1, hg1⟩
  rw [dense.fn.nauty.fn_body_eq, Nauty.body_eq]
  -- sizes
  have hn6 : n ≤ 65536 := hnmax
  have hM0 : 0 < Harness.wordsOf n := by simp only [Harness.wordsOf, Statement.setwordsNeeded]; omega
  have hMl : Harness.wordsOf n ≤ 1024 := by
    simp only [Harness.wordsOf, Statement.setwordsNeeded]; omega
  have hnM : n ≤ 64 * Harness.wordsOf n := by
    simp only [Harness.wordsOf, Statement.setwordsNeeded]; omega
  let nT := nTemps bg bl bp bo bst bD bc (2 * 500 * Harness.wordsOf n) (Harness.wordsOf n) n
  let pars : List ident := [dense.id.g_arg, dense.id.lab, dense.id.ptn, dense.id.active_arg,
    dense.id.orbits_arg, dense.id.options, dense.id.stats_arg, dense.id.ws_arg, dense.id.worksize,
    dense.id.m_arg, dense.id.n_arg, dense.id.canong_arg]
  have hmA : PTree.get dense.id.m_arg nT = some (.Vint (ir (Harness.wordsOf n))) := by
    simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss]
  have hnA : PTree.get dense.id.n_arg nT = some (.Vint (ir n)) := by
    simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss]
  -- the frame from the initial memory to the entry
  have U01 : Unch m₀ m1 (fun z => z = Harness.Block.options ∨ z = Block.naugraphDnwork ∨
      z = Block.naugraphDnworkSz ∨ ¬ Mem.valid_block m₀ z) :=
    hu0.trans (hu1.mono fun z hz => .inr (.inr (.inr fun h => hz (hgrow0 _ h))))
  have hv01 : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m1 z := fun z h => hg1 _ (hgrow0 _ h)
  have hT : ∀ x v, PTree.get x (nTemps bg bl bp bo bst bD bc (2 * 500 * Harness.wordsOf n)
      (Harness.wordsOf n) n) = some v → PTree.get x (nTemps bg bl bp bo bst bD bc
      (2 * 500 * Harness.wordsOf n) (Harness.wordsOf n) n) = some v := fun _ _ h => h
  -- head: the dispatch copy
  have hdgr : Mem.range_perm m1 Harness.Block.dispatchGraph (zOfInt 0) (zOfInt 88) .Cur .Readable := by
    have h := globWritable hm0 info_dispatchGraphInit
    rw [show init_data_list_size dispatchGraphInit = zOfInt 88 from rfl] at h
    intro o ho
    exact Mem.perm_implies _ _ _ _ _ _ ((rperm_unch U01 (by nG hm0) h) o ho) (.perm_W_R)
  refine wp_head (M := Harness.wordsOf n)
    (by simp (config := {decide := true}) only [nTemps, temps_gso, temps_gss])
    (OptionsAt.unch hopt hu1 (fun h => h (hgrow0 _ (valid_init hm0 (by decide)))))
    (fun i hi => by rw [U01.load _ _ _ (by nG hm0)]; exact dispatchGraph_load hm0 i hi) hdgr
    (dispatchGraph_vp hm0 U01 (by nG hm0))
    (rperm_unch U01 (by nG hm0) (dispatch_writable hm0))
    (fun b hb => by
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · exact (Keep.unch U01 (by nG hm0)).perm _ _ (fnPerm hm0 Refine.funct_refine)
      · exact (Keep.unch U01 (by nG hm0)).perm _ _ (fnPerm hm0 Refine.funct_refine1)
      · exact (Keep.unch U01 (by nG hm0)).perm _ _ (fnPerm hm0 Search.funct_updatecanFn)
      · exact (Keep.unch U01 (by nG hm0)).perm _ _ (fnPerm hm0 Search.funct_targetcellFn)
      · exact (Keep.unch U01 (by nG hm0)).perm _ _ (fnPerm hm0 Search.funct_cheapautomFn))
    (by simp (config := {decide := true}) only [nTemps, temps_gso, temps_gss])
    (by omega) ?_
  intro le2 m2 hD2 hu2 hg2 hle2
  have hL2 : ∀ x ∈ pars, PTree.get x le2 = PTree.get x nT := fun x hx =>
    hle2 x (by rintro rfl; revert hx; decide) (by rintro rfl; revert hx; decide)
      (by rintro rfl; revert hx; decide) (by rintro rfl; revert hx; decide)
  -- sizes
  refine wp_tSizes (M := Harness.wordsOf n) (n := n)
    (by rw [hL2 _ (by decide)]; exact hT _ _ hmA) (by rw [hL2 _ (by decide)]; exact hT _ _ hnA)
    hn0 (by omega) hnM (by omega) ?_
  intro le3 hle3
  have hL3 : ∀ x ∈ pars, PTree.get x le3 = PTree.get x nT := fun x hx => by
    rw [hle3 x (by rintro rfl; revert hx; decide), hL2 x hx]
  -- the blocks of the arguments, the workspace and `initstatus`
  have hcD : 0 < capD := by omega
  have hvD : Mem.valid_block mE bD :=
    Mem.perm_valid_block _ _ (zOfInt 0) .Cur .Freeable ((hDW.mal hcD).perm 0 (by decide) (by omega))
  have hvA : ∀ x ∈ [bg, bl, bp, bo, bst, bc], Mem.valid_block mE x := fun x hx => (hfresh x hx).2
  have hP0 : [bg, bl, bp, bo, bst, bc, bD, bI].Pairwise (· ≠ ·) := by
    have hbI : ∀ x ∈ [bg, bl, bp, bo, bst, bc, bD], x ≠ bI := by
      intro x hx he; subst he
      rcases List.mem_cons.1 hx with h | h
      · exact hbI (h ▸ hvA _ (by simp))
      rcases List.mem_cons.1 h with h | h
      · exact hbI (h ▸ hvA _ (by simp))
      rcases List.mem_cons.1 h with h | h
      · exact hbI (h ▸ hvA _ (by simp))
      rcases List.mem_cons.1 h with h | h
      · exact hbI (h ▸ hvA _ (by simp))
      rcases List.mem_cons.1 h with h | h
      · exact hbI (h ▸ hvA _ (by simp))
      rcases List.mem_cons.1 h with h | h
      · exact hbI (h ▸ hvA _ (by simp))
      rcases List.mem_cons.1 h with h | h
      · exact hbI (h ▸ hvD)
      · simp at h
    have hbD : ∀ x ∈ [bg, bl, bp, bo, bst, bc], x ≠ bD := fun x hx he => hbDn (he ▸ hx)
    have hl : [bg, bl, bp, bo, bst, bc, bD, bI] = [bg, bl, bp, bo, bst, bc] ++ [bD, bI] := rfl
    rw [hl, List.pairwise_append]
    refine ⟨hpw, by simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil,
      and_true, List.not_mem_nil, false_implies, implies_true]; exact hbI _ (by simp), ?_⟩
    intro x hx y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · exact hbD x hx
    · refine hbI x ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h <;> simp [h]
  have hPg0 : ∀ x ∈ [bg, bl, bp, bo, bst, bc, bD, bI], ∀ g : block, posToNat g < 313 → x ≠ g := by
    intro x hx g hg he
    have hv := valid_init hm0 hg
    rw [← he] at hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h] at hv
    · exact (hfresh bg (by simp)).1 hv
    · exact (hfresh bl (by simp)).1 hv
    · exact (hfresh bp (by simp)).1 hv
    · exact (hfresh bo (by simp)).1 hv
    · exact (hfresh bst (by simp)).1 hv
    · exact (hfresh bc (by simp)).1 hv
    · exact hbD0 hv
    · exact hbI (hgrow0 _ hv)
  have hvb : ∀ x ∈ [bg, bl, bp, bo, bst, bc, bD, bI], Mem.valid_block m1 x := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h]
    · exact hg1 _ (hvA bg (by simp))
    · exact hg1 _ (hvA bl (by simp))
    · exact hg1 _ (hvA bp (by simp))
    · exact hg1 _ (hvA bo (by simp))
    · exact hg1 _ (hvA bst (by simp))
    · exact hg1 _ (hvA bc (by simp))
    · exact hg1 _ hvD
    · exact Alloc.valid_of_access hfI
  -- the frames: `A` from the initial memory (globals), `B` from the entry
  have A1 : Unch m₀ m1 (fun z => ¬ Mem.valid_block m₀ z ∨
      z ∈ [Harness.Block.options, Block.naugraphDnwork, Block.naugraphDnworkSz]) :=
    U01.mono fun z hz => by
      rcases hz with h | h | h | h
      · exact .inr (by simp [h])
      · exact .inr (by simp [h])
      · exact .inr (by simp [h])
      · exact .inl h
  have B1 : Unch m1 m1 (fun z => ¬ Mem.valid_block m1 z ∨ z ∈ ([] : List block)) := Unch.refl _ _
  have A2 := fam (G' := [Search.Block.dispatch]) A1 hu2 (fun z h => .inr (by simp [h]))
  have B2 := fam (G' := [Search.Block.dispatch]) B1 hu2 (fun z h => .inr (by simp [h]))
  -- main: `m`, `n` and the checks
  refine wp_tMain (M := Harness.wordsOf n) (n := n)
    (by rw [hle3 _ (by decide), hL2 _ (by decide)]; exact hT _ _ hmA)
    (by rw [hle3 _ (by decide), hL2 _ (by decide)]; exact hT _ _ hnA) (by omega) (by omega)
    ((int0_init hm0 (by decide)).writable |> A2.access _ _ _ _ (by nb))
    ((int0_init hm0 (by decide)).writable |> A2.access _ _ _ _ (by nb)) hD2
    ((Keep.unch A2 (by nb)).perm _ _ (fnPerm hm0 funct_naugraphCheck)) ?_
  intro m3 hMm3 hNn3 hu3 hg3
  have A3 := fam (G' := [Search.Block.m, Search.Block.n]) A2 hu3
    (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have B3 := fam (G' := [Search.Block.m, Search.Block.n]) B2 hu3
    (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have hv03 : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m3 z := fun z h => hg3 _ (hg2 _ (hv01 _ h))
  have hv13 : ∀ z, Mem.valid_block m1 z → Mem.valid_block m3 z := fun z h => hg3 _ (hg2 _ h)
  -- the nine allocations
  have hgl := Init.globals hm0
  refine wp_tAlloc (M := Harness.wordsOf n) (n := n) hMm3 hNn3 hM0 hn0 (by omega) (by omega) ?_ ?_
  · intro d hd b
    simp only [allocDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hgl.nautyDefltwork _ b).keep A3 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
    · exact (hgl.nautyFixedpts _ b).keep A3 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
    · exact (hgl.nautyActive _ b).keep A3 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
    · exact (hgl.nautyWorkperm _ b).keep A3 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
    · exact (hgl.nautyFirstlab _ b).keep A3 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
    · exact (hgl.nautyCanonlab _ b).keep A3 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
    · exact (hgl.nautyFirstcode _ b).keep A3 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
    · exact (hgl.nautyCanoncode _ b).keep A3 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
    · exact (hgl.nautyFirsttc _ b).keep A3 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
  intro le4 m4 cb hcb hdist hu4 hg4 hle4
  simp only [allocDs_globals] at hu4
  have A4 := fam (G' := allocG) A3 hu4
    (fun z h => h.elim .inr fun h => .inl fun hv => h (hv03 _ hv))
  have B4 := fam (G' := allocG) B3 hu4
    (fun z h => h.elim .inr fun h => .inl fun hv => h (hv13 _ hv))
  have hv04 : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m4 z := fun z h => hg4 _ (hv03 _ h)
  have hv14 : ∀ z, Mem.valid_block m1 z → Mem.valid_block m4 z := fun z h => hg4 _ (hv13 _ h)
  obtain ⟨d0, c0, f0, z0⟩ := hcb 0 (by simp [allocDs])
  obtain ⟨d1, c1, f1, z1⟩ := hcb 1 (by simp [allocDs])
  obtain ⟨d2, c2, f2, z2⟩ := hcb 2 (by simp [allocDs])
  obtain ⟨d3, c3, f3, z3⟩ := hcb 3 (by simp [allocDs])
  obtain ⟨d4, c4, f4, z4⟩ := hcb 4 (by simp [allocDs])
  obtain ⟨d5, c5, f5, z5⟩ := hcb 5 (by simp [allocDs])
  obtain ⟨d6, c6, f6, z6⟩ := hcb 6 (by simp [allocDs])
  obtain ⟨d7, c7, f7, z7⟩ := hcb 7 (by simp [allocDs])
  obtain ⟨d8, c8, f8, z8⟩ := hcb 8 (by simp [allocDs])
  simp only [allocDs, List.getElem_cons_zero, List.getElem_cons_succ] at d0 c0 z0 d1 c1 z1 d2 c2 z2 d3 c3 z3 d4 c4 z4 d5 c5 z5 d6 c6 z6 d7 c7 z7 d8 c8 z8
  have hfA : ∀ i < 9, ¬ Mem.valid_block m3 (cb i).2 := fun i hi => (hcb i (by simpa [allocDs] using hi)).2.2.1
  have hP : [bg, bl, bp, bo, bst, bc, bD, bI, (cb 0).2, (cb 1).2, (cb 2).2, (cb 3).2, (cb 4).2,
      (cb 5).2, (cb 6).2, (cb 7).2, (cb 8).2].Pairwise (· ≠ ·) := by
    have hl : [bg, bl, bp, bo, bst, bc, bD, bI, (cb 0).2, (cb 1).2, (cb 2).2, (cb 3).2, (cb 4).2,
        (cb 5).2, (cb 6).2, (cb 7).2, (cb 8).2] = [bg, bl, bp, bo, bst, bc, bD, bI] ++
        (List.range 9).map fun i => (cb i).2 := rfl
    rw [hl, List.pairwise_append]
    refine ⟨hP0, ?_, ?_⟩
    · rw [List.pairwise_map]
      refine List.pairwise_lt_range.imp_of_mem fun {i j} hi hj hij => ?_
      exact hdist i j hij (by simpa [allocDs] using List.mem_range.1 hj)
    · intro x hx y hy he
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
      exact hfA i (List.mem_range.1 hi) (he ▸ hv13 _ (hvb x hx))
  have hPg : ∀ x ∈ [bg, bl, bp, bo, bst, bc, bD, bI, (cb 0).2, (cb 1).2, (cb 2).2, (cb 3).2,
      (cb 4).2, (cb 5).2, (cb 6).2, (cb 7).2, (cb 8).2], ∀ g : block, posToNat g < 313 → x ≠ g := by
    intro x hx g hg he
    have hx' : x ∈ [bg, bl, bp, bo, bst, bc, bD, bI] ∨ ∃ i < 9, x = (cb i).2 := by
      have hl : [bg, bl, bp, bo, bst, bc, bD, bI, (cb 0).2, (cb 1).2, (cb 2).2, (cb 3).2, (cb 4).2,
          (cb 5).2, (cb 6).2, (cb 7).2, (cb 8).2] = [bg, bl, bp, bo, bst, bc, bD, bI] ++
          (List.range 9).map fun i => (cb i).2 := rfl
      rw [hl, List.mem_append, List.mem_map] at hx
      rcases hx with h | ⟨i, hi, rfl⟩
      · exact .inl h
      · exact .inr ⟨i, List.mem_range.1 hi, rfl⟩
    rcases hx' with h | ⟨i, hi, rfl⟩
    · exact hPg0 x h g hg he
    · exact hfA i hi (he ▸ hv03 _ (valid_init hm0 hg))
  -- the frames from `m2`, `m3` and `m4`
  have F2 : Unch m2 m4 (fun z => ¬ Mem.valid_block m3 z ∨ z ∈ ([] : List block) ++
      [Search.Block.m, Search.Block.n] ++ allocG) :=
    ((Unch.refl m2 _).mono (fun z h => h)).trans <| (hu3.mono fun z h => .inr (by
      rcases h with rfl | rfl <;> simp)).trans (hu4.mono fun z h => h.elim (fun h => .inr (by simp [h]))
        .inl)
  have F3 : Unch m3 m4 (fun z => ¬ Mem.valid_block m3 z ∨ z ∈ ([] : List block) ++ allocG) :=
    hu4.mono fun z h => h.elim (fun h => .inr (by simp [h])) .inl
  have F4 : Unch m4 m4 (fun z => False ∨ z ∈ ([] : List block)) := Unch.refl _ _
  -- the target-cell list
  have hMm4 := hMm3.unch F3 (by nb)
  have hNn4 := hNn3.unch F3 (by nb)
  refine wp_tTc (M := Harness.wordsOf n) hMm4 hM0 (by omega)
    ((allocM_init hm0).unch U01 (by nG hm0) |>.unch B4 (by nb))
    ((tcnode0_init hm0).unch U01 (by nG hm0) |>.unch B4 (by nb)) ?_
  intro le5 m5 hA5 hT5 hu5 hg5 hle5
  have B5 := fam (G' := [Search.Block.allocM, Search.Block.tcnode0]) B4 hu5
    (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F2 := fam (G' := [Search.Block.allocM, Search.Block.tcnode0]) F2 hu5
    (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F3 := fam (G' := [Search.Block.allocM, Search.Block.tcnode0]) F3 hu5
    (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F4 := fam (G' := [Search.Block.allocM, Search.Block.tcnode0]) F4 hu5
    (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F5 : Unch m5 m5 (fun z => False ∨ z ∈ ([] : List block)) := Unch.refl _ _
  have hL4 : ∀ x ∈ pars, PTree.get x le4 = PTree.get x nT := fun x hx => by
    rw [hle4 x (by
      intro d hd
      simp only [allocDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨fun h => by dsimp only at h; subst h; revert hx; decide,
          fun h => by dsimp only at h; subst h; revert hx; decide⟩), hL3 x hx]
  have hL5 : ∀ x ∈ pars, PTree.get x le5 = PTree.get x nT := fun x hx => by
    rw [hle5 x (by rintro rfl; revert hx; decide), hL4 x hx]
  -- the option copies
  have hW6 : ∀ x ∈ optTargets, Mem.valid_access m5 x.1 x.2 (zOfInt 0) .Writable := by
    intro x hx
    simp only [optTargets, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
    all_goals first
      | exact B5.access _ _ _ _ (by nb) (U01.access _ _ _ _ (by nG hm0)
          (int0_init hm0 (by decide)).writable)
      | exact B5.access _ _ _ _ (by nb) (U01.access _ _ _ _ (by nG hm0)
          (ptr0_init hm0 (by decide)).writable)
  have hdum : Mem.perm m5 Harness.Block.dummyfile (zOfInt 0) .Cur .Nonempty := by
    have h := globWritable hm0 info_dummyfile
    have h0 := h (zOfInt 0) ⟨by change intOfZ _ ≤ intOfZ _; exact Int.le_refl _,
      by change intOfZ _ < intOfZ _; decide⟩
    exact (Keep.unch B5 (by nb)).perm _ _ ((Keep.unch U01 (by nG hm0)).perm _ _
      (Mem.perm_implies _ _ _ _ _ _ h0 (.perm_any_N _)))
  have hMN0 : 0 < Harness.wordsOf n * n := Nat.mul_pos hM0 hn0
  refine wp_tOpts (bo := bo) (bst := bst) (bc := bc)
    (by rw [hL5 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    (by rw [hL5 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    (by rw [hL5 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    (by rw [hL5 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    (OptionsAt.unch (OptionsAt.unch hopt hu1 (fun h => h (hgrow0 _ (valid_init hm0 (by decide)))))
      B5 (by nb))
    hW6 hdum
    ((Keep.unch B5 (by nb)).perm _ _ ((Keep.unch hu1 (fun h => h (hvA bc (by simp)))).perm _ _
      (perm0_of_array hcg hMN0))) ?_
  intro le6 m6 hF6 hu6 hg6 hle6
  have B6 := fam (G' := optTargets.map Prod.snd) B5 hu6 (fun z h => .inr h)
  have F2 := fam (G' := optTargets.map Prod.snd) F2 hu6 (fun z h => .inr h)
  have F3 := fam (G' := optTargets.map Prod.snd) F3 hu6 (fun z h => .inr h)
  have F4 := fam (G' := optTargets.map Prod.snd) F4 hu6 (fun z h => .inr h)
  have F5 := fam (G' := optTargets.map Prod.snd) F5 hu6 (fun z h => .inr h)
  have F6 : Unch m6 m6 (fun z => False ∨ z ∈ ([] : List block)) := Unch.refl _ _
  have hL6 : ∀ x ∈ pars, PTree.get x le6 = PTree.get x nT := fun x hx => by
    rw [hle6 x (by rintro rfl; revert hx; decide) (by rintro rfl; revert hx; decide)
      (by rintro rfl; revert hx; decide), hL5 x hx]
  -- `ptn` and `active`
  obtain ⟨hsort, hlt, hlast, hlen⟩ := part_facts G hn0
  have hc2 : 0 < (cb 2).1 := by omega
  have hc1 : 0 < (cb 1).1 := by omega
  have hA6 : Mem.load .Mint64 m6 Block.nautyActive (zOfInt 0) = some (.Vptr (cb 2).2 Ptrofs.zero) := by
    rw [F4.load _ _ _ (by nb)]; exact d2.ptr hc2
  have haw6 := (arr_of_dyn d2 z2 hc2 .Mint64 rfl rfl _ rfl _ c2).unch F4 (by nb)
  refine wp_tPtn (ends := (initialPartition G).2) hsort hlt hlast hn0 (by omega) hnM hM0 (by omega)
    (by rw [hL6 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    (OptionsAt.unch (OptionsAt.unch hopt hu1 (fun h => h (hgrow0 _ (valid_init hm0 (by decide)))))
      B6 (by nb))
    (by rw [hL6 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    (by rw [hL6 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    ((hptn.unch hu1 (fun h => h (hvA bp (by simp)))).unch B6 (by nb))
    (hNn3.unch F3 (by nb)) (hMm3.unch F3 (by nb)) hA6 haw6
    ((hgl.nautyBit.unch U01 (by nG hm0)).unch B6 (by nb))
    (by
      intro z hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> exact ⟨by nb, by nb⟩)
    (by nb) ?_
  intro le7 m7 harr7 hnc7 hact7 hk7 hu7 hg7 hle7
  have B6 := fam (G' := [bp, (cb 2).2]) B6 hu7 (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F2 := fam (G' := [bp, (cb 2).2]) F2 hu7 (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F3 := fam (G' := [bp, (cb 2).2]) F3 hu7 (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F4 := fam (G' := [bp, (cb 2).2]) F4 hu7 (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F5 := fam (G' := [bp, (cb 2).2]) F5 hu7 (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F6 := fam (G' := [bp, (cb 2).2]) F6 hu7 (fun z h => .inr (by rcases h with rfl | rfl <;> simp))
  have F7 : Unch m7 m7 (fun z => False ∨ z ∈ ([] : List block)) := Unch.refl _ _
  have hL7 : ∀ x ∈ pars, PTree.get x le7 = PTree.get x nT := fun x hx => by
    rw [hle7 x (by rintro rfl; revert hx; decide) (by rintro rfl; revert hx; decide) (by rintro rfl; revert hx; decide) (by rintro rfl; revert hx; decide), hL6 x hx]
  -- `g`, `canong`, `initstatus`
  refine wp_tInit (bg := bg) (bc := bc) (M := Harness.wordsOf n)
    (by rw [hL7 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    (by rw [hL7 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    (fun i hi => (hD2 i hi).unch F2 (by nb))
    (B6.access _ _ _ _ (by nb) (U01.access _ _ _ _ (by nG hm0) (ptr0_init hm0 (by decide)).writable))
    (B6.access _ _ _ _ (by nb) (U01.access _ _ _ _ (by nG hm0) (ptr0_init hm0 (by decide)).writable))
    (B6.access _ _ _ _ (by nb) hfI)
    ((Facts.get hF6 (c := .Mint32) (b := Search.Block.doschreier) (v := .Vint (ir 0))
      (by simp [optFacts])).unch F6 (by nb))
    ⟨by nb, by nb, by nb, by nb⟩ ?_
  intro le8 m8 hgP8 hcP8 hi8 hfi8 hu8 hgv8 hle8
  have B6 := fam (G' := [Search.Block.g, Search.Block.canong, bI]) B6 hu8 (fun z h => .inr (by rcases h with rfl | rfl | rfl <;> simp))
  have F2 := fam (G' := [Search.Block.g, Search.Block.canong, bI]) F2 hu8 (fun z h => .inr (by rcases h with rfl | rfl | rfl <;> simp))
  have F3 := fam (G' := [Search.Block.g, Search.Block.canong, bI]) F3 hu8 (fun z h => .inr (by rcases h with rfl | rfl | rfl <;> simp))
  have F4 := fam (G' := [Search.Block.g, Search.Block.canong, bI]) F4 hu8 (fun z h => .inr (by rcases h with rfl | rfl | rfl <;> simp))
  have F5 := fam (G' := [Search.Block.g, Search.Block.canong, bI]) F5 hu8 (fun z h => .inr (by rcases h with rfl | rfl | rfl <;> simp))
  have F6 := fam (G' := [Search.Block.g, Search.Block.canong, bI]) F6 hu8 (fun z h => .inr (by rcases h with rfl | rfl | rfl <;> simp))
  have F7 := fam (G' := [Search.Block.g, Search.Block.canong, bI]) F7 hu8 (fun z h => .inr (by rcases h with rfl | rfl | rfl <;> simp))
  have F8 : Unch m8 m8 (fun z => False ∨ z ∈ ([] : List block)) := Unch.refl _ _
  have hL8 : ∀ x ∈ pars, PTree.get x le8 = PTree.get x nT := fun x hx => by
    rw [hle8 x (by rintro rfl; revert hx; decide), hL7 x hx]
  -- `orbits`
  refine wp_tOrbits (bo := bo) (n := n) (v := ov) (by omega)
    ((Facts.get hF6 (c := .Mint64) (b := Search.Block.orbits) (v := .Vptr bo Ptrofs.zero)
      (by simp [optFacts])).unch F6 (by nb))
    (hNn3.unch F3 (by nb)) ((hob.unch hu1 (fun h => h (hvA bo (by simp)))).unch B6 (by nb))
    ⟨by nb, by nb⟩ ?_
  intro le9 m9 horb9 hu9 hgv9 hle9
  have B6 := fam (G' := [bo]) B6 hu9 (fun z h => .inr (by rw [h]; simp))
  have F2 := fam (G' := [bo]) F2 hu9 (fun z h => .inr (by rw [h]; simp))
  have F3 := fam (G' := [bo]) F3 hu9 (fun z h => .inr (by rw [h]; simp))
  have F4 := fam (G' := [bo]) F4 hu9 (fun z h => .inr (by rw [h]; simp))
  have F5 := fam (G' := [bo]) F5 hu9 (fun z h => .inr (by rw [h]; simp))
  have F6 := fam (G' := [bo]) F6 hu9 (fun z h => .inr (by rw [h]; simp))
  have F7 := fam (G' := [bo]) F7 hu9 (fun z h => .inr (by rw [h]; simp))
  have F8 := fam (G' := [bo]) F8 hu9 (fun z h => .inr (by rw [h]; simp))
  have F9 : Unch m9 m9 (fun z => False ∨ z ∈ ([] : List block)) := Unch.refl _ _
  have hL9 : ∀ x ∈ pars, PTree.get x le9 = PTree.get x nT := fun x hx => by
    rw [hle9 x (by rintro rfl; revert hx; decide), hL8 x hx]
  -- the search's locations
  let S : SLoc :=
    { bg := bg
      gofs := Ptrofs.zero
      gw := gw
      bl := bl
      lofs := Ptrofs.zero
      bp := bp
      pofs := Ptrofs.zero
      bo := bo
      oofs := Ptrofs.zero
      bst := bst
      sofs := Ptrofs.zero
      bc := bc
      cofs := Ptrofs.zero
      bws := bD
      wofs := Ptrofs.zero
      bA := (cb 2).2
      capA := (cb 2).1
      bF := (cb 1).2
      capF := (cb 1).1
      bWP := (cb 3).2
      capWP := (cb 3).1
      bFL := (cb 4).2
      capFL := (cb 4).1
      bCL := (cb 5).2
      capCL := (cb 5).1
      bFC := (cb 6).2
      capFC := (cb 6).1
      bCC := (cb 7).2
      capCC := (cb 7).1
      bTC := (cb 8).2
      capTC := (cb 8).1
      bUA := Harness.Block.emitGenerator
      M := Harness.wordsOf n
      capD := capD }
  have hsb : S.sb = 0 := rfl
  have hR9 : Mem.range_perm m9 bst (zOfInt 0) (zOfInt 88) .Cur .Freeable :=
    rperm_unch B6 (by nb) (rperm_unch hu1 (fun h => h (hvA bst (by simp))) hstR)
  have hst9 : PtrAt m9 Search.Block.stats (.Vptr S.bst S.sofs) :=
    (Facts.get hF6 (c := .Mint64) (b := Search.Block.stats) (v := .Vptr bst Ptrofs.zero)
      (by simp [optFacts])).unch F6 (by nb)
  -- the statistics and `fixedpts`
  refine wp_tStats (S := S) (n := n) (M := Harness.wordsOf n) (bF := (cb 1).2) rfl hst9 hR9 (by omega)
    (hNn3.unch F3 (by nb)) (hMm3.unch F3 (by nb)) hM0 (by omega)
    (by rw [F4.load _ _ _ (by nb)]; exact d1.ptr hc1)
    ((arr_of_dyn d1 z1 hc1 .Mint64 rfl rfl _ rfl _ c1).unch F4 (by nb))
    (B6.access _ _ _ _ (by nb) (U01.access _ _ _ _ (by nG hm0) (int0_init hm0 (by decide)).writable))
    (B6.access _ _ _ _ (by nb) (U01.access _ _ _ _ (by nG hm0) (int0_init hm0 (by decide)).writable))
    ⟨by nb, by nb, by nb, by nb, by nb, by nb, by nb⟩ ⟨by nb, by nb, by nb, by nb⟩ ?_
  intro le10 m10 s0 s8 s12 s16 s24 s32 s40 s48 s56 hfw10 hnc10 hel10 hacc10 hkF10 hu10 hgv10 hle10
  have B6 := fam (G' := [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon]) B6 hu10 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl <;> simp))
  have F2 := fam (G' := [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon]) F2 hu10 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl <;> simp))
  have F3 := fam (G' := [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon]) F3 hu10 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl <;> simp))
  have F4 := fam (G' := [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon]) F4 hu10 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl <;> simp))
  have F5 := fam (G' := [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon]) F5 hu10 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl <;> simp))
  have F6 := fam (G' := [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon]) F6 hu10 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl <;> simp))
  have F7 := fam (G' := [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon]) F7 hu10 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl <;> simp))
  have F8 := fam (G' := [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon]) F8 hu10 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl <;> simp))
  have F9 := fam (G' := [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon]) F9 hu10 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl <;> simp))
  have F10 : Unch m10 m10 (fun z => False ∨ z ∈ ([] : List block)) := Unch.refl _ _
  have hL10 : ∀ x ∈ pars, PTree.get x le10 = PTree.get x nT := fun x hx => by
    rw [hle10 x (by rintro rfl; revert hx; decide) (by rintro rfl; revert hx; decide), hL9 x hx]
  -- the workspace
  refine wp_tWork (S := S) (M := Harness.wordsOf n) (bD := bD) rfl
    (by rw [hL10 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    (by rw [hL10 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss])
    hM0 (by omega) (hMm3.unch F3 (by nb)) (hst9.unch hu10 (by nb))
    (hacc10 _ _ _ (va88 hR9 .Mint32 20 (by decide) (by decide) ⟨zOfInt 5, rfl⟩))
    (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with h|h|h|h|h|h|h <;> subst h
      all_goals first
        | exact B6.access _ _ _ _ (by nb) (U01.access _ _ _ _ (by nG hm0)
            (int0_init hm0 (by decide)).writable)
        | exact B6.access _ _ _ _ (by nb) (U01.access _ _ _ _ (by nG hm0)
            (ptr0_init hm0 (by decide)).writable))
    ⟨by nb, by nb, by nb, by nb, by nb, by nb, by nb, by nb, by nb⟩ ?_
  intro le11 m11 hws11 hwt11 hfm11 herr11 hnsp11 hisl11 hiss11 hiap11 hacc11 hfk11 hu11 hgv11 hle11
  have B6 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) B6 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F2 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) F2 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F3 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) F3 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F4 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) F4 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F5 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) F5 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F6 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) F6 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F7 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) F7 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F8 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) F8 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F9 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) F9 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F10 := fam (G' := [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses, Search.Block.invapplics]) F10 hu11 (fun z h => .inr (by rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have F11 : Unch m11 m11 (fun z => False ∨ z ∈ ([] : List block)) := Unch.refl _ _
  have hL11 : ∀ x ∈ pars, PTree.get x le11 = PTree.get x nT := fun x hx => by
    rw [hle11 x (by rintro rfl; revert hx; decide), hL10 x hx]
  -- the root search state
  have hv111 : ∀ z, Mem.valid_block m1 z → Mem.valid_block m11 z := fun z h =>
    hgv11 _ (hgv10 _ (hgv9 _ (hgv8 _ (hg7 _ (hg6 _ (hg5 _ (hv14 _ h)))))))
  have hv411 : ∀ z, Mem.valid_block m4 z → Mem.valid_block m11 z := fun z h =>
    hgv11 _ (hgv10 _ (hgv9 _ (hgv8 _ (hg7 _ (hg6 _ (hg5 _ h))))))
  let st0 := SearchInf.initialC n (initialPartition G).1 (initialPartition G).2
  have hF6' : ∀ {c b v}, (c, b, v) ∈ optFacts bo bst → FieldAt m11 c b 0 v → True := fun _ _ => trivial
  have hopt11 : ∀ {c : memory_chunk} {b : block} {v : val}, (c, b, v) ∈ optFacts bo bst →
      (¬ ((False ∨ b ∈ ([] : List block) ++ [bp, (cb 2).2] ++ [Search.Block.g, Search.Block.canong, bI] ++
        [bo] ++ [bst, (cb 1).2, Search.Block.noncheaplevel, Search.Block.eqlevCanon] ++
        [bst, Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr,
          Search.Block.needshortprune, Search.Block.invarsuclevel, Search.Block.invsuccesses,
          Search.Block.invapplics]))) → FieldAt m11 c b 0 v :=
    fun hm hn => (hF6 _ hm).unch F6 hn
  have hdisp : ∀ (i : Nat) (hi : i < 11), FieldAt m11 .Mint64 Search.Block.dispatch (8 * (i : Int))
      ((dispatchOf (Harness.wordsOf n))[i]'(by rw [dispatchOf_length]; exact hi)) :=
    fun i hi => (hD2 i hi).unch F2 (by nb)
  have hfix : Fixed n m11 S := by
    obtain ⟨d0', d1', d2', d3', d4', d5', d6', d7', d8', d9', d10'⟩ :=
      (⟨hdisp 0 (by decide), hdisp 1 (by decide), hdisp 2 (by decide), hdisp 3 (by decide),
        hdisp 4 (by decide), hdisp 5 (by decide), hdisp 6 (by decide), hdisp 7 (by decide),
        hdisp 8 (by decide), hdisp 9 (by decide), hdisp 10 (by decide)⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    simp only [dispatchOf, dispatchVals, List.set_cons_succ, List.set_cons_zero,
      List.getElem_cons_zero, List.getElem_cons_succ] at d0' d1' d2' d3' d4' d5' d6' d7' d8' d9' d10'
    exact
    { g := hgP8.unch F8 (by nb)
      canong := hcP8.unch F8 (by nb)
      orbits := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      stats := hst9.unch F9 (by nb)
      workspace := hws11
      worktop := hwt11
      mm := hMm3.unch F3 (by nb)
      nn := hNn3.unch F3 (by nb)
      getcanon := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      digraph := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      writeautoms := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      domarkers := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      doschreier := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      tcLevel := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      invarproc := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      usernodeproc := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      userlevelproc := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      usercanonproc := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      userautomproc := hopt11 (by (try dsimp only [S]); simp [optFacts]) (by nb)
      dIsautom := d0'
      dTestcanlab := d1'
      dUpdatecan := d2'
      dRefine := by
        have e : (if Harness.wordsOf n = 1 then val.Vptr Refine.Block.refine1 Ptrofs.zero
            else val.Vptr Refine.Block.refine Ptrofs.zero) = .Vptr S.refineBlock Ptrofs.zero := by
          show _ = val.Vptr (if Harness.wordsOf n = 1 then _ else _) Ptrofs.zero
          split <;> rfl
        rw [← e]; exact d3'
      dRefine1 := d4'
      dCheapautom := d5'
      dTargetcell := d6'
      kill := B6.access _ _ _ _ (by nb) (U01.access _ _ _ _ (by nG hm0) (kill_init hm0))
      allocM := hA5.unch F5 (by nb)
      mininv := ⟨ir 0, hopt11 (v := .Vint (ir 0)) (by simp [optFacts]) (by nb)⟩
      maxinv := ⟨ir 1, hopt11 (v := .Vint (ir 1)) (by simp [optFacts]) (by nb)⟩
      invarg := ⟨ir 0, hopt11 (v := .Vint (ir 0)) (by simp [optFacts]) (by nb)⟩
      dFreedyn := d7'
      dCleanup := d10' }
  have hsc : Scalars m11 st0 false :=
    { gcaFirst := ((int0_init hm0 (by decide)).unch U01 (by nG hm0)).unch B6 (by nb)
      gcaCanon := ((int0_init hm0 (by decide)).unch U01 (by nG hm0)).unch B6 (by nb)
      noncheaplevel := hnc10.unch F10 (by nb)
      allsamelevel := ((int0_init hm0 (by decide)).unch U01 (by nG hm0)).unch B6 (by nb)
      eqlevFirst := ((int0_init hm0 (by decide)).unch U01 (by nG hm0)).unch B6 (by nb)
      eqlevCanon := hel10.unch F10 (by nb)
      compCanon := ((int0_init hm0 (by decide)).unch U01 (by nG hm0)).unch B6 (by nb)
      samerows := ((int0_init hm0 (by decide)).unch U01 (by nG hm0)).unch B6 (by nb)
      canonlevel := ((int0_init hm0 (by decide)).unch U01 (by nG hm0)).unch B6 (by nb)
      stabvertex := ((int0_init hm0 (by decide)).unch U01 (by nG hm0)).unch B6 (by nb)
      cosetindex := ((int0_init hm0 (by decide)).unch U01 (by nG hm0)).unch B6 (by nb)
      needshortprune := hnsp11 }
  have hfk : ∀ {c : memory_chunk} {o : Int} {v : val}, o + csize c ≤ 20 ∨ 24 ≤ o →
      FieldAt m10 c bst o v → FieldAt m11 c bst o v := fun ho h => hfk11 _ _ _ ho h
  have hsb' : ∀ k : Int, S.sb + k = k := fun k => by rw [hsb, Int.zero_add]
  rw [hsb'] at s8 s12 s16 s24 s32 s48 s56
  have s0' : ∃ x, FieldAt m10 .Mfloat64 bst 0 (.Vfloat x) := ⟨_, by rw [← hsb]; exact s0⟩
  have hstats : Stats m11 S st0 true :=
    { numorbits := hfk (o := 12) (by decide) s12
      numgenerators := hfk (o := 16) (by decide) s16
      numnodes := hfk (o := 24) (by decide) s24
      numbadleaves := hfk (o := 32) (by decide) s32
      maxlevel := fun h => absurd h (by decide)
      maxlevelW := hacc11 _ _ _ s40
      tctotal := hfk (o := 48) (by decide) s48
      canupdates := hfk (o := 56) (by decide) s56
      fits := by rw [hsb]; decide
      perm := rperm_acc hacc11 (rperm_acc hacc10 hR9)
      errstatus := herr11
      grpsize1 := let ⟨x, hx⟩ := s0'; ⟨x, hfk (o := 0) (by decide) hx⟩
      grpsize2 := ⟨_, hfk (o := 8) (by decide) s8⟩ }
  have c3p : 0 < (cb 3).1 := by omega
  have c4p : 0 < (cb 4).1 := by omega
  have c5p : 0 < (cb 5).1 := by omega
  have c6p : 0 < (cb 6).1 := by omega
  have c7p : 0 < (cb 7).1 := by omega
  have c8p : 0 < (cb 8).1 := by omega
  have hrep : ∀ {k : Nat} {i : Nat}, i < k → (Array.replicate k (0 : Nat))[i]! = 0 := fun hi => by
    rw [getElem!_pos _ _ (by simpa using hi)]; simp
  have hrepZ : ∀ {k : Nat} {i : Nat}, i < k → (Array.replicate k (0 : Int))[i]! = 0 := fun hi => by
    rw [getElem!_pos _ _ (by simpa using hi)]; simp
  have harrs : Arrays m11 S ⟨rowsOf G⟩ st0 :=
    { lab := (hlab.unch hu1 (fun h => h (hvA bl (by simp)))).unch B6 (by nb)
      ptn := harr7.unch F7 (by nb)
      orbits := horb9.unch F9 (by nb)
      active := let ⟨aw, ha, hr⟩ := hact7; ⟨aw, ha.unch F7 (by nb), hr⟩
      fixedpts := ⟨fun _ => lr 0, hfw10.unch F10 (by nb), Set.setRep_zero hnM⟩
      workperm := ⟨_, (arr_of_dyn d3 z3 c3p .Mint32 rfl rfl _ rfl n c3).unch F4 (by nb)⟩
      firstlab := ((arr_of_dyn d4 z4 c4p .Mint32 rfl rfl _ rfl n c4).unch F4 (by nb)).congr
        fun i hi => by simp only [ints, st0, SearchInf.initialC, initial]; rw [hrep hi]; rfl
      canonlab := ((arr_of_dyn d5 z5 c5p .Mint32 rfl rfl _ rfl n c5).unch F4 (by nb)).congr
        fun i hi => by simp only [ints, st0, SearchInf.initialC, initial]; rw [hrep hi]; rfl
      firstcode := ((arr_of_dyn d6 z6 c6p .Mint16signed rfl rfl _ decode_short0 (n + 2) c6).unch F4
        (by nb)).congr fun i hi => by simp only [shorts, st0, SearchInf.initialC, initial]; rw [hrep hi]; rfl
      canoncode := ((arr_of_dyn d7 z7 c7p .Mint16signed rfl rfl _ decode_short0 (n + 2) c7).unch F4
        (by nb)).congr fun i hi => by simp only [shorts, st0, SearchInf.initialC, initial]; rw [hrep hi]; rfl
      firsttc := ((arr_of_dyn d8 z8 c8p .Mint32 rfl rfl _ rfl (n + 2) c8).unch F4 (by nb)).congr
        fun i hi => by simp only [intsZ, st0, SearchInf.initialC]; rw [hrepZ hi]; rfl
      canong := ⟨⟨cw0, (hcg.unch hu1 (fun h => h (hvA bc (by simp)))).unch B6 (by nb),
        fun v hv => absurd hv (Nat.not_lt_zero _)⟩⟩
      autos := ⟨by simp [st0, SearchInf.initialC, initial], ⟨fun _ => lr 0,
        ((arr_of_dyn hDW hZD hcD .Mint64 rfl rfl _ rfl _ hcapD).unch hu1 (fun h => h hvD)).unch B6 (by nb),
        fun i hi => absurd hi (by simp [st0, SearchInf.initialC, initial])⟩, hfm11⟩
      graph := ⟨(hg.arr.unch hu1 (fun h => h (hvA bg (by simp)))).unch B6 (by nb), hg.rep⟩ }
  have hdyns : Dyns n m11 S :=
    { active := d2.keep F4 (by nb) (by nb) (fun _ => ((((((Keep.unch hu5 (by nb)).trans (Keep.unch hu6 (by nb))).trans (hk7)).trans (Keep.unch hu8 (by nb))).trans (Keep.unch hu9 (by nb))).trans (Keep.unch hu10 (by nb))).trans (Keep.unch hu11 (by nb)))
      fixedpts := d1.keep F4 (by nb) (by nb) (fun _ => ((((((Keep.unch hu5 (by nb)).trans (Keep.unch hu6 (by nb))).trans (Keep.unch hu7 (by nb))).trans (Keep.unch hu8 (by nb))).trans (Keep.unch hu9 (by nb))).trans (hkF10)).trans (Keep.unch hu11 (by nb)))
      workperm := d3.keep F4 (by nb) (by nb) (fun _ => Keep.unch F4 (by nb))
      firstlab := d4.keep F4 (by nb) (by nb) (fun _ => Keep.unch F4 (by nb))
      canonlab := d5.keep F4 (by nb) (by nb) (fun _ => Keep.unch F4 (by nb))
      firstcode := d6.keep F4 (by nb) (by nb) (fun _ => Keep.unch F4 (by nb))
      canoncode := d7.keep F4 (by nb) (by nb) (fun _ => Keep.unch F4 (by nb))
      firsttc := d8.keep F4 (by nb) (by nb) (fun _ => Keep.unch F4 (by nb))
      capA := c2
      capF := c1
      capWP := c3
      capFL := c4
      capCL := c5
      capFC := c6
      capCC := c7
      capTC := c8
      workspace := (hDW.keep hu1 (fun h => h (hgrow0 _ (valid_init hm0 (by decide))))
          (fun h => h (hgrow0 _ (valid_init hm0 (by decide)))) (fun _ => Keep.unch hu1 (fun h => h hvD))).keep
        B6 (by nb) (by nb) (fun _ => Keep.unch B6 (by nb))
      capWs := hcapD }
  have hw1 := ((hgl.naugraphWorkperm 4 Search.Block.n).keep U01 (by nG hm0) (by nG hm0) (fun h => absurd h (Nat.lt_irrefl 0))).keep B6 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
  have hw2 := ((hgl.naugraphWorkset 8 Search.Block.n).keep U01 (by nG hm0) (by nG hm0) (fun h => absurd h (Nat.lt_irrefl 0))).keep B6 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
  have hw3 := ((hgl.naugraphBucket 4 Search.Block.n).keep U01 (by nG hm0) (by nG hm0) (fun h => absurd h (Nat.lt_irrefl 0))).keep B6 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
  have hw4 := ((hgl.nautilWorkperm 4 Search.Block.n).keep U01 (by nG hm0) (by nG hm0) (fun h => absurd h (Nat.lt_irrefl 0))).keep B6 (by nb) (by nb) (fun h => absurd h (Nat.lt_irrefl 0))
  have hwork : WorkAt n m11 S S.blocks :=
    ⟨⟨0, Search.Block.n, 0, Search.Block.n, 0, Search.Block.n, 0, Search.Block.n,
      hw1,
      hw2,
      hw3,
      hw4,
      fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0),
      fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0),
      fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0),
      fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0),
      fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0)⟩⟩
  have htab : Tables m11 := by
    have h0 : Tables m₀ := ⟨hgl.nautyBit, hgl.naugraphBit, hgl.nautilBit, hgl.leftbit, hgl.bytecount⟩
    refine (h0.unch U01 ?_).unch B6 ?_
    · intro z hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> nG hm0
    · intro z hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> nb
  have hdist : S.blocks.Pairwise (· ≠ ·) := by
    refine blocks_pairwise S rfl ?_ ?_
    · -- `S`'s data blocks are `hP`'s list without `bI`, `(cb 0).2` and with
      -- `(cb 1).2`, `(cb 2).2` swapped.
      have hperm : [bg, bl, bp, bo, bst, bc, bD, bI, (cb 0).2, (cb 2).2, (cb 1).2, (cb 3).2,
          (cb 4).2, (cb 5).2, (cb 6).2, (cb 7).2, (cb 8).2].Perm [bg, bl, bp, bo, bst, bc, bD, bI,
          (cb 0).2, (cb 1).2, (cb 2).2, (cb 3).2, (cb 4).2, (cb 5).2, (cb 6).2, (cb 7).2, (cb 8).2] :=
        List.Perm.append_left [bg, bl, bp, bo, bst, bc, bD, bI, (cb 0).2]
          (List.Perm.swap (cb 1).2 (cb 2).2 _)
      have hsub : [bg, bl, bp, bo, bst, bc, bD, (cb 2).2, (cb 1).2, (cb 3).2, (cb 4).2, (cb 5).2,
          (cb 6).2, (cb 7).2, (cb 8).2].Sublist [bg, bl, bp, bo, bst, bc, bD, bI, (cb 0).2, (cb 2).2,
          (cb 1).2, (cb 3).2, (cb 4).2, (cb 5).2, (cb 6).2, (cb 7).2, (cb 8).2] :=
        .cons₂ _ (.cons₂ _ (.cons₂ _ (.cons₂ _ (.cons₂ _ (.cons₂ _ (.cons₂ _
          (.cons _ (.cons _ (List.Sublist.refl _)))))))))
      exact (hperm.symm.nodup_iff.1 hP).sublist hsub
    · intro x hx
      apply hPg
      simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp [h]
  have hS11 : SearchAt m11 S ⟨rowsOf G⟩ st0 true false :=
    ⟨hfix, hsc, hstats, harrs, hdyns, hwork, htab, hdist, SInv.root G hn0 (by omega), hn0,
      by omega, hnM, hM0, show Harness.wordsOf n < 33554432 by omega⟩
  have hnw11 : ∀ z, ¬ IsWork m11 z := noWork hw1 hw2 hw3 hw4
  have hvG : ∀ z : block, posToNat z < 313 → Mem.valid_block m11 z := fun z hz =>
    hv111 _ (hv01 _ (valid_init hm0 hz))
  -- blocks outside `S`
  have hout : ∀ z : block, posToNat z < 313 → z ∉ consts → z ≠ Harness.Block.emitGenerator →
      z ∉ S.blocks := by
    intro z hz h1 h2 hm
    rcases mem_blocks rfl hm with h | h
    · refine hPg z ?_ z hz rfl
      simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
      rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp [h]
    · rcases List.mem_cons.1 h with h | h
      · exact h2 h
      · exact h1 h
  have houtV : ∀ x ∈ [bI, (cb 0).2], x ∉ S.blocks := by
    intro x hx hm
    rcases mem_blocks rfl hm with h | h
    · simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at hx h
      rcases hx with rfl | rfl <;>
        rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> exact absurd h (by sep_ne hP)
    · exact hPg x (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢; rcases hx with h | h <;> simp [h])
        x (consts_small x h) rfl
  -- the node's frame
  have hNF : ∀ z, z ∉ S.blocks → Mem.valid_block m11 z → z ≠ Search.Block.tcnode0 →
      ¬ (S.Chg z ∨ ¬ Mem.valid_block m11 z ∨ IsWork m11 z ∨ z = Search.Block.tcnode0 ∨
        (∃ i p, ([] : List (block × block))[i]? = some p ∧ 1 ≤ i + 2 ∧ z = p.1) ∨
        (∃ i p, ([] : List (block × block))[i]? = some p ∧ 1 ≤ i + 1 ∧ z = p.2)) := by
    rintro z h1 h2 h3 (h | h | h | h | ⟨i, p, h, -⟩ | ⟨i, p, h, -⟩)
    · exact h1 h.1
    · exact h h2
    · exact hnw11 z h
    · exact h3 h
    · simp at h
    · simp at h
  have hvT : Mem.valid_block m11 Search.Block.tcnode0 := hvG _ (by decide)
  have hvU : Mem.valid_block m11 Harness.Block.emitGenerator := hvG _ (by decide)
  have hpU : Mem.perm m11 Harness.Block.emitGenerator (zOfInt 0) .Cur .Nonempty :=
    (Keep.unch B6 (by nb)).perm _ _ ((Keep.unch U01 (by nG hm0)).perm _ _
      (fnPerm hm0 funct_emitGenerator))
  -- the root call
  refine wp_tRoot (NodeOk := SearchInf.NodeOk G) (Em := Em) (S := S) (ctx := ⟨rowsOf G⟩) (st := st0)
    (nc := (initialPartition G).2.length) (root_satisfies G Em hOff hFirst S st0 _ []) hS11
    (hT5.unch F5 (by nb)) ⟨.nil, fun p hp => absurd hp (List.not_mem_nil), fun p hp => absurd hp
      (List.not_mem_nil)⟩ hAut (by omega) hlen (SearchInf.nodeOk_root G hn0) hvU hpU
    (by rw [hL11 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss]; rfl)
    (by rw [hL11 _ (by decide)]; simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss]; rfl)
    (by rw [hle11 _ (by decide), hle10 _ (by decide) (by decide), hle9 _ (by decide),
      hle8 _ (by decide)]; exact hnc7) ?_
  intro t m12 rr hS12 hE12 hC12 hF12 hW12 hU12
  obtain ⟨v, hv, hv1⟩ := exitValue_root hU12
  obtain ⟨chain, hTc12, hTo12, -, hnew12⟩ := hC12
  -- HexGraphIso's run
  have hR : hexNode true ⟨rowsOf G⟩ 1 (initialPartition G).2.length st0 =
      node true ⟨rowsOf G⟩ SearchInf.nautyInfinity 100 (n + 2) 1 (initialPartition G).2.length st0 := rfl
  have hfin := SearchInf.runTraced_inf G hn0 (by show n + 2 < 2000000002; omega)
  rw [← hR] at hfin
  have hrc : runColoredTraced G =
      runTraced n (rowsOf G) (initialPartition G).1 (initialPartition G).2 := rfl
  rw [← hrc] at hfin
  have hcl0 : (hexNode true ⟨rowsOf G⟩ 1 (initialPartition G).2.length st0).2.canonlab =
      (runColored G).canonlab := congrArg (fun T => T.result.canonlab) hfin
  have hsz := canonlab_size G
  have hcl : ∀ i < n, (hexNode true ⟨rowsOf G⟩ 1 (initialPartition G).2.length st0).2.canonlab[i]! < n :=
    fun i hi => by rw [hcl0]; have := cellsReach_lt (canonlab_cellsReach G) i hi; omega
  have hcs : ∀ u < n, ∃ i < n,
      (hexNode true ⟨rowsOf G⟩ 1 (initialPartition G).2.length st0).2.canonlab[i]! = u := by
    intro u hu
    rw [hcl0]
    have hm : u ∈ (runColored G).canonlab.toList :=
      (canonlab_perm_range G).mem_iff.2 (List.mem_range.2 hu)
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
    have hi' : i < n := by simpa [hsz] using hi
    refine ⟨i, hi', ?_⟩
    rw [getElem!_pos _ i (by rw [hsz]; exact hi')]
    simpa using he
  have hiw12 : ∀ z, IsWork m12 z → ¬ Mem.valid_block m11 z := fun z h =>
    (hW12 z h).elim (fun h => absurd h (hnw11 z)) id
  have hvm12 : ∀ z ∈ S.blocks, Mem.valid_block m12 z := fun z hz =>
    hF12.2 _ (hS11.valid_all hvU hvT z hz)
  have hld12 : ∀ z : block, posToNat z < 313 → z ∉ consts → z ≠ Harness.Block.emitGenerator →
      z ≠ Search.Block.tcnode0 → ∀ c o, Mem.load c m12 z o = Mem.load c m11 z o :=
    fun z hz h1 h2 h3 c o => hF12.1.load _ _ _ (hNF z (hout z hz h1 h2) (hvG z hz) h3)
  refine wp_tPost (S := S) (ctx := ⟨rowsOf G⟩) (v := v) hS12 hvm12 rfl (by rw [temps_gss, hv]) hv1
    (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hL11 _ (by decide)]
        simp (config := {decide := true}) only [nT, nTemps, temps_gso, temps_gss]; rfl)
    hcl hcs
    (by
      intro z hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl <;>
        exact ⟨hout _ (by decide) (by decide) (by decide), hF12.2 _ (hvG _ (by decide)),
          fun h => hiw12 _ h (hvG _ (by decide))⟩)
    ⟨_, by rw [hld12 _ (by decide) (by decide) (by decide) (by decide)]; exact hisl11.load⟩
    ⟨_, by rw [hld12 _ (by decide) (by decide) (by decide) (by decide)]; exact hiap11.load⟩
    ⟨_, by rw [hld12 _ (by decide) (by decide) (by decide) (by decide)]; exact hiss11.load⟩ ?_
  intro le13 m13 hS13 hGr13 hSt13 hle13
  obtain ⟨hFr13, hW13⟩ := hSt13
  have hiw13 : ∀ z, IsWork m13 z → ¬ Mem.valid_block m11 z := fun z h =>
    (hW13 z h).elim (hiw12 z) (fun h hv => h (hF12.2 _ hv))
  have hSF : ∀ z, z ∉ S.blocks → Mem.valid_block m11 z →
      ¬ (S.Chg z ∨ ¬ Mem.valid_block m12 z ∨ IsWork m12 z) := by
    rintro z h1 h2 (h | h | h)
    · exact h1 h.1
    · exact h (hF12.2 _ h2)
    · exact hiw12 z h h2
  have hflat : ∀ z ∈ flat chain, ¬ Mem.valid_block m11 z := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact (hnew12 p hp).1
    · exact (hnew12 p hp).2
  have hTc13 : TcChain m13 S.M Search.Block.tcnode0 chain := by
    refine TcChain.unch hFr13.1 hTc12 fun z hz => ?_
    rcases List.mem_cons.1 hz with rfl | hz
    · rintro (h | h | h)
      · exact h.2.2 rfl
      · exact h (hF12.2 _ hvT)
      · exact hiw12 _ h hvT
    · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
      obtain ⟨a1, a2, a3, a4⟩ := hTo12.apart p hp
      obtain ⟨v1, v2⟩ := hTo12.valid p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl
      · rintro (h | h | h)
        · exact a1 h.1
        · exact h v1
        · exact a3 h
      · rintro (h | h | h)
        · exact a2 h.1
        · exact h v2
        · exact a4 h
  have hv0 : Mem.valid_block m11 (cb 0).2 := hv411 _ (Mem.perm_valid_block _ _ (zOfInt 0) .Cur .Freeable
    ((d0.mal (by omega)).perm 0 (by decide) (by have := c0; omega)))
  have hb0S : (cb 0).2 ∉ S.blocks := houtV _ (by simp)
  have hDW13 : DynAt m13 Block.nautyDefltwork Block.nautyDefltworkSz 8 (cb 0).1 (cb 0).2 :=
    ((d0.keep F4 (by nb) (by nb) (fun _ => Keep.unch F4 (by nb))).keep hF12.1
      (hNF _ (hout _ (by decide) (by decide) (by decide)) (hvG _ (by decide)) (by decide))
      (hNF _ (hout _ (by decide) (by decide) (by decide)) (hvG _ (by decide)) (by decide))
      (fun _ => Keep.unch hF12.1 (hNF _ hb0S hv0 (by nb)))).keep hFr13.1
      (hSF _ (hout _ (by decide) (by decide) (by decide)) (hvG _ (by decide)))
      (hSF _ (hout _ (by decide) (by decide) (by decide)) (hvG _ (by decide)))
      (fun _ => Keep.unch hFr13.1 (hSF _ hb0S hv0))
  have hmS : ∀ z ∈ S.blocks, z ≠ Block.nautyDefltwork ∧ z ≠ Block.nautyDefltworkSz := by
    intro z hz
    rcases mem_blocks rfl hz with h | h
    · have hz' : z ∈ [bg, bl, bp, bo, bst, bc, bD, bI, (cb 0).2, (cb 1).2, (cb 2).2, (cb 3).2,
          (cb 4).2, (cb 5).2, (cb 6).2, (cb 7).2, (cb 8).2] := by
        simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
        rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp [h]
      exact ⟨hPg z hz' _ (by decide), hPg z hz' _ (by decide)⟩
    · have : ∀ g ∈ Harness.Block.emitGenerator :: consts, g ≠ Block.nautyDefltwork ∧
          g ≠ Block.nautyDefltworkSz := by decide
      exact this z h
  refine wp_tFree (S := S) (ctx := ⟨rowsOf G⟩) (chain := chain) hS13
    (fun z hz => hFr13.2 _ (hvm12 z hz)) hTc13 (hTo12.mono hFr13.2 hW13) hDW13
    ((Keep.unch hFr13.1 (hSF _ (hout _ (by decide) (by decide) (by decide)) (hvG _ (by decide)))).perm _ _
      ((Keep.unch hF12.1 (hNF _ (hout _ (by decide) (by decide) (by decide)) (hvG _ (by decide))
        (by decide))).perm _ _ ((Keep.unch B6 (by nb)).perm _ _ ((Keep.unch U01 (by nG hm0)).perm _ _
          (fnPerm hm0 funct_naugraphFreedyn)))))
    (fun z hz => by
      have := hiw13 z hz
      exact ⟨fun h => this (h ▸ hvG _ (by decide)), fun h => this (h ▸ hvG _ (by decide)),
        fun h => this (h ▸ hvG _ (by decide))⟩)
    (fun _ => ⟨hb0S, fun h => hiw13 _ h hv0, fun h => hflat _ h hv0,
      hPg _ (by simp) _ (by decide), hPg _ (by simp) _ (by decide)⟩)
    hmS
    (fun z hz => ⟨fun h => hflat z hz (h ▸ hvG _ (by decide)),
      fun h => hflat z hz (h ▸ hvG _ (by decide))⟩) ?_
  intro m14 hU14 hg14
  have hFS : ∀ z, z ∉ freeGlobals → z ∉ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws] →
      z ≠ (cb 0).2 → Mem.valid_block m11 z → ¬ FreeSet m13 S chain (cb 0).1 (cb 0).2 z := by
    rintro z h1 h2 h3 h4 (h | h | ⟨-, h⟩ | h | h)
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact hiw13 z h h4
    · exact hflat z h h4
  -- `initstatus` is released on return
  have hbIS : bI ∉ S.blocks := houtV _ (by simp)
  have hvI : Mem.valid_block m11 bI := hv111 _ (hvb bI (by simp))
  have hfI14 : Mem.valid_access m14 .Mint32 bI (zOfInt 0) .Freeable :=
    hU14.access _ _ _ _ (hFS _ (by simp only [freeGlobals]; nb) (by nb) (by nb) hvI)
      (hFr13.1.access _ _ _ _ (hSF _ hbIS hvI) (hF12.1.access _ _ _ _ (hNF _ hbIS hvI (by nb))
        (F8.access _ _ _ _ (by nb) hfi8)))
  obtain ⟨m15, hfree⟩ := Mem.range_perm_free _ _ _ _ hfI14.1
  have hu15 : Unch m14 m15 (· = bI) := Alloc.Unch.free hfree
  have hk15 : ∀ z, z ∈ [bl, bo, bc, bst] →
      (¬ FreeSet m13 S chain (cb 0).1 (cb 0).2 z) ∧ ¬ z = bI := by
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with h | h | h | h <;> rw [h] <;>
      exact ⟨hFS _ (by simp only [freeGlobals]; nb) (by nb) (by nb) (hv111 _ (hvb _ (by simp))),
        by nb⟩
  have tr : ∀ {z : block}, z ∈ [bl, bo, bc, bst] → ∀ {c : memory_chunk} {o : Int} {v : val},
      FieldAt m13 c z o v → FieldAt m15 c z o v :=
    fun hz _ _ _ h => (h.unch hU14 (hk15 _ hz).1).unch hu15 (hk15 _ hz).2
  have trA : ∀ {z : block}, z ∈ [bl, bo, bc, bst] → ∀ {c : memory_chunk} {base : Int}
      {vals : Nat → val} {N : Nat}, ArrayAt m13 c z base vals N → ArrayAt m15 c z base vals N :=
    fun hz _ _ _ _ h => (h.unch hU14 (hk15 _ hz).1).unch hu15 (hk15 _ hz).2
  have hA := hS13.arrays
  have hSt := hS13.stats
  have hvO : Mem.valid_block m11 Harness.Block.options := hvG _ (by decide)
  have hOS : Harness.Block.options ∉ S.blocks := hout _ (by decide) (by decide) (by decide)
  refine ⟨m15, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show Mem.free_list m14 [(bI, zOfInt 0, Cfrontend.Ctypes.sizeof ge.genv_cenv tint)] = some m15
    simp only [Mem.free_list]
    rw [show Cfrontend.Ctypes.sizeof ge.genv_cenv tint =
      ZArith.BinInt.Z.add (zOfInt 0) (Common.Memdata.size_chunk .Mint32) from rfl, hfree]
  · rw [← hEm]
    have := hE12.append Emits.nil
    rwa [List.append_nil (Em true 1 (initialPartition G).2.length st0)] at this
  · exact trA (z := bl) (by simp) hA.lab |>.congr fun i _ => by rw [show (postState ⟨rowsOf G⟩
      (hexNode true ⟨rowsOf G⟩ 1 (initialPartition G).2.length st0).2).lab =
      (runColoredTraced G).result.canonlab from hcl0]
  · have e : (postState ⟨rowsOf G⟩
        (hexNode true ⟨rowsOf G⟩ 1 (initialPartition G).2.length st0).2).orbits =
        (Statement.finalState G).orbits := SearchInf.orbits_inf G hn0 (by show n + 2 < 2000000002; omega)
    exact trA (z := bo) (by simp) hA.orbits |>.congr fun i _ => by rw [e]
  · obtain ⟨cw, hgA⟩ := hGr13
    refine ⟨cw, trA (z := bc) (by simp) hgA.arr, ?_⟩
    rw [← congrArg (fun T => T.result.canong) hfin]
    exact hgA.rep
  · rw [← congrArg (fun T => T.result.numorbits) hfin]; exact tr (z := bst) (by simp) hSt.numorbits
  · rw [← congrArg (fun T => T.result.numgenerators) hfin]; exact tr (z := bst) (by simp) hSt.numgenerators
  · exact tr (z := bst) (by simp) hSt.errstatus
  · rw [← congrArg (fun T => T.result.numnodes) hfin]; exact tr (z := bst) (by simp) hSt.numnodes
  · rw [← congrArg (fun T => T.result.numbadleaves) hfin]; exact tr (z := bst) (by simp) hSt.numbadleaves
  · rw [← congrArg (fun T => T.result.maxlevel) hfin]; exact tr (by simp) (hSt.maxlevel rfl)
  · rw [← congrArg (fun T => T.result.tctotal) hfin]; exact tr (z := bst) (by simp) hSt.tctotal
  · rw [← congrArg (fun T => T.result.canupdates) hfin]; exact tr (z := bst) (by simp) hSt.canupdates
  · exact rperm_unch hu15 (hk15 bst (by simp)).2 (rperm_unch hU14 (hk15 bst (by simp)).1 hSt.perm)
  · intro z hz
    have h := hg14 _ (hFr13.2 _ (hF12.2 _ (hv111 _ (hg1 _ hz))))
    unfold Mem.valid_block at h ⊢
    rw [Mem.nextblock_free _ _ _ _ _ hfree]; exact h
  · exact hu15.access _ _ _ _ (by nb) (hU14.access _ _ _ _
      (hFS _ (by simp only [freeGlobals]; nb) (by nb) (by nb) hvO)
      (hFr13.1.access _ _ _ _ (hSF _ hOS hvO) (hF12.1.access _ _ _ _ (hNF _ hOS hvO (by decide))
        (B6.access _ _ _ _ (by nb) (hu1.access _ _ _ _
          (fun h => h (hgrow0 _ (valid_init hm0 (by decide)))) hopt.digraph.writable)))))

/-- `densenauty` meets the harness's specification, given the emission laws. -/
theorem densenauty_ok {k : Nat} (G : Colored n k) (gens : List (Array Nat))
    (Em : Bool → Nat → Nat → Search n → List Int)
    (hOff : EmLawOff Em ⟨rowsOf G⟩) (hFirst : EmLawFirst Em ⟨rowsOf G⟩)
    (hEm : Em true 1 (initialPartition G).2.length
      (SearchInf.initialC n (initialPartition G).1 (initialPartition G).2) = gensWords gens n)
    (hAut : AutomCb xi Harness.Block.emitGenerator) (bg bl bp bo bst bc : block) :
    Satisfies xi ge (.Internal dense.fn.densenauty) (Harness.densenautySpec G gens bg bl bp bo bst bc) :=
  densenauty_satisfies G gens bg bl bp bo bst bc fun capD bD =>
    nauty_satisfies G gens Em hOff hFirst hEm hAut bg bl bp bo bst bc capD bD

/-- `main` meets its specification, given the emission laws, the root's emitted
words, and their agreement with `expected`'s first block. -/
theorem main_ok {k : Nat} (G : Colored n k) (gens : List (Array Nat)) (ins : List Int)
    (Em : Bool → Nat → Nat → Search n → List Int)
    (hOff : EmLawOff Em ⟨rowsOf G⟩) (hFirst : EmLawFirst Em ⟨rowsOf G⟩)
    (hEm : Em true 1 (initialPartition G).2.length
      (SearchInf.initialC n (initialPartition G).1 (initialPartition G).2) = gensWords gens n)
    (hgens : gensWords gens n = Harness.autosWords G)
    (hins : Statement.Encodes G ins) (hn0 : 0 < n) (hmax : n ≤ Statement.maxN)
    (hkmax : k ≤ Statement.maxN) :
    Satisfies Statement.xi ge (.Internal dense.fn.main) (Harness.mainSpec G ins) :=
  Harness.main_satisfies G gens ins hins hn0 hmax hkmax hgens fun bg bl bp bo bst bc =>
    densenauty_ok G gens Em hOff hFirst hEm automCb_emit bg bl bp bo bst bc

end NautyVerified.Proofs.Top

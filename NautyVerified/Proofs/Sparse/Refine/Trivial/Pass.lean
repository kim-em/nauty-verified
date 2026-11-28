import NautyVerified.Proofs.Sparse.Refine.Trivial.Edge
import NautyVerified.Proofs.Sparse.Refine.Trivial.ResetK2
import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Pass

/-!
# `refine_sg`'s singleton splitter meets `TrivialPass`

`trivialPass`: `trivial` (`RESETMARKS1`, `RESETMARKS2`, the reads of the
splitting vertex's row, the neighbour scan `wp_edgeLoop`, `sortints` of the
touched starts, the hash of their number and the touched-cell loop
`wp_cellLoop`) computes HexGraphIso's `splitSingleton` (`splitSingleton_eq`).
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph sortCells splitSingleton)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {S : Scr}

/-- The neighbour scan of the splitting vertex at position `split`. -/
abbrev scan (G : Hex.SparseGraph n) (s : RefineSt n) (split : Nat) : Array Nat × Array Nat × Array Nat :=
  markScan (.ofGraph G) s.cellstart s.marks s.vmarks (s.stamp + 1) s.lab[split]!

/-- HexGraphIso's `mark_neighbors` for `scan`: the sorted touched starts are
distinct nontrivial cells of the partition. -/
theorem scan_cells {level : Nat} {s : RefineSt n} (hv : s.Valid level) {split : Nat} (hsp : split < n) :
    (sortCells (scan G s split).2.1).toList.Nodup ∧
      ∀ a ∈ (sortCells (scan G s split).2.1).toList,
        IsCell s.ptn level a (s.cellend[a]! + 1 - a) ∧ a < s.cellend[a]! ∧ s.cellend[a]! < n := by
  have hlq := Hex.GraphIso.Nauty.Sparse.perm_bound hv.lab hsp
  have hmark := Hex.GraphIso.Nauty.Sparse.mark_neighbors G ⟨s.lab[split]!, hlq⟩ s.lab s.ptn s.cellstart
    s.cellend s.marks s.vmarks level s.stamp hv.lab hv.size hv.closed hv.index
    ⟨hv.scratch.marks_size, hv.scratch.marks_le⟩ ⟨hv.scratch.vmarks_size, hv.scratch.vmarks_le⟩
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, mark_loop] at hmark
  exact ⟨hmark.1.nodup, hmark.2.2⟩

/-- After the scan and the sort: the hash of the number of touched cells and
the touched-cell loop. -/
theorem wp_rest {Q : Post} {le : temp_env} {m : mem} {s : RefineSt n} {split : Nat}
    (hok : Ok n L) (hm : Mem m L G s S) (hr : Rep L s S) (ht : Tmp le L s) (hv : s.Valid L.level)
    (hbud : Budget L.level s) (hcode : s.longcode < 2 ^ 62) (hsp : split < n)
    (hXn : (scan G s split).2.1.size ≤ n)
    (hmk2 : ∀ v < n, (S.mk2 v = S.st2 ↔ (scan G s split).2.2[v]! = s.stamp + 1))
    (hw4 : ∀ i < (scan G s split).2.1.size,
      S.w4 i = .Vint (ir (sortCells (scan G s split).2.1)[i]!))
    (hhc : PTree.get id.«hitcells» le = some (.Vint (ir (scan G s split).2.1.size)))
    (hQ : ∀ le' m' S', After L G (splitSingleton (.ofGraph G) L.level split s) passTemps le m le' m' S' →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (.Ssequence (sk (mash (tv id.«hitcells»))) (.Ssequence (sk (.Sset id.«i» (ci 0 tint)))
      cellLoopT)) Q empty_env le m := by
  have hnl := hok.nlt
  let X := (scan G s split).2.1
  let r := scan G s split
  let init : RefineSt n :=
    ({ s with marks := r.1, vmarks := r.2.2, stamp := s.stamp + 1 } : RefineSt n).hash (sortCells X).size
  have hsz : (sortCells X).size = X.size := Nontrivial.sortCells_size X
  have hsplit : splitSingleton (.ofGraph G) L.level split s =
      cellFold L.level (s.stamp + 1) (sortCells X).toList init := splitSingleton_eq _ _ _ _
  have hst := RefineSt.Valid.singleton hv G split hsp
  rw [hsplit] at hst
  obtain ⟨hnd, hcells⟩ := scan_cells (G := G) hv hsp
  wp_step; wp_step; wp_step
  refine wp_mash ht.longcode hcode (show Exec.evalExpr sge empty_env le m (tv id.«hitcells») = _ from hhc)
    rfl (by omega) ?_
  have ht1 : Tmp _ L (s.hash X.size) := ht.hash X.size
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  have ht2 : Tmp _ L init := (ht1.set (x := id.«i») (.Vint (ir 0)) (by decide)).congr
    (by simp only [init, RefineSt.hash, hsz, X]) rfl
  have hm0 : Mem m L G init S := hm.congr rfl rfl rfl rfl
  have hr0 : Rep L init S := ⟨hr.starts, hr.queue, hr.w3size, hr.w3small, hr.ptnSmall⟩
  have hqn : (cellFold L.level (s.stamp + 1) (sortCells X).toList init).queue.size ≤ n :=
    queue_size_le hst.1.queue.set
  have hnc : (cellFold L.level (s.stamp + 1) (sortCells X).toList init).numcells < 2147483648 := by
    have hb := Budget.step hst.2 hbud
    have := Hex.GraphIso.Nauty.bcount_le
      (cellFold L.level (s.stamp + 1) (sortCells X).toList init).ptn L.level n
    unfold Budget at hb
    omega
  refine wp_cellLoop (stamp := s.stamp + 1) hok hm0 hr0 ht2 hnd (by rw [Array.length_toList, hsz]; exact hXn)
    hmk2 (fun i hi => ?_) ?_ (temps_gss _ _ _) hv.lab hv.size hv.index hcells
    (Nat.lt_of_lt_of_le (Refine.mash_lt _ _) (by decide)) hqn hnc ?_
  · rw [Array.length_toList, hsz] at hi
    rw [hw4 i hi, getElem!_pos (sortCells X).toList i (by rw [Array.length_toList, hsz]; exact hi),
      getElem!_pos (sortCells X) i (by rw [hsz]; exact hi), Array.getElem_toList]
  · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hhc, Array.length_toList, hsz]
  intro le' m' S' hm' hr' ht' _ _ _ _ _ hf' ho'
  apply hQ
  rw [hsplit]
  refine ⟨hm', hr', hf', ht', (cellFold_props _ _ _ _ (Nat.lt_of_lt_of_le (Refine.mash_lt _ _)
    (by decide))).2.2.2, fun x h1 h2 h3 h4 => ?_⟩
  have hsub : ∀ y ∈ loopTempsT, y ∈ passTemps := by decide
  rw [ho' x (fun h => h1 (hsub x h)) h3 h4, temps_gso _ _ (fun h => h1 (by rw [h]; decide)),
    temps_gso _ _ h3]

theorem trivialPass : TrivialPass (xi := xi) := by
  intro n L G Q le m s S split hok hm hr ht hv hfr hbud hcode hsp _ _ hisp hQ
  have hnl := hok.nlt
  have hmc1 := hok.mc1
  have hmc2 := hok.mc2
  obtain ⟨hmk, hvmk, hst⟩ := hfr
  have hlq := Hex.GraphIso.Nauty.Sparse.perm_bound hv.lab hsp
  apply wp_seq; simp only [seqPost, Post.after]
  refine Nontrivial.wp_resetmarks1K hm.k1 (t := idOf 734) (ij := id.«ij») ?_
  intro le1 m1 st1 mk1 hM1 hbelow1 hu1 hg1 hk1 ho1
  have hm1 := Nontrivial.Mem.setK1 hok hm hu1 st1 mk1 hM1
  have hf1 : Frame L m m1 := ⟨hu1.mono fun z hz => .inl (by
      rcases hz with rfl | ⟨-, rfl⟩ <;> simp [Loc.writes, Loc.wblocks]), fun z _ => hk1 z, hg1⟩
  apply wp_seq; simp only [seqPost, Post.after]
  refine wp_resetmarks2K hm1.k2 (t := idOf 735) (ij := id.«ij__1») ?_
  intro le2 m2 st2 mk2 hM2 hbelow2 hu2 hg2 hk2 ho2
  have hm2 := Mem.setK2 hok hm1 hu2 st2 mk2 hM2
  have hf2 : Frame L m1 m2 := ⟨hu2.mono fun z hz => .inl (by
      rcases hz with rfl | ⟨-, rfl⟩ <;> simp [Loc.writes, Loc.wblocks]), fun z _ => hk2 z, hg2⟩
  have ho12 : ∀ x, x ≠ idOf 734 → x ≠ id.«ij» → x ≠ idOf 735 → x ≠ id.«ij__1» →
      PTree.get x le2 = PTree.get x le := fun x h1 h2 h3 h4 => by rw [ho2 x h3 h4, ho1 x h1 h2]
  have ho2' : ∀ x, x ∉ passTemps → PTree.get x le2 = PTree.get x le := fun x hx =>
    ho12 x (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
      (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
  have ht2 : Tmp le2 L s := ht.frame ho2' (by decide)
  have hisp2 : PTree.get id.«isplit» le2 = some (.Vint (ir split)) := by
    rw [ho12 _ (by decide) (by decide) (by decide) (by decide)]; exact hisp
  let S2 : Scr := { { S with st1 := st1, mk1 := mk1 } with st2 := st2, mk2 := mk2 }
  have hr2 : Rep L s S2 := ⟨hr.starts, hr.queue, hr.w3size, hr.w3small, hr.ptnSmall⟩
  -- hitcells = 0
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  let le3 := PTree.set id.«hitcells» (.Vint (ir 0)) le2
  have ht3 : Tmp le3 L s := ht2.set _ (by decide)
  -- splitv = lab[isplit]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_lab hok hm2 ht3 (show Exec.evalExpr sge empty_env le3 m2 (tv id.«isplit») = _ by
    simp only [Exec.evalExpr, le3]; rw [temps_gso _ _ (by decide)]; exact hisp2) rfl hsp]
  let le4 := PTree.set id.«splitv» (.Vint (ir s.lab[split]!)) le3
  have ht4 : Tmp le4 L s := ht3.set _ (by decide)
  have hsv4 : Exec.evalExpr sge empty_env le4 m2 (tv id.«splitv») = some (.Vint (ir s.lab[split]!)) := by
    simp only [Exec.evalExpr, le4, temps_gss]
  -- vi = v[splitv]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_idx (pe := .Etempvar id.«v» (tptr tulong)) hm2.graph.varr (by omega) ht4.v rfl rfl rfl
    _ _ hlq hsv4 rfl]
  let le5 := PTree.set id.«vi» (vVals G s.lab[split]!) le4
  have ht5 : Tmp le5 L s := ht4.set _ (by decide)
  -- di = d[splitv]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_idx (pe := .Etempvar id.«d» (tptr tint)) hm2.graph.darr (by omega) ht5.d rfl rfl rfl
    _ _ hlq (show Exec.evalExpr sge empty_env le5 m2 (tv id.«splitv») = _ by
      simp only [Exec.evalExpr, le5]; rw [temps_gso _ _ (by decide)]; exact hsv4) rfl]
  let le6 := PTree.set id.«di» (dVals G s.lab[split]!) le5
  have ht6 : Tmp le6 L s := ht5.set _ (by decide)
  -- ii = 0; the neighbour scan
  apply wp_seq; simp only [seqPost, Post.after]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  let le7 := PTree.set id.«ii» (.Vlong (lr 0)) le6
  have ht7 : Tmp le7 L s := ht6.set _ (by decide)
  have hg7 : ∀ x, x ≠ id.«ii» → x ≠ id.«di» → x ≠ id.«vi» → x ≠ id.«splitv» → x ≠ id.«hitcells» →
      PTree.get x le7 = PTree.get x le2 := fun x h1 h2 h3 h4 h5 => by
    simp only [le7, le6, le5, le4, le3]
    rw [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3, temps_gso _ _ h4, temps_gso _ _ h5]
  let v := s.lab[split]!
  have hlo := G.offset_mono (i := v) (j := v + 1) (by omega) (by omega)
  have hhi := G.offset_le (i := v + 1) (by omega)
  have hdeg : (Graph.ofGraph G).degree v ≤ n := degree_lt G hlq
  have hinv : MarkInv n (s.stamp + 1) (s.marks, #[], s.vmarks) := by
    refine ⟨fun k hk => ?_, List.nodup_nil, by simp, by rw [hmk]; simp, by rw [hvmk]; simp⟩
    rw [hmk, hst, getElem!_pos (Array.replicate n 0) k (by simp; omega), Array.getElem_replicate]
    simp
  refine wp_edgeLoop (s := s) (S := S2) (stamp := s.stamp + 1) (VI := (Graph.ofGraph G).offsets[v]!)
    (D := (Graph.ofGraph G).degree v) (marks := s.marks) (vmarks := s.vmarks) hok hm2 hr2 ht7 hinv
    (fun k hk => ?_) (fun k hk => ?_) (fun w hw => hv.index.vertex_le hv.size hv.closed hv.lab hw)
    (by simp only [Graph.degree, Graph.ofGraph] at hdeg ⊢; omega) (by omega)
    (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact temps_gss _ _ _)
    (by rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _) (temps_gss _ _ _)
    (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide),
      temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]) ?_
  · rw [hmk, hst, getElem!_pos (Array.replicate n 0) k (by simp; omega), Array.getElem_replicate]
    have := hbelow1 k (by omega)
    constructor
    · intro h; exact absurd (show mk1 k = (st1 : Int) from h) (by omega)
    · intro h; omega
  · rw [hvmk, hst, getElem!_pos (Array.replicate n 0) k (by simp; omega), Array.getElem_replicate]
    have := hbelow2 k (by omega)
    constructor
    · intro h; exact absurd (show mk2 k = (st2 : Int) from h) (by omega)
    · intro h; omega
  intro le8 m8 S8 hm8 hr8 _ _ _ _ _ _ r2 r4 hmi hhc8 hf8 ho8
  have hsc : scanAt (Graph.ofGraph G) s.cellstart s.marks s.vmarks (s.stamp + 1)
      (Graph.ofGraph G).offsets[v]! ((Graph.ofGraph G).degree v) = scan G s split := rfl
  rw [hsc] at r2 r4 hmi hhc8
  have ht8 : Tmp le8 L s := ht7.frame ho8 (by decide)
  let X := (scan G s split).2.1
  have hXn : X.size ≤ n := hmi.size_le
  have hXnd : X.toList.Nodup := hmi.2.1
  have hXv : ∀ i < X.size, X[i]! < n := fun i hi => by
    rw [getElem!_pos X i hi]; exact hmi.2.2.1 _ (Array.getElem_mem_toList _)
  have ho8' : ∀ x, x ∉ passTemps → PTree.get x le8 = PTree.get x le := fun x hx => by
    have hsubE : ∀ y ∈ edgeTemps, y ∈ passTemps := by decide
    rw [ho8 x (fun h => hx (hsubE x h)), hg7 x (fun h => hx (by rw [h]; decide))
      (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
      (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))]
    exact ho2' x hx
  have hfinal : ∀ le' m' S', After L G (splitSingleton (.ofGraph G) L.level split s) passTemps le8 m8
      le' m' S' → Q.normal E0 empty_env le' m' := fun le' m' S' hA =>
    hQ le' m' S' (Nontrivial.After.pre hA ((hf1.trans hf2).trans hf8) fun x h1 _ _ _ => ho8' x h1)
  simp only [E0_append]
  apply wp_seq; simp only [seqPost, Post.after]
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hhc8, typeof, cop]
  rw [ir_lt (a := 1) (b := (X.size : Int)) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩]
  by_cases h1 : 1 < X.size
  · rw [show decide ((1 : Int) < X.size) = true from decide_eq_true (by omega)]
    simp (config := {decide := true}) only [cop, ite_true]
    wp_step; wp_step
    refine Nontrivial.wp_sortHitcell hok hm8 (X := X) (by omega) hXn r4 hXv hXnd hhc8 ?_
    intro m9 w hm9 hw9 hf9
    refine wp_rest hok hm9 ⟨hr8.starts, hr8.queue, hr8.w3size, hr8.w3small, hr8.ptnSmall⟩ ht8 hv
      hbud hcode hsp hXn r2 hw9 hhc8 ?_
    intro le' m' S' hA
    exact hfinal le' m' S' (Nontrivial.After.pre hA hf9 fun _ _ _ _ _ => rfl)
  · rw [show decide ((1 : Int) < X.size) = false from decide_eq_false (by omega)]
    simp (config := {decide := true}) only [cop, ite_false]
    apply wp_skip
    refine wp_rest hok hm8 hr8 ht8 hv hbud hcode hsp hXn r2
      (fun i hi => by rw [Nontrivial.sortCells_small (show X.size ≤ 1 by omega)]; exact r4 i hi) hhc8 hfinal

end NautyVerified.Proofs.Sparse.Refine.Trivial

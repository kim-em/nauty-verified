import NautyVerified.Proofs.Sparse.Refine.Nontrivial.ResetK

/-!
# `refine_sg`'s nontrivial splitter meets `NontrivialPass`

`nontrivialPass_of`: given the count split (`CountPass`), `nontrivial`
(`RESETMARKS1`, the count phase `wp_countLoop`, `sortints` of the touched
starts, the hash of their number and the touched-cell loop `wp_cellLoopN`)
computes HexGraphIso's `splitNontrivial` (`splitNontrivial_eq`).
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph splitCounts sortCells splitNontrivial)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

theorem sortCells_size (X : Array Nat) : (sortCells X).size = X.size := by
  have := (Hex.GraphIso.Nauty.Sparse.sortCells_perm X).length_eq
  simpa using this

theorem sortCells_small {X : Array Nat} (h : X.size ≤ 1) : sortCells X = X := by
  rw [Hex.GraphIso.Nauty.Sparse.sortCells_eq_fast]
  unfold Hex.GraphIso.Nauty.Sparse.sortCellsFast
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h0 <;> simp [h0]

/-- An `After` from a later point, with the memory change and the temporaries
since the earlier one. -/
theorem After.pre {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {le le1 le2 : temp_env}
    {m m1 m2 : mem} {S2 : Scr} (h : After L G t passTemps le1 m1 le2 m2 S2) (hf : Frame L m m1)
    (ho : ∀ x, x ∉ passTemps → x ∉ args → x ≠ id.longcode → x ≠ id.nactive →
      PTree.get x le1 = PTree.get x le) :
    After L G t passTemps le m le2 m2 S2 :=
  ⟨h.mem, h.rep, hf.trans h.frame, h.tmp, h.code, fun x h1 h2 h3 h4 =>
    (h.temps x h1 h2 h3 h4).trans (ho x h1 h2 h3 h4)⟩

/-- After the count phase and the sort: the hash of the number of touched
cells and the touched-cell loop. -/
theorem wp_rest (hc : CountPass (xi := xi)) {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {S : Scr}
    {Q : Post} {le : temp_env} {m : mem} {s : RefineSt n} {split len : Nat}
    (hok : Ok n L) (hm : Mem m L G s S) (hr : Rep L s S) (ht : Tmp le L s) (hv : s.Valid L.level)
    (hbud : Budget L.level s) (hcode : s.longcode < 2 ^ 62)
    (hcc : IsCell s.ptn L.level split len) (hb : split + len ≤ n)
    (hhits : S.w3 = (countPhase (.ofGraph G) s split).2.1)
    (hw4 : ∀ i < (countPhase (.ofGraph G) s split).2.2.size,
      S.w4 i = .Vint (ir (sortCells (countPhase (.ofGraph G) s split).2.2)[i]!))
    (hXn : (countPhase (.ofGraph G) s split).2.2.size ≤ n)
    (hhc : PTree.get id.«hitcells» le = some (.Vint (ir (countPhase (.ofGraph G) s split).2.2.size)))
    (hQ : ∀ le' m' S', After L G (splitNontrivial (.ofGraph G) L.level split s) passTemps le m le' m' S' →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (.Ssequence (sk (mash (tv id.«hitcells»))) (.Ssequence (sk (.Sset id.«i» (ci 0 tint)))
      cellLoopN)) Q empty_env le m := by
  have hnl := hok.nlt
  let X := (countPhase (.ofGraph G) s split).2.2
  let b0 := countState (.ofGraph G) s split
  wp_step; wp_step; wp_step
  refine wp_mash ht.longcode hcode (show Exec.evalExpr sge empty_env le m (tv id.«hitcells») = _ from hhc)
    rfl (by omega) ?_
  have ht1 : Tmp _ L (s.hash X.size) := ht.hash X.size
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  have hsz : (sortCells X).size = X.size := sortCells_size X
  have hb0 : b0 = (countRaw (.ofGraph G) s split).hash (sortCells X).size := rfl
  have ht2 : Tmp _ L b0 := (ht1.set (x := id.«i») (.Vint (ir 0)) (by decide)).congr
    (by simp only [b0, countState, countRaw, RefineSt.hash, hsz, X]) rfl
  have hm0 : Mem m L G b0 S := hm.congr rfl rfl rfl rfl
  have hr0 : Rep L b0 S := ⟨hr.starts, hr.queue, hr.w3size, hr.w3small, hr.ptnSmall⟩
  have hF := Fold.initial G hv split len hcc hb
  refine wp_cellLoopN hc hok hm0 hr0 ht2 hF (by omega) hbud (Nat.lt_of_lt_of_le (Refine.mash_lt _ _) (by decide))
    (fun v hv => by rw [hhits]; rfl) (fun i hi => ?_) (by rw [Array.length_toList, hsz]; exact hXn) (temps_gss _ _ _) ?_ ?_
  · rw [Array.length_toList, hsz] at hi
    rw [hw4 i hi, getElem!_pos (sortCells X).toList i (by rw [Array.length_toList, hsz]; exact hi),
      getElem!_pos (sortCells X) i (by rw [hsz]; exact hi), Array.getElem_toList]
  · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hhc, Array.length_toList, hsz]
  intro le' m' S' hA
  apply hQ
  rw [splitNontrivial_eq]
  have : foldTo L.level (sortCells X).toList b0 (sortCells X).toList.length =
      (sortCells X).toList.foldl (fun t first => splitCounts L.level first false t) b0 := by
    simp only [foldTo, List.take_length]
  rw [← this]
  refine ⟨hA.mem, hA.rep, hA.frame, hA.tmp, hA.code, fun x h1 h2 h3 h4 => ?_⟩
  rw [hA.temps x h1 h2 h3 h4, temps_gso _ _ (fun h => h1 (by simp [h, passTemps])),
    temps_gso _ _ h3]

theorem nontrivialPass_of (hc : CountPass (xi := xi)) : NontrivialPass (xi := xi) := by
  intro n L G Q le m s S split len hok hm hr ht hv hfr hbud hcode hhits hcc hb hlen hsp hQ
  have hnl := hok.nlt
  obtain ⟨hmk, -, hst⟩ := hfr
  have hmc := hok.mc1
  apply wp_seq; simp only [seqPost, Post.after]
  refine wp_resetmarks1K hm.k1 (t := idOf 749) (ij := id.«ij__2») ?_
  intro le1 m1 st1 mk1 hM1 hbelow hu1 hg1 hk1 ho1
  have hm1 := Mem.setK1 hok hm hu1 st1 mk1 hM1
  have hf1 : Frame L m m1 := ⟨hu1.mono fun z hz => .inl (by
      rcases hz with rfl | ⟨-, rfl⟩ <;> simp [Loc.writes, Loc.wblocks]), fun z _ => hk1 z, hg1⟩
  have ho1' : ∀ x, x ∉ passTemps → PTree.get x le1 = PTree.get x le := fun x hx =>
    ho1 x (fun h => hx (by rw [h]; decide)) (fun h => hx (by rw [h]; decide))
  have ht1 : Tmp le1 L s := ht.frame ho1' (by decide)
  have hr1 : Rep L s { S with st1 := st1, mk1 := mk1 } :=
    ⟨hr.starts, hr.queue, hr.w3size, hr.w3small, hr.ptnSmall⟩
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  let le2 := PTree.set id.«hitcells» (.Vint (ir 0)) le1
  have ht2 : Tmp le2 L s := ht1.set _ (by decide)
  have hcr : CRep s { S with st1 := st1, mk1 := mk1 } (s.marks, s.hits, #[]) := by
    refine ⟨?_, fun i hi => absurd hi (by simp), fun k hk => ?_⟩
    · apply Array.ext
      · exact hr.w3size.trans hv.scratch.hits_size.symm
      · intro i h1 h2
        have := hhits i (by rw [hr.w3size] at h1; exact h1)
        rw [getElem!_pos S.w3 i h1, getElem!_pos s.hits i h2] at this
        exact this
    · simp only [hmk, hst]
      rw [getElem!_pos (Array.replicate n 0) k (by simp; omega), Array.getElem_replicate]
      constructor
      · intro h
        exact absurd (show mk1 k = (st1 : Int) from h) (by have := hbelow k (by omega); omega)
      · intro h; omega
  apply wp_seq; simp only [seqPost, Post.after]
  refine wp_countLoop (split := split) (len := len) hok hm1 hr1 ht2 hv hcr hcc hb ?_ ?_ ?_
  · rw [temps_gso _ _ (by decide), ho1 _ (by decide) (by decide)]; exact hsp
  · exact temps_gss _ _ _
  intro le3 m3 S3 hm3 hr3 hcr3 hsc3 hf3 hhc3 ho3
  have ht3 : Tmp le3 L s := ht2.frame ho3 (by decide)
  have hXn := touched_le hsc3
  let X := (countPhase (.ofGraph G) s split).2.2
  have hXn' : X.size ≤ n := hXn
  have hXnd : X.toList.Nodup := hsc3.touch.nodup
  have hXv : ∀ i < X.size, X[i]! < n := fun i hi => by
    have hm := (hsc3.touch.members X[i]!).mp (by rw [getElem!_pos X i hi]; exact Array.getElem_mem_toList _)
    exact hm.1
  have hfinal : ∀ le' m' S', After L G (splitNontrivial (.ofGraph G) L.level split s) passTemps le3 m3
      le' m' S' → Q.normal E0 empty_env le' m' := fun le' m' S' hA =>
    hQ le' m' S' (After.pre hA (hf1.trans hf3) fun x h1 _ _ _ => by
      have hsubC : ∀ y ∈ countTemps, y ∈ passTemps := by decide
      rw [ho3 x (fun h => h1 (hsubC x h)), temps_gso _ _ (fun h => h1 (by rw [h]; decide))]
      exact ho1' x h1)
  apply wp_seq; simp only [seqPost, Post.after]
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hhc3, typeof, cop]
  rw [ir_lt (a := 1) (b := (X.size : Int)) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩]
  by_cases h1 : 1 < X.size
  · rw [show decide ((1 : Int) < X.size) = true from decide_eq_true (by omega)]
    simp (config := {decide := true}) only [cop, ite_true]
    wp_step; wp_step
    refine wp_sortHitcell hok hm3 (X := X) (by omega) hXn hcr3.touched hXv hXnd hhc3 ?_
    intro m4 w hm4 hw4' hf4
    refine wp_rest hc hok hm4 ⟨hr3.starts, hr3.queue, hr3.w3size, hr3.w3small, hr3.ptnSmall⟩ ht3 hv
      hbud hcode hcc hb hcr3.hits hw4' hXn hhc3 ?_
    intro le' m' S' hA
    exact hfinal le' m' S' (After.pre hA hf4 fun _ _ _ _ _ => rfl)
  · rw [show decide ((1 : Int) < X.size) = false from decide_eq_false (by omega)]
    simp (config := {decide := true}) only [cop, ite_false]
    apply wp_skip
    refine wp_rest hc hok hm3 hr3 ht3 hv hbud hcode hcc hb hcr3.hits
      (fun i hi => by rw [sortCells_small (show X.size ≤ 1 by omega)]; exact hcr3.touched i hi) hXn hhc3 hfinal

end NautyVerified.Proofs.Sparse.Refine.Nontrivial

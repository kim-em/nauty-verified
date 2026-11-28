import NautyVerified.Proofs.Search.Node.Target
import NautyVerified.Proofs.Search.Node.Compare
import NautyVerified.Proofs.Search.Node.Policy

/-!
# `othernode0`'s target cell is `chooseTarget false`

`chooseOff` is `othernode0`'s fragment after `tc = -1`:

```
if (numcells < n && (eqlev_first == level || (getcanon && comp_canon >= 0))) {
  if (!getcanon || comp_canon < 0) {
    maketargetcell(…, firsttc[level], …);
    if (tc != firsttc[level]) eqlev_first = level - 1;
  } else maketargetcell(…, -1, …);
  stats->tctotal += tcellsize;
}
```

`wp_chooseOff`: it leaves HexGraphIso's `chooseTarget false` state, `tc`
holding its position, and, when a cell is chosen, the target cell and
`tcellsize` holding its contents and size.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep dyn3Set)
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

/-- `if (!getcanon) t710 = 1; else t710 = (comp_canon < 0);` -/
abbrev hintSel : statement :=
  .Sifthenelse (.Eunop .Onotbool (.Evar dense.id.«nauty:getcanon» tint) tint)
    (.Sset (idOf 710) (ci 1 tint))
    (Set.sk (.Sset (idOf 710) (.Ecast (.Ebinop .Olt (.Evar dense.id.«nauty:comp_canon» tint)
      (ci 0 tint) tint) tbool)))

/-- `if (tc != firsttc[level]) eqlev_first = level - 1;` -/
abbrev tcReset : statement :=
  .Sifthenelse (.Ebinop .One (.Evar dense.id.tc tint)
      (Alloc.gat dense.id.«nauty:firsttc» (Refine.tv dense.id.level)) tint)
    (Set.sk (.Sassign (.Evar dense.id.«nauty:eqlev_first» tint)
      (.Ebinop .Osub (Refine.tv dense.id.level) (ci 1 tint) tint))) .Sskip

/-- `stats->tctotal += tcellsize;` -/
abbrev tcTotal : statement :=
  .Sassign (statsF dense.id.tctotal tulong)
    (.Ebinop .Oadd (statsF dense.id.tctotal tulong) (.Evar dense.id.tcellsize tint) tulong)

/-- The fragment of `othernode0` that chooses the target cell. -/
abbrev chooseOff : statement :=
  .Ssequence (Set.sk Othernode.target)
    (.Sifthenelse (Refine.tv (idOf 711))
      (.Ssequence
        (.Ssequence (Set.sk hintSel)
          (.Sifthenelse (Refine.tv (idOf 710))
            (.Ssequence
              (Set.sk (mtcCall (Alloc.gat dense.id.«nauty:firsttc» (Refine.tv dense.id.level))))
              (Set.sk tcReset))
            (Set.sk (mtcCall (.Eunop .Oneg (ci 1 tint) tint)))))
        (Set.sk tcTotal))
      .Sskip)

/-- The condition under which `chooseTarget false` chooses a cell. -/
abbrev chooses {n : Nat} {κ : Type} (level numcells : Nat) (st : SearchState n κ) : Prop :=
  numcells < n ∧ (st.eqlevFirst = level ∨ 0 ≤ st.compCanon)

/-- `maketargetcell`'s position is a vertex and its size at most `n`. -/
theorem mtc_bounds {n : Nat} (ctx : Ctx n) (lab ptn : Array Nat) (level tcLevel : Nat) (hint : Int)
    (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) (hh : hint < n) {x : Nat} (hx : x < n)
    (hgt : level < ptn[x]!) :
    (maketargetcell ctx lab ptn level tcLevel hint).1 < n ∧
      (maketargetcell ctx lab ptn level tcLevel hint).2.2 ≤ n := by
  obtain ⟨h1, h2⟩ := Spec.Bestcell.targetcell_mem ctx lab ptn level tcLevel hint hs hlast hh hx hgt
  unfold maketargetcell
  simp only
  generalize targetcell ctx lab ptn level tcLevel hint = i at h1 h2 ⊢
  have hi1 : i + 1 < n := by
    rcases Nat.lt_or_ge (i + 1) n with h | h
    · exact h
    · have : i = n - 1 := by omega
      subst this; omega
  have := (Spec.cellEnd_spec hs hi1 hlast).2.1
  omega

/-- The hint `chooseTarget false` passes. -/
abbrev offHint {n : Nat} {κ : Type} (level : Nat) (st : SearchState n κ) : Int :=
  if st.compCanon < 0 then st.firsttc[level]! else -1

/-- `chooseTargetG O false`, case by case. -/
theorem chooseTargetG_false_eq {n : Nat} (O : NautyVerified.Proofs.Dispatch.Ops) (G : O.Gr n) (tl level nc : Nat)
    (st : SearchState n (O.Canon n)) :
    chooseTargetG O false G tl level nc st =
      if chooses level nc st then
        (((NautyVerified.Proofs.Maketargetcell.mtcOf n st.lab st.ptn level (O.targetcell G st.lab st.ptn level tl (offHint level st))).1 : Int),
         (NautyVerified.Proofs.Maketargetcell.mtcOf n st.lab st.ptn level (O.targetcell G st.lab st.ptn level tl (offHint level st))).2.1,
         (NautyVerified.Proofs.Maketargetcell.mtcOf n st.lab st.ptn level (O.targetcell G st.lab st.ptn level tl (offHint level st))).2.2,
         { (if st.compCanon < 0 ∧
              ((NautyVerified.Proofs.Maketargetcell.mtcOf n st.lab st.ptn level
                (O.targetcell G st.lab st.ptn level tl (offHint level st))).1 : Int) ≠
                st.firsttc[level]! then { st with eqlevFirst := level - 1 } else st) with
           tctotal := st.tctotal + (NautyVerified.Proofs.Maketargetcell.mtcOf n st.lab st.ptn level
             (O.targetcell G st.lab st.ptn level tl (offHint level st))).2.2 })
      else ((-1 : Int), VSet.empty, 0, st) := by
  unfold chooseTargetG offHint chooses
  by_cases hc : nc < n ∧ (st.eqlevFirst = level ∨ 0 ≤ st.compCanon)
  · rw [ite_eq_left hc]
    have hc' : (nc < n && (st.eqlevFirst == level || decide (st.compCanon ≥ 0))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
      exact ⟨hc.1, hc.2.imp id (fun h => by omega)⟩
    simp only [Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and, hc', ite_true]
    by_cases hcc : st.compCanon < 0
    · simp [hcc]
      split <;> simp_all
    · simp [hcc]
  · rw [ite_eq_right hc]
    have hc' : (nc < n && (st.eqlevFirst == level || decide (st.compCanon ≥ 0))) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      by_cases h1 : nc < n
      · right; exact ⟨fun h => hc ⟨h1, .inl h⟩, fun h => hc ⟨h1, .inr (by omega)⟩⟩
      · left; exact h1
    simp [hc']

/-- `chooseTarget false`, case by case. -/
theorem chooseTarget_false_eq {n : Nat} (ctx : Ctx n) (tl level nc : Nat) (st : Search n) :
    chooseTarget false ctx tl level nc st =
      if chooses level nc st then
        (((maketargetcell ctx st.lab st.ptn level tl (offHint level st)).1 : Int),
         (maketargetcell ctx st.lab st.ptn level tl (offHint level st)).2.1,
         (maketargetcell ctx st.lab st.ptn level tl (offHint level st)).2.2,
         { (if st.compCanon < 0 ∧
              ((maketargetcell ctx st.lab st.ptn level tl (offHint level st)).1 : Int) ≠
                st.firsttc[level]! then { st with eqlevFirst := level - 1 } else st) with
           tctotal := st.tctotal + (maketargetcell ctx st.lab st.ptn level tl (offHint level st)).2.2 })
      else ((-1 : Int), VSet.empty, 0, st) :=
  chooseTargetG_false_eq NautyVerified.Proofs.Dispatch.denseOps ctx tl level nc st

set_option maxHeartbeats 2000000 in
theorem wp_chooseOff {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level nc : Nat}
    (h : SearchAt m S ctx st pre nsp) (hvU : Mem.valid_block m S.bUA)
    (hvT : Mem.valid_block m Block.tcnode0)
    {bnc bt bz bc : block}
    (hloc : [bt, bz, bc].Pairwise (· ≠ ·))
    (hlocS : ∀ z ∈ [bt, bz, bc], z ∉ S.blocks ∧ Mem.valid_block m z ∧ ¬ IsWork m z)
    (hncS : bnc ≠ bt ∧ bnc ≠ bz ∧ bnc ≠ bc)
    (htc : PTree.get dense.id.«tcell» le = some (.Vptr bt Ptrofs.zero))
    (hen : PTree.get dense.id.numcells e = some (bnc, tint))
    (hez : PTree.get dense.id.«tcellsize» e = some (bz, tint))
    (hec : PTree.get dense.id.«tc» e = some (bc, tint))
    (hge : ∀ x ∈ [dense.id.«maketargetcell», dense.id.«nauty:g», dense.id.«nauty:tc_level»,
      dense.id.«nauty:digraph», dense.id.«nauty:dispatch», dense.id.«nauty:m», dense.id.«nauty:n»,
      dense.id.«nauty:getcanon», dense.id.«nauty:comp_canon», dense.id.«nauty:eqlev_first»,
      dense.id.«nauty:firsttc», dense.id.«nauty:stats»], PTree.get x e = none)
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc))) (hncl : nc ≤ n)
    (ht : ∃ v, ArrayAt m .Mint64 bt 0 v S.M) (hz : ∃ v, ArrayAt m .Mint32 bz 0 v 1)
    (hc : ArrayAt m .Mint32 bc 0 (fun _ => .Vint (ir (-1))) 1)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hl1 : 1 ≤ level) (hln : level ≤ n)
    (hnt : nc < n → ∃ x < n, level < st.ptn[x]!)
    (hQ : ∀ le' m',
      SearchAt m' S ctx (chooseTarget false ctx 100 level nc st).2.2.2 pre nsp →
      ArrayAt m' .Mint32 bc 0 (fun _ => .Vint (ir (chooseTarget false ctx 100 level nc st).1)) 1 →
      (chooses level nc st →
        (∃ ws, ArrayAt m' .Mint64 bt 0 (longs ws) S.M ∧
          SetRep (fun w => bv64 (ws w)) S.M (chooseTarget false ctx 100 level nc st).2.1) ∧
        ArrayAt m' .Mint32 bz 0
          (fun _ => .Vint (ir ((chooseTarget false ctx 100 level nc st).2.2.1 : Int))) 1) →
      (∃ v, ArrayAt m' .Mint64 bt 0 v S.M) → (∃ v, ArrayAt m' .Mint32 bz 0 v 1) →
      Unch m m' (fun z => S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = bt ∨ z = bz ∨
        z = bc) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → WorkMono m m' →
      (∀ z ∈ [bt, bz, bc], Keep m m' z) →
      (∀ x, x ≠ idOf 709 → x ≠ idOf 710 → x ≠ idOf 711 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp xi ge f chooseOff Q e le m := by
  have hge' := hge
  simp only [List.forall_mem_cons] at hge'
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, -⟩ := hge'
  simp only [chooseOff]
  wp_step; wp_step; wp_step
  refine wp_target h g7 g8 g9 g10 hen hncv hncl hlev hln ?_
  intro le1 h711 ho1
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, h711, Refine.tv, typeof, cop]
  by_cases hcho : chooses level nc st
  · rw [decide_eq_true hcho]
    simp only [ite_true]
    wp_step; wp_step; wp_step; wp_step
    refine wp_hint h g8 g9 ?_
    intro le2 h710 ho2
    simp only [seqPost, Post.after, E0_append]
    have hle2 : ∀ x, x ≠ idOf 710 → x ≠ idOf 711 → PTree.get x le2 = PTree.get x le :=
      fun x h1 h2 => by rw [ho2 x h1, ho1 x h2]
    have htc2 : PTree.get dense.id.«tcell» le2 = some (.Vptr bt Ptrofs.zero) := by
      rw [hle2 _ (by decide) (by decide)]; exact htc
    have hlab2 : PTree.get dense.id.«lab» le2 = some (.Vptr S.bl S.lofs) := by
      rw [hle2 _ (by decide) (by decide)]; exact hlab
    have hptn2 : PTree.get dense.id.«ptn» le2 = some (.Vptr S.bp S.pofs) := by
      rw [hle2 _ (by decide) (by decide)]; exact hptn
    have hlev2 : PTree.get dense.id.«level» le2 = some (.Vint (ir level)) := by
      rw [hle2 _ (by decide) (by decide)]; exact hlev
    apply wp_if_eval
    simp only [Exec.evalExpr, h710, Refine.tv, typeof, cop]
    have hnl := h.nlt
    have hI := h.inv
    have hlast : st.ptn[n - 1]! ≤ level := by have := hI.ptnLast; omega
    obtain ⟨x, hx, hgt⟩ := hnt hcho.1
    have ld : ∀ {m₁ : mem} {b : block} {v : val}, ArrayAt m₁ .Mint32 b 0 (fun _ => v) 1 →
        Mem.load .Mint32 m₁ b (zOfInt 0) = some v := fun hA => by
      have := hA.load 0 (by decide)
      simpa [elemOfs] using this
    have hgeT : ∀ x ∈ [dense.id.«maketargetcell», dense.id.«nauty:g», dense.id.«nauty:tc_level»,
        dense.id.«nauty:digraph», dense.id.«nauty:dispatch», dense.id.«nauty:m», dense.id.«nauty:n»],
        PTree.get x e = none := by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    -- after the call (and the reset): `stats->tctotal += tcellsize`
    have fin : ∀ (hint : Int) (st₂ : Search n) (m₂ : mem), hint < n →
        st₂.tctotal = st.tctotal →
        SearchAt m₂ S ctx st₂ pre nsp →
        (∃ ws, ArrayAt m₂ .Mint64 bt 0 (longs ws) S.M ∧
          SetRep (fun w => bv64 (ws w)) S.M (maketargetcell ctx st.lab st.ptn level 100 hint).2.1) →
        ArrayAt m₂ .Mint32 bz 0
          (fun _ => .Vint (ir ((maketargetcell ctx st.lab st.ptn level 100 hint).2.2 : Int))) 1 →
        ArrayAt m₂ .Mint32 bc 0
          (fun _ => .Vint (ir ((maketargetcell ctx st.lab st.ptn level 100 hint).1 : Int))) 1 →
        Unch m m₂ (fun z => S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z ∨ z = bt ∨ z = bz ∨
          z = bc) →
        (∀ z, Mem.valid_block m z → Mem.valid_block m₂ z) → WorkMono m m₂ →
        (∀ z ∈ [bt, bz, bc], Keep m m₂ z) →
        chooseTarget false ctx 100 level nc st =
          (((maketargetcell ctx st.lab st.ptn level 100 hint).1 : Int),
           (maketargetcell ctx st.lab st.ptn level 100 hint).2.1,
           (maketargetcell ctx st.lab st.ptn level 100 hint).2.2,
           { st₂ with tctotal := st₂.tctotal + (maketargetcell ctx st.lab st.ptn level 100 hint).2.2 }) →
        Wp xi ge f (Set.sk tcTotal) Q e le2 m₂ := by
      intro hint st₂ m₂ hh st₂t h₂ hT hZ hC hU₂ hg₂ hw₂ hK₂ hct
      obtain ⟨_, hsz⟩ := mtc_bounds ctx st.lab st.ptn level 100 hint hI.ptnSize hlast hh hx hgt
      wp_step; wp_step
      refine wp_tctotal h₂ g12 hez (ld hZ) (by omega) ?_
      intro m₃ h₃ hu₃ hg₃
      have hb : ∀ z ∈ [bt, bz, bc], z ∉ S.blocks := fun z hz => (hlocS z hz).1
      have nst : bt ≠ S.bst ∧ bz ≠ S.bst ∧ bc ≠ S.bst :=
        ⟨fun e => hb bt (by simp) (e ▸ by simp [SLoc.blocks]),
         fun e => hb bz (by simp) (e ▸ by simp [SLoc.blocks]),
         fun e => hb bc (by simp) (e ▸ by simp [SLoc.blocks])⟩
      have := hQ le2 m₃ (by rw [hct]; exact h₃) (by rw [hct]; exact hC.unch hu₃ nst.2.2)
        (fun _ => by
          rw [hct]
          obtain ⟨ws, hw, hr⟩ := hT
          exact ⟨⟨ws, hw.unch hu₃ nst.1, hr⟩, hZ.unch hu₃ nst.2.1⟩)
        (let ⟨ws, hw, _⟩ := hT; ⟨_, hw.unch hu₃ nst.1⟩) ⟨_, hZ.unch hu₃ nst.2.1⟩
        (hU₂.trans (hu₃.mono fun z hz => .inl (by subst hz; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩))) (fun z hz => hg₃ z (hg₂ z hz))
        (hw₂.trans hg₂ (WorkMono.of_unch h₂.work hu₃ (by simp only [workG]; sep_all h.distinct)
          fun z hz e => h₂.work_not hz (e ▸ by simp [SLoc.blocks])))
        (fun z hz => (hK₂ z hz).trans (Keep.unch hu₃ (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact nst.1
          · exact nst.2.1
          · exact nst.2.2)))
        (fun x h1 h2 h3 => by rw [ho2 x h2, ho1 x h3])
      exact this
    by_cases hcc : st.compCanon < 0
    · rw [decide_eq_true hcc]
      simp only [ite_true]
      have hft := hI.firsttcRange level (by omega)
      have hhint : Exec.evalExpr ge e le2 m (Alloc.gat dense.id.«nauty:firsttc» (Refine.tv dense.id.level)) =
          some (.Vint (ir st.firsttc[level]!)) :=
        Alloc.eval_gat g11 Program.find_nautyFirsttc
          (h.dyns.firsttc.ptr (by have := h.dyns.capTC; omega))
          h.arrays.firsttc (by omega) (Refine.tv dense.id.level) level (by omega) hlev2 rfl
      wp_step; wp_step; wp_step
      refine wp_nodeTarget h hvU hvT hloc hlocS htc2 hez hec hgeT ht hz ⟨_, hc⟩ hlab2 hptn2 hlev2 hl1 hln
        hhint rfl hft.1 hft.2 ⟨x, hx, hgt⟩ ?_
      intro m₁ h₁ hT hZ hC hU₁ hg₁ hw₁ hK₁
      obtain ⟨hpos, -⟩ := mtc_bounds ctx st.lab st.ptn level 100 st.firsttc[level]! hI.ptnSize hlast
        hft.2 hx hgt
      simp only [seqPost, Post.after, E0_append]
      wp_step; wp_step
      refine wp_tcReset h₁ g10 g11 hec (ld hC) (by omega) (by omega) hlev2 hl1 hln ?_
      intro m₂ h₂ hu₂ hg₂
      have hb : ∀ z ∈ [bt, bz, bc], z ∉ S.blocks := fun z hz => (hlocS z hz).1
      have nE : ∀ z ∈ [bt, bz, bc], z ≠ Block.eqlevFirst := fun z hz e =>
        hb z hz (e ▸ by simp [SLoc.blocks])
      simp only [seqPost, Post.after, E0_append]
      refine fin st.firsttc[level]! _ m₂ hft.2 (by split <;> rfl) h₂
        (let ⟨ws, hw, hr⟩ := hT; ⟨ws, hw.unch hu₂ (fun hm => nE bt (by simp) (by simpa using hm)), hr⟩)
        (hZ.unch hu₂ fun hm => nE bz (by simp) (by simpa using hm))
        (hC.unch hu₂ fun hm => nE bc (by simp) (by simpa using hm))
        (hU₁.trans (hu₂.mono fun z hz => .inl (by simp at hz; subst hz; exact ⟨by simp [SLoc.blocks], by sep_ne h.distinct, by sep_ne h.distinct⟩)))
        (fun z hz => hg₂ z (hg₁ z hz))
        (hw₁.trans hg₁ (WorkMono.of_unch h₁.work hu₂ (by simp only [workG]; sep_all h.distinct)
          fun z hz e => h₁.work_not hz (by simp at e; exact e ▸ by simp [SLoc.blocks])))
        (fun z hz => (hK₁ z hz).trans (Keep.unch hu₂ fun hm => nE z hz (by simpa using hm))) ?_
      rw [chooseTarget_false_eq, ite_eq_left hcho]
      simp only [offHint, hcc, ite_true, true_and]
      split <;> rfl
    · rw [decide_eq_false hcc]
      simp only [Bool.false_eq_true, ite_false]
      wp_step; wp_step
      refine wp_nodeTarget (hint := -1) h hvU hvT hloc hlocS htc2 hez hec hgeT ht hz ⟨_, hc⟩ hlab2 hptn2
        hlev2 hl1 hln (by simp [Exec.evalExpr, typeof, cop]) rfl (by decide) (by omega)
        ⟨x, hx, hgt⟩ ?_
      intro m₁ h₁ hT hZ hC hU₁ hg₁ hw₁ hK₁
      simp only [seqPost, Post.after, E0_append]
      refine fin (-1) st m₁ (by omega) rfl h₁ hT hZ hC hU₁ hg₁ hw₁ hK₁ ?_
      rw [chooseTarget_false_eq, ite_eq_left hcho]
      simp only [offHint, hcc, ite_false, false_and]
  · rw [decide_eq_false hcho]
    simp only [Bool.false_eq_true, ite_false]
    apply wp_skip
    have hct : chooseTarget false ctx 100 level nc st = ((-1 : Int), VSet.empty, 0, st) := by
      rw [chooseTarget_false_eq, ite_eq_right hcho]
    have := hQ le1 m (by rw [hct]; exact h) (by rw [hct]; exact hc) (fun hh => absurd hh hcho) ht hz
      (Unch.refl _ _) (fun _ hz => hz) (WorkMono.refl m) (fun z _ => Keep.refl m z)
      fun x h1 h2 h3 => ho1 x h3
    exact this

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)
open NautyVerified.Proofs.Maketargetcell (mtcOf)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}

/-- The size `mtcOf` gives is at most `n` when its position starts a nontrivial cell. -/
theorem mtcOf_size {n : Nat} {lab ptn : Array Nat} {level tc : Nat} (hs : ptn.size = n)
    (hlast : ptn[n - 1]! ≤ level) (h1 : tc < n) (h2 : level < ptn[tc]!) :
    (mtcOf n lab ptn level tc).2.2 ≤ n := by
  have hi1 : tc + 1 < n := by
    rcases Nat.lt_or_ge (tc + 1) n with h | h
    · exact h
    · have : tc = n - 1 := by omega
      subst this; omega
  have := (Spec.cellEnd_spec hs hi1 hlast).2.1
  simp only [mtcOf]
  omega

set_option maxHeartbeats 4000000 in
/-- `chooseOff` with `D`'s target-cell procedure: `chooseTargetG O false`'s state.
`htc` is what nautil.c's scan needs of `O.targetcell`'s position when a cell is
chosen. The calls may change `D`'s written globals, its scratch blocks in use
and new blocks. -/
theorem wp_chooseOffG {D : DispatchC ge O} {n : Nat} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {pre nsp : Bool} {level nc : Nat}
    (h : SearchAtG D.toDispatchRep m S gl cl G st pre nsp) (hvU : Mem.valid_block m S.bUA)
    (hvT : Mem.valid_block m E.tcnode0)
    {bnc bt bz bc : block}
    (hloc : [bt, bz, bc].Pairwise (· ≠ ·))
    (hlocS : ∀ z ∈ [bt, bz, bc], z ∉ S.blocksG D.toDispatchRep gl cl ∧ Mem.valid_block m z ∧
      ¬ IsWorkG D.toDispatchRep m z)
    (htcell : PTree.get dense.id.«tcell» le = some (.Vptr bt Ptrofs.zero))
    (hen : PTree.get dense.id.numcells e = some (bnc, tint))
    (hez : PTree.get dense.id.«tcellsize» e = some (bz, tint))
    (hec : PTree.get dense.id.«tc» e = some (bc, tint))
    (hge : ∀ x ∈ [dense.id.«maketargetcell», dense.id.«nauty:g», dense.id.«nauty:tc_level»,
      dense.id.«nauty:digraph», dense.id.«nauty:dispatch», dense.id.«nauty:m», dense.id.«nauty:n»,
      dense.id.«nauty:getcanon», dense.id.«nauty:comp_canon», dense.id.«nauty:eqlev_first»,
      dense.id.«nauty:firsttc», dense.id.«nauty:stats»], PTree.get x e = none)
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc))) (hncl : nc ≤ n)
    (ht : ∃ v, ArrayAt m .Mint64 bt 0 v S.M) (hz : ∃ v, ArrayAt m .Mint32 bz 0 v 1)
    (hc : ArrayAt m .Mint32 bc 0 (fun _ => .Vint (ir (-1))) 1)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hl1 : 1 ≤ level) (hln : level ≤ n)
    (htc : chooses level nc st →
      O.targetcell G st.lab st.ptn level 100 (offHint level st) < n ∧
        level < st.ptn[O.targetcell G st.lab st.ptn level 100 (offHint level st)]!)
    (hQ : ∀ le' m',
      SearchAtG D.toDispatchRep m' S gl cl G (chooseTargetG O false G 100 level nc st).2.2.2 pre nsp →
      ArrayAt m' .Mint32 bc 0
        (fun _ => .Vint (ir (chooseTargetG O false G 100 level nc st).1)) 1 →
      (chooses level nc st →
        (∃ ws, ArrayAt m' .Mint64 bt 0 (longs ws) S.M ∧
          SetRep (fun w => bv64 (ws w)) S.M (chooseTargetG O false G 100 level nc st).2.1) ∧
        ArrayAt m' .Mint32 bz 0
          (fun _ => .Vint (ir ((chooseTargetG O false G 100 level nc st).2.2.1 : Int))) 1) →
      (∃ v, ArrayAt m' .Mint64 bt 0 v S.M) → (∃ v, ArrayAt m' .Mint32 bz 0 v 1) →
      Unch m m' (fun z => S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m z ∨
        IsWorkG D.toDispatchRep m z ∨ z = bt ∨ z = bz ∨ z = bc) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → WorkMonoG D.toDispatchRep m m' →
      (∀ z ∈ [bt, bz, bc], Keep m m' z) →
      (∀ x, x ≠ idOf 709 → x ≠ idOf 710 → x ≠ idOf 711 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp xi ge f chooseOff Q e le m := by
  have hge' := hge
  simp only [List.forall_mem_cons] at hge'
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, -⟩ := hge'
  have mL : ∀ z ∈ S.litG, z ∈ S.blocksG D.toDispatchRep gl cl := fun z hz =>
    (S.litG_sub D.toDispatchRep gl cl).subset hz
  have hb : ∀ z ∈ [bt, bz, bc], z ∉ S.blocksG D.toDispatchRep gl cl := fun z hz => (hlocS z hz).1
  simp only [chooseOff]
  wp_step; wp_step; wp_step
  refine wp_targetG h g7 g8 g9 g10 hen hncv hncl hlev hln ?_
  intro le1 h711 ho1
  simp only [seqPost, Post.after, E0_append]
  apply wp_if_eval
  simp only [Exec.evalExpr, h711, Refine.tv, typeof, cop]
  by_cases hcho : chooses level nc st
  · rw [decide_eq_true hcho]
    simp only [ite_true]
    wp_step; wp_step; wp_step; wp_step
    refine wp_hintG h g8 g9 ?_
    intro le2 h710 ho2
    simp only [seqPost, Post.after, E0_append]
    have hle2 : ∀ x, x ≠ idOf 710 → x ≠ idOf 711 → PTree.get x le2 = PTree.get x le :=
      fun x h1 h2 => by rw [ho2 x h1, ho1 x h2]
    have htc2 : PTree.get dense.id.«tcell» le2 = some (.Vptr bt Ptrofs.zero) := by
      rw [hle2 _ (by decide) (by decide)]; exact htcell
    have hlab2 : PTree.get dense.id.«lab» le2 = some (.Vptr S.bl S.lofs) := by
      rw [hle2 _ (by decide) (by decide)]; exact hlab
    have hptn2 : PTree.get dense.id.«ptn» le2 = some (.Vptr S.bp S.pofs) := by
      rw [hle2 _ (by decide) (by decide)]; exact hptn
    have hlev2 : PTree.get dense.id.«level» le2 = some (.Vint (ir level)) := by
      rw [hle2 _ (by decide) (by decide)]; exact hlev
    apply wp_if_eval
    simp only [Exec.evalExpr, h710, Refine.tv, typeof, cop]
    have hnl := h.nlt
    have hI := h.inv
    have hlast : st.ptn[n - 1]! ≤ level := by have := hI.ptnLast; omega
    have ld : ∀ {m₁ : mem} {b : block} {v : val}, ArrayAt m₁ .Mint32 b 0 (fun _ => v) 1 →
        Mem.load .Mint32 m₁ b (zOfInt 0) = some v := fun hA => by
      have := hA.load 0 (by decide)
      simpa [elemOfs] using this
    have hgeT : ∀ x ∈ [dense.id.«maketargetcell», dense.id.«nauty:g», dense.id.«nauty:tc_level»,
        dense.id.«nauty:digraph», dense.id.«nauty:dispatch», dense.id.«nauty:m», dense.id.«nauty:n»],
        PTree.get x e = none := by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    have nst : bt ≠ S.bst ∧ bz ≠ S.bst ∧ bc ≠ S.bst :=
      ⟨fun e => hb bt (by simp) (e ▸ mL _ (by simp [SLoc.litG])),
       fun e => hb bz (by simp) (e ▸ mL _ (by simp [SLoc.litG])),
       fun e => hb bc (by simp) (e ▸ mL _ (by simp [SLoc.litG]))⟩
    -- after the call (and the reset): `stats->tctotal += tcellsize`
    have fin : ∀ (tc : Nat) (st₂ : SearchState n (O.Canon n)) (m₂ : mem), tc < n →
        level < st.ptn[tc]! → st₂.tctotal = st.tctotal →
        SearchAtG D.toDispatchRep m₂ S gl cl G st₂ pre nsp →
        (∃ ws, ArrayAt m₂ .Mint64 bt 0 (longs ws) S.M ∧
          SetRep (fun w => bv64 (ws w)) S.M (mtcOf n st.lab st.ptn level tc).2.1) →
        ArrayAt m₂ .Mint32 bz 0
          (fun _ => .Vint (ir ((mtcOf n st.lab st.ptn level tc).2.2 : Int))) 1 →
        ArrayAt m₂ .Mint32 bc 0
          (fun _ => .Vint (ir ((mtcOf n st.lab st.ptn level tc).1 : Int))) 1 →
        Unch m m₂ (fun z => S.ChgG D.toDispatchRep gl cl z ∨ ¬ Mem.valid_block m z ∨
          IsWorkG D.toDispatchRep m z ∨ z = bt ∨ z = bz ∨ z = bc) →
        (∀ z, Mem.valid_block m z → Mem.valid_block m₂ z) → WorkMonoG D.toDispatchRep m m₂ →
        (∀ z ∈ [bt, bz, bc], Keep m m₂ z) →
        chooseTargetG O false G 100 level nc st =
          (((mtcOf n st.lab st.ptn level tc).1 : Int), (mtcOf n st.lab st.ptn level tc).2.1,
           (mtcOf n st.lab st.ptn level tc).2.2,
           { st₂ with tctotal := st₂.tctotal + (mtcOf n st.lab st.ptn level tc).2.2 }) →
        Wp xi ge f (Set.sk tcTotal) Q e le2 m₂ := by
      intro tc st₂ m₂ htn htl st₂t h₂ hT hZ hC hU₂ hg₂ hw₂ hK₂ hct
      have hsz := mtcOf_size (lab := st.lab) hI.ptnSize hlast htn htl
      wp_step; wp_step
      refine wp_tctotalG h₂ g12 hez (ld hZ) (by omega) ?_
      intro m₃ h₃ hu₃ hg₃
      have hw₃ := (SStepG.of_unch h₂ hu₃ hg₃
        (fun z hz => .inl (by subst hz; exact ⟨mL _ (by simp [SLoc.litG]), by sep_ne h.lit,
          by sep_ne h.lit⟩))
        (fun z hz e => h.lit_globs S.bst (by simp [SLoc.litG]) (e ▸ D.wglobs_sub _ hz))
        ⟨(by sep_ne h.lit : E.nautilWorkperm ≠ S.bst),
          (by sep_ne h.lit : E.nautilWorkpermSz ≠ S.bst)⟩).2
      exact hQ le2 m₃ (by rw [hct]; exact h₃) (by rw [hct]; exact hC.unch hu₃ nst.2.2)
        (fun _ => by
          rw [hct]
          obtain ⟨ws, hw, hr⟩ := hT
          exact ⟨⟨ws, hw.unch hu₃ nst.1, hr⟩, hZ.unch hu₃ nst.2.1⟩)
        (let ⟨ws, hw, _⟩ := hT; ⟨_, hw.unch hu₃ nst.1⟩) ⟨_, hZ.unch hu₃ nst.2.1⟩
        (hU₂.trans (hu₃.mono fun z hz => .inl (by
          subst hz; exact ⟨mL _ (by simp [SLoc.litG]), by sep_ne h.lit, by sep_ne h.lit⟩)))
        (fun z hz => hg₃ z (hg₂ z hz)) (hw₂.trans hg₂ hw₃)
        (fun z hz => (hK₂ z hz).trans (Keep.unch hu₃ (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact nst.1
          · exact nst.2.1
          · exact nst.2.2)))
        (fun x h1 h2 h3 => by rw [ho2 x h2, ho1 x h3])
    obtain ⟨htn, htl⟩ := htc hcho
    by_cases hcc : st.compCanon < 0
    · rw [decide_eq_true hcc]
      simp only [ite_true]
      have hoh : offHint level st = st.firsttc[level]! := by simp [offHint, hcc]
      rw [hoh] at htn htl
      have hft := hI.firsttcRange level (by omega)
      have hhint : Exec.evalExpr ge e le2 m
          (Alloc.gat dense.id.«nauty:firsttc» (Refine.tv dense.id.level)) =
          some (.Vint (ir st.firsttc[level]!)) :=
        Alloc.eval_gat g11 E.find_nautyFirsttc
          (h.dyns.firsttc.ptr (by have := h.dyns.capTC; omega))
          h.arrays.firsttc (by omega) (Refine.tv dense.id.level) level (by omega) hlev2 rfl
      wp_step; wp_step; wp_step
      refine wp_nodeTargetG h hvU hvT hloc hlocS htc2 hez hec hgeT ht hz ⟨_, hc⟩ hlab2 hptn2 hlev2
        hl1 hln hhint rfl hft.1 hft.2 ⟨htn, htl⟩ ?_
      intro m₁ h₁ hT hZ hC hU₁ hg₁ hw₁ hK₁
      simp only [seqPost, Post.after, E0_append]
      wp_step; wp_step
      refine wp_tcResetG h₁ g10 g11 hec (ld hC) (by omega) (by simp only [mtcOf]; omega) hlev2 hl1
        hln ?_
      intro m₂ h₂ hu₂ hg₂
      have nE : ∀ z ∈ [bt, bz, bc], z ≠ E.eqlevFirst := fun z hz e =>
        hb z hz (e ▸ mL _ (by simp [SLoc.litG]))
      have hw₂ := (SStepG.of_unch h₁ hu₂ hg₂
        (fun z hz => .inl (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          subst hz; exact ⟨mL _ (by simp [SLoc.litG]), by sep_ne h.lit, by sep_ne h.lit⟩))
        (fun z hz e => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at e
          exact h.lit_globs E.eqlevFirst (by simp [SLoc.litG]) (e ▸ D.wglobs_sub _ hz))
        ⟨fun e => (by sep_ne h.lit : E.nautilWorkperm ≠ E.eqlevFirst) (by simpa using e),
          fun e => (by sep_ne h.lit : E.nautilWorkpermSz ≠ E.eqlevFirst) (by simpa using e)⟩).2
      simp only [seqPost, Post.after, E0_append]
      refine fin _ _ m₂ htn htl (by split <;> rfl) h₂
        (let ⟨ws, hw, hr⟩ := hT; ⟨ws, hw.unch hu₂ (fun hm => nE bt (by simp) (by simpa using hm)), hr⟩)
        (hZ.unch hu₂ fun hm => nE bz (by simp) (by simpa using hm))
        (hC.unch hu₂ fun hm => nE bc (by simp) (by simpa using hm))
        (hU₁.trans (hu₂.mono fun z hz => .inl (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
          subst hz; exact ⟨mL _ (by simp [SLoc.litG]), by sep_ne h.lit, by sep_ne h.lit⟩)))
        (fun z hz => hg₂ z (hg₁ z hz)) (hw₁.trans hg₁ hw₂)
        (fun z hz => (hK₁ z hz).trans (Keep.unch hu₂ fun hm => nE z hz (by simpa using hm))) ?_
      rw [chooseTargetG_false_eq, ite_eq_left hcho]
      simp only [offHint, hcc, ite_true, true_and]
      split <;> rfl
    · rw [decide_eq_false hcc]
      simp only [Bool.false_eq_true, ite_false]
      have hoh : offHint level st = -1 := by simp [offHint, hcc]
      rw [hoh] at htn htl
      wp_step; wp_step
      refine wp_nodeTargetG (hint := -1) h hvU hvT hloc hlocS htc2 hez hec hgeT ht hz ⟨_, hc⟩ hlab2
        hptn2 hlev2 hl1 hln (by simp [Exec.evalExpr, typeof, cop]) rfl (by decide) (by omega)
        ⟨htn, htl⟩ ?_
      intro m₁ h₁ hT hZ hC hU₁ hg₁ hw₁ hK₁
      simp only [seqPost, Post.after, E0_append]
      refine fin _ st m₁ htn htl rfl h₁ hT hZ hC hU₁ hg₁ hw₁ hK₁ ?_
      rw [chooseTargetG_false_eq, ite_eq_left hcho]
      simp only [offHint, hcc, ite_false, false_and]
  · rw [decide_eq_false hcho]
    simp only [Bool.false_eq_true, ite_false]
    apply wp_skip
    have hct : chooseTargetG O false G 100 level nc st = ((-1 : Int), VSet.empty, 0, st) := by
      rw [chooseTargetG_false_eq, ite_eq_right hcho]
    exact hQ le1 m (by rw [hct]; exact h) (by rw [hct]; exact hc) (fun hh => absurd hh hcho) ht hz
      (Unch.refl _ _) (fun _ hz => hz) (WorkMonoG.refl m) (fun z _ => Keep.refl m z)
      fun x h1 h2 h3 => ho1 x h3

end Generic

end NautyVerified.Proofs.Search

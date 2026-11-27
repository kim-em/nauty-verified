import NautyVerified.Proofs.Fmperm.Cycle

/-!
# The main loop of `fmperm`

`wp_vertex`: one iteration of `fmperm`'s loop, for vertex `i`, turns the
sets `fix`, `mcr` and the `workperm` marks into HexGraphIso's `permStep`.
-/

namespace NautyVerified.Proofs.Fmperm

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Spec
open NautyVerified.Proofs.Set (longs addW BitTable)
open NautyVerified.Proofs.Alloc (gat eval_gat wp_gstore)
open Hex.GraphIso.Nauty (VSet)

variable {xi : ExternalCalls}

/-- The state of `fmperm`'s loop: sets `fix` and `mcr` (words `wf`, `wm`)
representing `s.1`, `s.2.1`, and `workperm` holding the marks `s.2.2`. -/
structure St (m : mem) (le : temp_env) (b bf : block) (fofs : ptrofs) (bm : block) (mofs : ptrofs)
    (n M : Nat) (wf wm : Nat → Lib.Integers.int64) (s : VSet n × VSet n × Array Bool) : Prop where
  hfix : PTree.get id.fix le = some (.Vptr bf fofs)
  hmcr : PTree.get id.mcr le = some (.Vptr bm mofs)
  farr : ArrayAt m .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf) M
  marr : ArrayAt m .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm) M
  frep : SetRep (fun w => bv64 (wf w)) M s.1
  mrep : SetRep (fun w => bv64 (wm w)) M s.2.1
  warr : ArrayAt m .Mint32 b 0 (seenVals s.2.2) n
  ssize : s.2.2.size = n
  bit : BitTable m Block.nautilBit
  Mlt : M < 2147483648
  nM : n ≤ 64 * M

/-- The blocks of `fmperm`'s arrays are distinct. -/
structure Disj (n : Nat) (bpm b bf bm : block) : Prop where
  fm : bf ≠ bm
  fp : bf ≠ bpm
  mp : bm ≠ bpm
  fb : 0 < n → bf ≠ b
  mb : 0 < n → bm ≠ b
  wf : Block.nautilWorkperm ≠ bf
  wm : Block.nautilWorkperm ≠ bm
  bitf : Block.nautilBit ≠ bf
  bitm : Block.nautilBit ≠ bm
  bitb : 0 < n → Block.nautilBit ≠ b

theorem Frame.temps {m : mem} {le le' : temp_env} {bpm : block} {pofs : ptrofs} {b : block}
    {perm : Array Nat} {n : Nat} (h : Frame m le bpm pofs b perm n)
    (hle : ∀ x, x ≠ id.i → x ≠ id.k → x ≠ id.l → PTree.get x le' = PTree.get x le) :
    Frame m le' bpm pofs b perm n :=
  { h with
    hperm := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hperm
    hn := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hn }

theorem Frame.unch {m m' : mem} {le : temp_env} {bpm : block} {pofs : ptrofs} {b : block}
    {perm : Array Nat} {n : Nat} (h : Frame m le bpm pofs b perm n) {S : block → Prop}
    (hu : Unch m m' S) (hp : ¬ S bpm) (hw : ¬ S Block.nautilWorkperm) :
    Frame m' le bpm pofs b perm n :=
  { h with
    parr := h.parr.unch hu hp
    wpPtr := fun hn => by rw [hu.load _ _ _ hw]; exact h.wpPtr hn }

theorem St.temps {m : mem} {le le' : temp_env} {b bf : block} {fofs : ptrofs} {bm : block}
    {mofs : ptrofs} {n M : Nat} {wf wm : Nat → Lib.Integers.int64} {s : VSet n × VSet n × Array Bool}
    (h : St m le b bf fofs bm mofs n M wf wm s)
    (hle : ∀ x, x ≠ id.i → x ≠ id.k → x ≠ id.l → PTree.get x le' = PTree.get x le) :
    St m le' b bf fofs bm mofs n M wf wm s :=
  { h with
    hfix := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hfix
    hmcr := by rw [hle _ (by decide) (by decide) (by decide)]; exact h.hmcr }

theorem wp_vertex {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bpm : block}
    {pofs : ptrofs} {b bf : block} {fofs : ptrofs} {bm : block} {mofs : ptrofs}
    {perm : Array Nat} {n M i0 : Nat} {wf wm : Nat → Lib.Integers.int64}
    {s : VSet n × VSet n × Array Bool}
    (h : Frame m le bpm pofs b perm n) (hs : St m le b bf fofs bm mofs n M wf wm s)
    (hd : Disj n bpm b bf bm) (he : PTree.get Set.bit e = none) (hge : PTree.get id.wp e = none)
    (hi : PTree.get id.i le = some (.Vint (ir i0))) (hi0 : i0 < n)
    (hQ : ∀ le' m' wf' wm', Frame m' le' bpm pofs b perm n →
      St m' le' b bf fofs bm mofs n M wf' wm' (permStep perm s i0) →
      Unch m m' (fun z => z = b ∨ z = bf ∨ z = bm) →
      (∀ x, x ≠ id.k → x ≠ id.l → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f step Q e le m := by
  have hnlt := h.nlt
  have hnM := hs.nM
  have hpi := h.psmall i0 hi0
  have hpe := eval_at (ge := ge) (e := e) h.parr h.nlt id.perm h.hperm (tv id.i) i0 hi0 hi rfl
  wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, hpe, show Exec.evalExpr ge e le m (tv id.i) = _ from hi]
  simp only [ints, typeof, cop]
  rw [ir_eq (a := (perm[i0]! : Int)) (b := (i0 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hfx : perm[i0]! = i0
  · rw [ite_eq_left (by simp; omega)]
    wp_step
    refine Set.wp_addElement hs.farr hs.Mlt hs.hfix hi rfl (by omega) (by omega) hs.bit he ?_
    intro m1 harr1 hu1
    refine Set.wp_addElement (hs.marr.unch hu1 (Ne.symm hd.fm)) hs.Mlt hs.hmcr hi rfl (by omega)
      (by omega) (hs.bit.unch hu1 hd.bitf) he ?_
    intro m2 harr2 hu2
    have hps : permStep perm s i0 = (s.1.insert i0, s.2.1.insert i0, s.2.2) := by
      simp [permStep, hfx]
    refine hQ le m2 (addW wf i0) (addW wm i0) ((h.unch hu1 (Ne.symm hd.fp) hd.wf).unch hu2 (Ne.symm hd.mp) hd.wm) ?_
      ((hu1.mono fun z hz => .inr (.inl hz)).trans (hu2.mono fun z hz => .inr (.inr hz)))
      (fun _ _ _ => rfl)
    rw [hps]
    exact { hs with
      farr := harr1.unch hu2 hd.fm
      marr := harr2
      frep := Set.setRep_add hs.frep hi0
      mrep := Set.setRep_add hs.mrep hi0
      warr := (hs.warr.unch hu1 (Ne.symm (hd.fb (by omega)))).unch hu2 (Ne.symm (hd.mb (by omega)))
      bit := (hs.bit.unch hu1 hd.bitf).unch hu2 hd.bitm }
  · rw [ite_eq_right (by simp; omega)]
    have hwe := eval_gat hge find_nautilWorkperm (h.wpPtr (by omega)) hs.warr h.nlt (tv id.i) i0 hi0
      hi rfl
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hwe]
    simp only [seenVals, Exec.evalExpr, typeof, cop]
    by_cases hseen : s.2.2[i0]! = true
    · rw [ite_eq_left hseen]
      rw [ir_eq (a := 1) (b := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
      try simp only [cop]
      rw [ite_eq_right (by decide)]
      apply wp_skip
      have hps : permStep perm s i0 = s := by simp [permStep, hfx, hseen]
      rw [← hps] at hs
      exact hQ le m wf wm h hs (Unch.refl _ _) (fun _ _ _ => rfl)
    · rw [ite_eq_right hseen]
      rw [ir_eq (a := 0) (b := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
      try simp only [cop]
      rw [ite_eq_left (by decide)]
      rw [cycle_eq]
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [show Exec.evalExpr ge e le m (tv id.i) = _ from hi]
      let le1 := PTree.set id.l (.Vint (ir (i0 : Int))) le
      have ho1 : ∀ x, x ≠ id.l → PTree.get x le1 = PTree.get x le := fun x hx => temps_gso _ _ hx
      have hf1 : Frame m le1 bpm pofs b perm n := h.temps fun x _ _ h3 => ho1 x h3
      wp_step
      refine wp_walk hf1 hge hs.warr hs.ssize (by rw [ho1 _ (by decide)]; exact hi) (temps_gss _ _ _)
        hi0 ?_
      intro le2 m2 harr2 hu2 ho2
      have hoth : ∀ x, x ≠ id.k → x ≠ id.l → PTree.get x le2 = PTree.get x le := fun x h1 h2 => by
        rw [ho2 x h1 h2, ho1 x h2]
      have hi2 : PTree.get id.i le2 = some (.Vint (ir i0)) := by rw [hoth _ (by decide) (by decide)]; exact hi
      have hmcr2 : PTree.get id.mcr le2 = some (.Vptr bm mofs) := by
        rw [hoth _ (by decide) (by decide)]; exact hs.hmcr
      refine Set.wp_addElement (hs.marr.unch hu2 (hd.mb (by omega))) hs.Mlt hmcr2 hi2 rfl (by omega)
        (by omega) (hs.bit.unch hu2 (hd.bitb (by omega))) he ?_
      intro m3 harr3 hu3
      have hps : permStep perm s i0 = (s.1, s.2.1.insert i0, mark perm i0 (List.range n) s.2.2 i0) := by
        simp [permStep, hfx, hseen]
      refine hQ le2 m3 wf (addW wm i0) (((h.temps fun x _ h2 h3 => hoth x h2 h3).unch hu2
          (h.bpm_b (by omega)) (h.wp_b (by omega))).unch hu3 (Ne.symm hd.mp) hd.wm) ?_
        ((hu2.mono fun z hz => .inl hz).trans (hu3.mono fun z hz => .inr (.inr hz))) hoth
      rw [hps]
      exact { hfix := by rw [hoth _ (by decide) (by decide)]; exact hs.hfix
              hmcr := hmcr2
              farr := (hs.farr.unch hu2 (hd.fb (by omega))).unch hu3 hd.fm
              marr := harr3
              frep := hs.frep
              mrep := Set.setRep_add hs.mrep hi0
              warr := harr2.unch hu3 (Ne.symm (hd.mb (by omega)))
              ssize := by
                show (mark perm i0 (List.range n) s.2.2 i0).size = n
                rw [mark_size]; exact hs.ssize
              bit := (hs.bit.unch hu2 (hd.bitb (by omega))).unch hu3 hd.bitm
              Mlt := hs.Mlt
              nM := hs.nM }

theorem foldl_range_succ {β : Type} (f : β → Nat → β) (b : β) (k : Nat) :
    (List.range (k + 1)).foldl f b = f ((List.range k).foldl f b) k := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem wp_main {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bpm : block}
    {pofs : ptrofs} {b bf : block} {fofs : ptrofs} {bm : block} {mofs : ptrofs}
    {perm : Array Nat} {n M : Nat} {wf wm : Nat → Lib.Integers.int64}
    (h : Frame m le bpm pofs b perm n)
    (hs : St m le b bf fofs bm mofs n M wf wm (VSet.empty, VSet.empty, Array.replicate n false))
    (hd : Disj n bpm b bf bm) (he : PTree.get Set.bit e = none) (hge : PTree.get id.wp e = none)
    (hQ : ∀ le' m' wf' wm', Frame m' le' bpm pofs b perm n →
      St m' le' b bf fofs bm mofs n M wf' wm'
        ((List.range n).foldl (permStep perm) (VSet.empty, VSet.empty, Array.replicate n false)) →
      Unch m m' (fun z => z = b ∨ z = bf ∨ z = bm) →
      (∀ x, x ≠ id.i → x ≠ id.k → x ≠ id.l → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp xi ge f (forLoop id.i id.n step) Q e le m := by
  let s0 : VSet n × VSet n × Array Bool := (VSet.empty, VSet.empty, Array.replicate n false)
  let sk := fun k => (List.range k).foldl (permStep perm) s0
  let Oth := fun le' : temp_env =>
    ∀ x, x ≠ id.i → x ≠ id.k → x ≠ id.l → PTree.get x le' = PTree.get x le
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) => k ≤ n ∧
    PTree.get id.i le' = some (.Vint (ir k)) ∧ ∃ wf' wm', Frame m' le' bpm pofs b perm n ∧
      St m' le' b bf fofs bm mofs n M wf' wm' (sk k) ∧ Unch m m' (fun z => z = b ∨ z = bf ∨ z = bm) ∧
      Oth le'
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    PTree.get id.i le' = some (.Vint (ir k)) ∧ k < n ∧ ∃ wf' wm', Frame m' le' bpm pofs b perm n ∧
      St m' le' b bf fofs bm mofs n M wf' wm' (sk (k + 1)) ∧
      Unch m m' (fun z => z = b ∨ z = bf ∨ z = bm) ∧ Oth le'
  refine wp_forLoop id.i id.n step n h.nlt Inv Mid ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, wf', wm', hf, -, -, -⟩
    exact ⟨hk, hi, hf.hn⟩
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, wf, wm, h.temps fun x hx _ _ => temps_gso _ _ hx,
      hs.temps fun x hx _ _ => temps_gso _ _ hx, Unch.refl _ _, fun x hx _ _ => temps_gso _ _ hx⟩
  · rintro k le' m' hk ⟨-, hi, wf', wm', hf, hs', hu, ho⟩
    refine wp_vertex hf hs' hd he hge hi hk ?_
    intro le2 m2 wf2 wm2 hf2 hs2 hu2 ho2
    refine ⟨rfl, ?_, hk, wf2, wm2, hf2, ?_, hu.trans hu2, fun x h1 h2 h3 => by rw [ho2 x h2 h3, ho x h1 h2 h3]⟩
    · rw [ho2 _ (by decide) (by decide)]; exact hi
    · show St m2 le2 b bf fofs bm mofs n M wf2 wm2 ((List.range (k + 1)).foldl (permStep perm) s0)
      rw [foldl_range_succ]; exact hs2
  · rintro k le' m' ⟨hi, hk, wf', wm', hf, hs', hu, ho⟩
    refine ⟨hi, by omega, temps_gss _ _ _, wf', wm', hf.temps fun x hx _ _ => temps_gso _ _ hx,
      hs'.temps fun x hx _ _ => temps_gso _ _ hx, hu, fun x h1 h2 h3 => by
        rw [temps_gso _ _ h1, ho x h1 h2 h3]⟩
  · rintro le' m' ⟨-, -, wf', wm', hf, hs', hu, ho⟩
    exact hQ le' m' wf' wm' hf hs' hu ho

end NautyVerified.Proofs.Fmperm

import NautyVerified.Proofs.Search.Node.FirstVertex
import NautyVerified.Proofs.Search.Node.OtherLoop

/-!
# `firstpathnode0`'s child loop

`wp_fpnLoop`: the loop over the target cell runs HexGraphIso's first-path
`sweep` from the cursor `tv1` with the full cell fuel `n + 1`, emitting
`sweepEmFirst`. It either finishes (the sweep's `.done`, with the final index
and state) or returns the target of an unwind below `level`.

The invariant `FInv` at fuel `k`: the memory is in `LoopAt` for the sweep's
state, cell and index so far, the temporaries hold them, the sweep from here
gives the final result `R`, and the words emitted so far followed by what the
rest of the sweep emits are the node's.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso Hex.GraphIso.Nauty
open NautyVerified.Spec.SearchInf (NodeOk nautyInfinity)

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-- The sweep from a cursor, with nauty's pinned constants. -/
abbrev fSweep (L : LCtx n) (tv1 k : Nat) (c : Option Nat) (cell : VSet n) (idx : Nat)
    (st : Search n) : Exit × Nat × Search n :=
  sweep true L.ctx nautyInf 100 (nodeFuel n (L.level + 1)) k L.level L.nc L.tc tv1 c cell idx st

/-- What the sweep emits from a cursor. -/
abbrev fSweepEm (Em : Bool → Nat → Nat → Search n → List Int) (L : LCtx n) (tv1 k : Nat)
    (c : Option Nat) (cell : VSet n) (st : Search n) : List Int :=
  sweepEmFirst Em L.ctx L.level L.nc L.tc tv1 k c cell st

/-- `if (orbits[tv] == tv1) ++index;` -/
theorem wp_fpnIndex {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hge : PTree.get dense.id.«nauty:orbits» e = none) {v tv1 idx : Nat}
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v))) (hv : v < n)
    (htv1 : PTree.get dense.id.«tv1» le = some (.Vint (ir tv1))) (htv1n : tv1 < n)
    (hidx : PTree.get dense.id.«index» le = some (.Vint (ir idx)))
    (hQ : ∀ le', PTree.get dense.id.«index» le' =
        some (.Vint (ir ((if st.orbits[v]! == tv1 then idx + 1 else idx : Nat) : Int))) →
      (∀ x, x ≠ dense.id.«index» → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m) :
    Wp xi ge f indexIf Q e le m := by
  have hnl := h.nlt
  apply wp_if_eval
  rw [Processnode.eval_eqI (x := (st.orbits[v]! : Int)) (y := (tv1 : Int))
    (eval_orbAt h hge htv hv) (by simp [Exec.evalExpr, Refine.tv, htv1]) rfl rfl
    ⟨by omega, by have := h.inv.orbitsSmall v hv; omega⟩ ⟨by omega, by omega⟩]
  by_cases ho : st.orbits[v]! = tv1
  · rw [decide_eq_true (by omega)]
    simp only [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m = some true from rfl, ite_true]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hidx, typeof, cop]
    refine hQ _ ?_ fun x hx => temps_gso _ _ hx
    rw [temps_gss]
    simp [ho]
  · rw [decide_eq_false (by omega)]
    simp only [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl,
      Bool.false_eq_true, ite_false]
    apply wp_skip
    exact hQ le (by simp [ho, hidx]) fun _ _ => rfl

/-- The loop invariant at the head of the loop, with fuel `k` left. -/
def FInv {k0 : Nat} (G : Colored n k0) (Em : Bool → Nat → Nat → Search n → List Int) (L : LCtx n)
    (tv1 : Nat) (R : Exit × Nat × Search n) (Lem : List Int) (k : Nat) (t : trace)
    (le : temp_env) (m : mem) : Prop :=
  ∃ (c : Option Nat) (cl : VSet n) (s : Search n) (idx : Nat) (pre : Bool) (ch : List (block × block)),
    LoopAt L m s pre false cl ch ∧ FTemps le L tv1 ∧
    PTree.get dense.id.«tv» le = some (.Vint (ir (curVal c))) ∧
    PTree.get dense.id.«index» le = some (.Vint (ir idx)) ∧ idx + k ≤ n + 1 ∧
    (pre = true → c = some tv1) ∧ SweepOkFirst G L.level L.nc L.tc tv1 cl c s ∧
    fSweep L tv1 k c cl idx s = R ∧ ∃ l, Emits t l ∧ l ++ fSweepEm Em L tv1 k c cl s = Lem

/-- After a vertex, before the cursor moves. -/
def FMid {k0 : Nat} (G : Colored n k0) (Em : Bool → Nat → Nat → Search n → List Int) (L : LCtx n)
    (tv1 : Nat) (R : Exit × Nat × Search n) (Lem : List Int) (k : Nat) (t : trace)
    (le : temp_env) (m : mem) : Prop :=
  ∃ (v : Nat) (cl : VSet n) (s : Search n) (idx k' : Nat) (ch : List (block × block)),
    k = k' + 1 ∧ LoopAt L m s false false cl ch ∧ FTemps le L tv1 ∧
    PTree.get dense.id.«tv» le = some (.Vint (ir v)) ∧ v < n ∧
    PTree.get dense.id.«index» le = some (.Vint (ir idx)) ∧ idx + k' ≤ n + 1 ∧
    SweepOkFirst G L.level L.nc L.tc tv1 cl (cl.nextElem (some v)) s ∧
    fSweep L tv1 k' (cl.nextElem (some v)) cl idx s = R ∧
    ∃ l, Emits t l ∧ l ++ fSweepEm Em L tv1 k' (cl.nextElem (some v)) cl s = Lem

theorem fSweepEm_succ (Em : Bool → Nat → Nat → Search n → List Int) (L : LCtx n) (tv1 k v : Nat)
    (cl : VSet n) (s : Search n) :
    fSweepEm Em L tv1 (k + 1) (some v) cl s = vertexEm (k := 0) Em L.level L.nc L.tc tv1 v s ++
      match fChild L tv1 v cl s with
      | (.done, cl', s') => fSweepEm Em L tv1 k (cl'.nextElem (some v)) cl' s'
      | _ => [] := by
  simp only [fSweepEm, sweepEmFirst, vertexEm, fChild]
  rfl

theorem fSweep_succ (L : LCtx n) (tv1 k v : Nat) (cl : VSet n) (idx : Nat) (s : Search n) :
    fSweep L tv1 (k + 1) (some v) cl idx s =
      match fChild L tv1 v cl s with
      | (.done, cl', s') => fSweep L tv1 k (cl'.nextElem (some v)) cl'
          (if s'.orbits[v]! == tv1 then idx + 1 else idx) s'
      | (e, _, s') => (e, idx, s') :=
  sweep_true_some _ _ _ _ _ _ _ _ _ _ _ _ _

theorem fSweep_none (L : LCtx n) (tv1 k : Nat) (cl : VSet n) (idx : Nat) (s : Search n) :
    fSweep L tv1 k none cl idx s = (.done, idx, s) :=
  sweep_true_none _ _ _ _ _ _ _ _ _ _ _ _

theorem fSweepEm_none (Em : Bool → Nat → Nat → Search n → List Int) (L : LCtx n) (tv1 k : Nat)
    (cl : VSet n) (s : Search n) : fSweepEm Em L tv1 k none cl s = [] := by
  cases k <;> rfl

theorem fChild_eta (L : LCtx n) (tv1 v : Nat) (cl : VSet n) (s : Search n) :
    fChild L tv1 v cl s = ((fChild L tv1 v cl s).1, (fChild L tv1 v cl s).2.1,
      (fChild L tv1 v cl s).2.2) := rfl

set_option maxHeartbeats 8000000 in
/-- `firstpathnode0`'s child loop runs the first-path sweep. -/
theorem wp_fpnLoop {k0 : Nat} {G : Colored n k0} {Em : Bool → Nat → Nat → Search n → List Int}
    {f : function} {Q : Post} {e : env} (L : LCtx n) {tv1 : Nat} {R : Exit × Nat × Search n}
    {Lem : List Int} (hE : FEnv e L) (hfr : f.fn_return = tint) (hn0 : 0 < n)
    (hn : n + 2 < nautyInfinity)
    (hRecF : ∀ st' ch', Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpec xi (NodeOk G) Em L.S L.ctx st' (L.level + 1) (L.nc + 1) ch'))
    (hRecO : ∀ st' ch', Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpec xi (NodeOk G) Em L.S L.ctx st' (L.level + 1) (L.nc + 1) ch'))
    (hcb : AutomCb xi L.S.bUA) (hln : L.level + 1 ≤ n) (hncl : L.nc + 1 ≤ n) (htv1n : tv1 < n)
    (hRf : R.1 ≠ .fuel)
    (hQn : ∀ t le' m' cl ch, R.1 = .done → Emits t Lem → LoopAt L m' R.2.2 false false cl ch →
      FTemps le' L tv1 → PTree.get dense.id.«index» le' = some (.Vint (ir R.2.1)) →
      R.2.1 ≤ n + 1 → Q.normal t e le' m')
    (hQr : ∀ t m' cl ch target short, R.1 = .unwind target short → target < L.level →
      LoopAt L m' R.2.2 false short cl ch → Emits t Lem →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret t (.Vint (ir target)) m''
      | none => False)
    {k : Nat} {le : temp_env} {m : mem} (hI : FInv G Em L tv1 R Lem k E0 le m) :
    Wp xi ge f Firstpathnode.childLoop Q e le m := by
  rw [fpnLoop_eq]
  refine wp_loop (I := fun c t e' le m => e' = e ∧ FInv G Em L tv1 R Lem c t le m)
    (J := fun c t e' le m => e' = e ∧ FMid G Em L tv1 R Lem c t le m) ?_ ?_ ⟨rfl, hI⟩
  · -- the body
    intro c t e' le' m' ⟨rfl, cur, cl, s, idx, pre, ch, hL, hT, htv, hidx, hik, hpre, hok, hsw, l,
      hl, hlem⟩
    have hnl := hL.search.nlt
    have hcurlt : ∀ v, cur = some v → v < n := fun v hv => by
      subst hv; exact hok.pos.1
    wp_step; wp_step; wp_step
    refine Processnode.wp_ifB (Processnode.eval_geI (x := curVal cur) (y := 0) htv rfl rfl rfl
      (curVal_in hcurlt (by omega)) ⟨by decide, by decide⟩) rfl ?_
    rcases cur with _ | v
    · -- no vertex left: leave the loop
      simp only [curVal, show ¬ (0 : Int) ≤ -1 by decide, decide_false, Bool.false_eq_true, ite_false]
      apply wp_break
      have hp : pre = false := by
        cases pre
        · rfl
        · cases hpre rfl
      subst hp
      rw [fSweep_none] at hsw
      rw [fSweepEm_none, List.append_nil] at hlem
      subst hsw hlem
      simpa using hQn _ _ _ cl ch rfl hl hL hT hidx (by show idx ≤ n + 1; omega)
    · simp only [curVal, show (0 : Int) ≤ v by omega, decide_true, ite_true]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      rcases c with _ | c
      · exact absurd (by rw [← hsw, fSweep, sweep]) hRf
      have hv := hcurlt v rfl
      wp_step; wp_step; wp_step
      refine wp_fpnChild (Em := Em) L hE hT htv hL (fun hp => Option.some.inj (hpre hp)) hok hn0 hn
        hRecF hRecO hcb hln hncl htv1n hfr ?_ ?_
      · intro t' le₁ m₁ ch₁ hd hL' hEm hT' htv' hidx'
        simp only [seqPost, Post.after]
        wp_step; wp_step
        refine wp_fpnIndex hL'.search (hE.glob _ (by decide)) htv' hv hT'.tv1 htv1n
          (by rw [hidx']; exact hidx) ?_
        intro le₂ hidx₂ hle₂
        have hsw' := fSweep_succ L tv1 c v cl idx s
        rw [fChild_eta, hd] at hsw'
        have hem' := fSweepEm_succ Em L tv1 c v cl s
        rw [fChild_eta, hd] at hem'
        refine ⟨rfl, v, _, _, _, c, ch₁, rfl, hL', hT'.of (fun x hx => hle₂ x (by revert x; decide))
          (by obtain ⟨cc, hcc⟩ := hT'.cc; exact ⟨cc, by rw [hle₂ _ (by decide)]; exact hcc⟩),
          by rw [hle₂ _ (by decide)]; exact htv', hv, hidx₂, ?_,
          sweepOkFirst_next hn0 hn hok L.ctx 100 (nodeFuel n (L.level + 1)) hd,
          by rw [← hsw, hsw'], l ++ vertexEm (k := k0) Em L.level L.nc L.tc tv1 v s, ?_, ?_⟩
        · split <;> omega
        · simpa using hl.append hEm
        · rw [← hlem, hem', List.append_assoc]
      · intro t' m₁ ch₁ target short hu hlt hL' hEm
        have hsw' := fSweep_succ L tv1 c v cl idx s
        rw [fChild_eta, hu] at hsw'
        have hem' := fSweepEm_succ Em L tv1 c v cl s
        rw [fChild_eta, hu] at hem'
        have hR : R = (.unwind target short, idx, (fChild L tv1 v cl s).2.2) := by
          rw [← hsw, hsw']
        have := hQr (t ++ t') m₁ _ ch₁ target short (by rw [hR]) hlt (by rw [hR]; exact hL')
          (by rw [← hlem, hem', List.append_nil]; exact hl.append hEm)
        revert this
        cases Mem.free_list m₁ (blocks_of_env ge _) <;> exact id
  · -- the increment
    intro c t e' le' m' ⟨rfl, v, cl, s, idx, k', ch, hc, hL, hT, htv, hv, hidx, hik, hok, hsw, l,
      hl, hlem⟩
    obtain ⟨tw, htw, hrep⟩ := hL.cell
    refine wp_nodeNextAt (idOf 715) hL.search (hE.gl _) hT.tcell htw hrep htv hv ?_
    intro r hr
    refine ⟨k', by omega, ?_⟩
    have hrv : r = curVal (cl.nextElem (some v)) := by
      rcases hr with ⟨h1, h2⟩ | ⟨w, h1, h2⟩ <;> rw [h1, h2] <;> rfl
    have hg : ∀ x, x ≠ dense.id.«tv» → x ≠ idOf 715 →
        PTree.get x (PTree.set dense.id.«tv» (.Vint (ir r)) (PTree.set (idOf 715) (.Vint (ir r)) le')) =
          PTree.get x le' := fun x h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2]
    refine ⟨rfl, cl.nextElem (some v), cl, s, idx, false, ch, hL,
      hT.of (fun x hx => hg x (by revert x; decide) (by revert x; decide))
        (by obtain ⟨cc, hcc⟩ := hT.cc; exact ⟨cc, by rw [hg _ (by decide) (by decide)]; exact hcc⟩),
      by rw [← hrv]; exact temps_gss _ _ _, by rw [hg _ (by decide) (by decide)]; exact hidx,
      by omega, (fun h => by cases h), hok, hsw, l, by simpa using hl, hlem⟩

end NautyVerified.Proofs.Search

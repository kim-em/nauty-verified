import NautyVerified.Proofs.Search.Node.FirstCall

/-!
# After a child of `firstpathnode0`

`tailRes level exit cell s`: what HexGraphIso's `firstChild` does after the
recursive call returned `exit` and the vertex was erased from `fixedpts`
(`s`): stop on fuel or an unwind below `level`, else prune the target cell on
request and `recover`.

`wp_fpnTail`: `DELELEMENT(fixedpts, tv); if (rtnlevel < level) return rtnlevel;
if (needshortprune) { … shortprune … } recover(ptn, level);` carries out
`tailRes`, returning through the frame's `return` at an unwind below `level`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls} {n : Nat}

/-- `firstChild` after the call. -/
def tailRes (level : Nat) (exit : Exit) (cell : VSet n) (s : Search n) : Exit × VSet n × Search n :=
  match exit with
  | .fuel => (.fuel, cell, s)
  | .unwind target short =>
    if target < level then (.unwind target short, cell, s) else
      ((.done), (if short then shortprune cell s else cell), Hex.GraphIso.Nauty.recover nautyInf level s)
  | .done => (.done, cell, Hex.GraphIso.Nauty.recover nautyInf level s)

theorem firstChild_orb (ctx : Ctx n) (tl fuel level nc tc tv1 tv : Nat) (cell : VSet n)
    (st : Search n) (ho : (st.orbits[tv]! == tv) = true) :
    firstChild ctx nautyInf tl fuel level nc tc tv1 tv cell st =
      let r := node (tv == tv1) ctx nautyInf tl fuel (level + 1) (nc + 1) (child true level tc tv st)
      let s := if tv == tv1 then afterChildFirst level tv1 r.2 else r.2
      tailRes level r.1 cell { s with fixedpts := s.fixedpts.erase tv } := by
  simp only [firstChild, ho, ite_true]
  rcases (node (tv == tv1) ctx nautyInf tl fuel (level + 1) (nc + 1) (child true level tc tv st)).1
    with _ | ⟨target, short⟩ | _ <;> rfl

/-- `if (needshortprune) { needshortprune = FALSE; shortprune(…); } recover(ptn, level);` -/
theorem wp_fpnPruneRec {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (L : LCtx n) {s : Search n} {nsp : Bool} {cell : VSet n} {ch : List (block × block)}
    (h : LoopAt L m s false nsp cell ch) (hnz : nsp = true → 0 < s.autos.size)
    (hge : ∀ x ∈ [dense.id.«nauty:needshortprune», dense.id.«nauty:fmptr», dense.id.«nauty:m»,
      dense.id.«shortprune», dense.id.«nauty:recover»], PTree.get x e = none)
    (htl : PTree.get dense.id.tcell le = some (.Vptr L.btc Ptrofs.zero))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr L.S.bp L.S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir L.level))) (hln : L.level ≤ n)
    (hQ : ∀ m', LoopAt L m' (Hex.GraphIso.Nauty.recover nautyInf L.level s) false false
      (if nsp then shortprune cell s else cell) ch → Q.normal E0 e le m') :
    Wp xi ge f (.Ssequence (Set.sk Othernode.prune0) recCall) Q e le m := by
  simp only [List.forall_mem_cons] at hge
  obtain ⟨g1, g2, g3, g4, g5, -⟩ := hge
  obtain ⟨tw, hta, htr⟩ := h.cell
  have hmem := List.mem_of_getElem? h.chain.own
  obtain ⟨-, hbS, -, hbW⟩ := h.chain.ok.apart _ hmem
  have hl1 := h.chain.lvl
  wp_step; wp_step; wp_step
  refine wp_prune0 h.search g1 g2 g3 g4 htl hta htr hbS hbW hnz ?_
  intro m₁ tw' hS₁ hta' htr' hu₁ hg₁
  have hWw : ∀ z ∈ workG8, ¬ (z = Block.needshortprune ∨ z = L.btc) := by
    intro z hz hW
    have hzS : z ∈ L.S.blocks := by
      simp only [workG8, List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with h | h | h | h | h | h | h | h <;> subst h <;> simp [SLoc.blocks]
    rcases hW with rfl | rfl
    · revert hz; decide
    · exact hbS hzS
  have h₁ : LoopAt L m₁ s false false (if nsp then shortprune cell s else cell) ch :=
    h.step hS₁ (hu₁.mono fun z hz => by
        rcases hz with rfl | rfl
        · exact .inl ⟨by simp [SLoc.blocks], by sep_ne h.search.distinct, by decide⟩
        · exact .inr (.inr (.inr rfl)))
      hg₁ (fun z hz => .inl (IsWork.back h.search hu₁ hWw hz))
      ⟨tw', hta', htr'⟩
  simp only [seqPost, Post.after, E0_append]
  refine wp_nodeRecover h₁.search g5 hptn hlev hl1 hln ?_
  intro m₂ hS₂ hF₂ hW₂
  obtain ⟨tw₁, hta₁, htr₁⟩ := h₁.cell
  have hbS' : ¬ (L.S.Chg L.btc ∨ ¬ Mem.valid_block m₁ L.btc ∨ IsWork m₁ L.btc) := by
    obtain ⟨-, a2, -, a4⟩ := h₁.chain.ok.apart _ hmem
    rintro (⟨h1, -⟩ | h2 | h3)
    · exact a2 h1
    · exact h2 (h₁.chain.ok.valid _ hmem).2
    · exact a4 h3
  exact hQ m₂ (h₁.step hS₂ (hF₂.1.mono fun z hz => by
      rcases hz with hz | hz | hz
      · exact .inl hz
      · exact .inr (.inl hz)
      · exact .inr (.inr (.inl hz))) hF₂.2 hW₂ ⟨tw₁, hta₁.unch hF₂.1 hbS', htr₁⟩)

set_option maxHeartbeats 4000000 in
/-- `DELELEMENT(fixedpts, tv); if (rtnlevel < level) return rtnlevel;` then the prune and
`recover`: `tailRes`. -/
theorem wp_fpnTail {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (L : LCtx n) {s : Search n} {cell : VSet n} {ch : List (block × block)} {tv : Nat} {E : Exit}
    (h : LoopAt L m s false (exitValue (L.level + 1) E).2 cell ch) (hE : E ≠ .fuel)
    (htg : ∀ tg sh, E = .unwind tg sh → tg < L.level + 1)
    (hnz : (exitValue (L.level + 1) E).2 = true → 0 < s.autos.size)
    (hfr : f.fn_return = tint)
    (hge : ∀ x ∈ [dense.id.«nauty:fixedpts», dense.id.«nauty:bit», dense.id.«nauty:needshortprune»,
      dense.id.«nauty:fmptr», dense.id.«nauty:m», dense.id.«shortprune», dense.id.«nauty:recover»],
      PTree.get x e = none)
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir tv))) (hv : tv < n)
    (hrt : PTree.get dense.id.«rtnlevel» le = some (.Vint (ir (exitValue (L.level + 1) E).1)))
    (htl : PTree.get dense.id.tcell le = some (.Vptr L.btc Ptrofs.zero))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr L.S.bp L.S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir L.level))) (hln : L.level ≤ n)
    (hQd : ∀ m', (tailRes L.level E cell { s with fixedpts := s.fixedpts.erase tv }).1 = .done →
      LoopAt L m' (tailRes L.level E cell { s with fixedpts := s.fixedpts.erase tv }).2.2 false false
        (tailRes L.level E cell { s with fixedpts := s.fixedpts.erase tv }).2.1 ch →
      Q.normal E0 e le m')
    (hQr : ∀ m' target short, E = .unwind target short → target < L.level →
      LoopAt L m' { s with fixedpts := s.fixedpts.erase tv } false short cell ch →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret E0 (.Vint (ir target)) m''
      | none => False) :
    Wp xi ge f (.Ssequence (Set.delElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit»
        (Refine.tv dense.id.«tv»))
      (.Ssequence (Set.sk earlyRet) (.Ssequence (Set.sk Othernode.prune0) recCall))) Q e le m := by
  simp only [List.forall_mem_cons] at hge
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, -⟩ := hge
  have hd := h.search.distinct
  have hl1 := h.chain.lvl
  have hnl := h.search.nlt
  wp_step
  refine wp_fixDel h.search g1 g2 htv hv ?_
  intro m₁ hS₁ hu₁ hg₁
  have h₁ := h.small hS₁ hu₁ hg₁ (fun z hz => by
      subst hz; exact ⟨by simp [SLoc.blocks], by sep_ne hd, by sep_ne hd⟩) (by sep_all hd)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  simp only [earlyRet]
  apply wp_if_eval
  rcases E with _ | ⟨target, short⟩ | _
  · -- done
    rw [Processnode.eval_ltI (x := ((L.level + 1 : Nat) : Int)) (y := (L.level : Int))
      (by simpa [Exec.evalExpr, Refine.tv, exitValue] using hrt) (by simp [Exec.evalExpr, Refine.tv, hlev])
      rfl rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    rw [decide_eq_false (by omega)]
    simp only [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m₁ = some false from rfl,
      Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [E0_append]
    exact wp_fpnPruneRec L h₁ (fun h => by simp [exitValue] at h) (by simp [g3, g4, g5, g6, g7]) htl hptn
      hlev hln fun m' h' => hQd m' rfl (by simpa [tailRes, exitValue] using h')
  · -- unwind
    simp only [exitValue] at hrt hnz h₁
    rw [Processnode.eval_ltI (x := (target : Int)) (y := (L.level : Int))
      (by simpa [Exec.evalExpr, Refine.tv] using hrt) (by simp [Exec.evalExpr, Refine.tv, hlev])
      rfl rfl ⟨by omega, by have := htg _ _ rfl; omega⟩ ⟨by omega, by omega⟩]
    by_cases ht : target < L.level
    · rw [decide_eq_true (by omega)]
      simp only [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m₁ = some true from rfl, ite_true]
      wp_step; wp_step
      apply wp_return_some_eval
      simp only [Exec.evalExpr, Refine.tv, hrt, typeof, hfr]
      exact hQr m₁ target short rfl ht h₁
    · rw [decide_eq_false (by omega)]
      simp only [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m₁ = some false from rfl,
        Bool.false_eq_true, ite_false]
      apply wp_skip
      simp only [E0_append]
      exact wp_fpnPruneRec L h₁ hnz (by simp [g3, g4, g5, g6, g7]) htl hptn hlev hln fun m' h' =>
        hQd m' (by simp [tailRes, ht]) (by simpa [tailRes, ht] using h')
  · exact absurd rfl hE

end NautyVerified.Proofs.Search

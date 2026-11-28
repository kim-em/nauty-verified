import NautyVerified.Proofs.Sparse.Refine.Select

/-!
# `refine_sg`'s main loop

`while (nactive > 0 && *numcells < n)`: choose the splitter (`wp_selectLoop`,
`wp_pick`), `DELELEMENT(active, isplit)`, `MASH(isplit)`, then the singleton
or nontrivial splitter (`TrivialPass`, `NontrivialPass`). Each iteration runs
the splitter on the state the C holds with the scratch it finds (`withScr`:
marks and stamp 0, as after `RESETMARKS`, and `HITS` below `n`), which is
`Same` as HexGraphIso's state, so by `loop_same` the C follows HexGraphIso's
main loop (`iterF (loopStep …)`); `entry_saturated` makes the loop stop by its
own test.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk delElementB)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph splitSingleton splitNontrivial)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n}

/-- `t` with the scratch the C finds: marks and stamp 0, `HITS` below `n`. -/
def withScr (t : RefineSt n) (S : Scr) : RefineSt n :=
  { t with
    marks := Array.replicate n 0
    vmarks := Array.replicate n 0
    stamp := 0
    hits := (Array.range n).map fun v => S.w3[v]! }

theorem withScr_hits (t : RefineSt n) (S : Scr) {v : Nat} (hv : v < n) :
    (withScr t S).hits[v]! = S.w3[v]! := by
  simp [withScr, hv]

theorem rep0_get {i : Nat} (hi : i < n) : (Array.replicate n 0)[i]! = 0 := by
  rw [getElem!_pos (Array.replicate n 0) i (by simpa using hi)]; simp

theorem withScr_valid {level : Nat} {t : RefineSt n} (h : t.Valid level) (S : Scr) :
    (withScr t S).Valid level :=
  ⟨h.lab, h.size, h.closed, h.index,
    ⟨h.scratch.starts_size, h.scratch.ends_size, by simp [withScr, RefineSt.toScratch],
      by simp [withScr, RefineSt.toScratch], by simp [withScr, RefineSt.toScratch],
      fun i hi => by simp [withScr, RefineSt.toScratch, rep0_get hi],
      fun i hi => by simp [withScr, RefineSt.toScratch, rep0_get hi]⟩, h.queue⟩

theorem withScr_same (t : RefineSt n) (S : Scr) : Same t (withScr t S) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem withScr_fresh (t : RefineSt n) (S : Scr) : Fresh (withScr t S) := ⟨rfl, rfl, rfl⟩

/-- The temporaries the main loop assigns, besides `longcode` and `nactive`. -/
def loopTemps : List ident :=
  passTemps ++ [id.«trivsplit», idOf 729, idOf 730, idOf 731, idOf 732]

/-- The loop test. -/
abbrev guardS : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Ebinop .Ogt (tv id.«nactive») (ci 0 tint) tint)
      (sk (.Sset (idOf 729) (.Ecast (.Ebinop .Olt (.Ederef (pi id.«numcells») tint) (tv id.«n») tint) tbool)))
      (.Sset (idOf 729) (ci 0 tint))))
    (.Sifthenelse (tv (idOf 729)) .Sskip .Sbreak)

/-- After the splitter choice: remove, hash and split. -/
abbrev splitS : statement :=
  .Ssequence (delElementB id.«active» id.«nausparse:bit» (tv id.«isplit»))
    (.Ssequence (sk (mash (tv id.«isplit»)))
      (sk (.Sifthenelse (tv id.«trivsplit») trivial nontrivial)))

theorem mainLoop_eq : mainLoop =
    .Sloop (.Ssequence guardS
      (.Ssequence (.Ssequence (sk (.Sset id.«i» (ci 0 tint))) selectLoop) (.Ssequence pick splitS)))
      .Sskip := rfl

/-- The main loop's invariant: memory holds a state `t` exactly, from which
HexGraphIso's main loop with `F` more iterations reaches a state `Same` as
`fin`. -/
def LoopInv (L : Loc) (G : Hex.SparseGraph n) (fin : RefineSt n) (m0 : mem) (le0 : temp_env)
    (F : Nat) (le : temp_env) (m : mem) : Prop :=
  ∃ t S, Mem m L G t S ∧ Rep L t S ∧ Tmp le L t ∧ t.Valid L.level ∧ Budget L.level t ∧
    t.longcode < 2 ^ 62 ∧ Frame L m0 m ∧
    Same fin (iterF (loopStep (.ofGraph G) L.level) F t) ∧
    ∀ x, x ∉ loopTemps → x ∉ args → x ≠ id.longcode → x ≠ id.nactive →
      PTree.get x le = PTree.get x le0

theorem iterF_stop {g : Graph n} {level : Nat} {t : RefineSt n}
    (h : (t.queue.isEmpty || decide (t.numcells ≥ n)) = true) :
    ∀ F, iterF (loopStep g level) F t = t
  | 0 => rfl
  | F + 1 => by simp only [iterF, loopStep, h, ite_true]

theorem iterF_go {g : Graph n} {level : Nat} {t : RefineSt n} (F : Nat)
    (h : (t.queue.isEmpty || decide (t.numcells ≥ n)) = false) :
    iterF (loopStep g level) (F + 1) t =
      iterF (loopStep g level) F (RefineSt.selected g level (RefineSt.position level t) t) := by
  simp only [iterF, loopStep, h, Bool.false_eq_true, ite_false]

/-- Choosing the same position in two admissible states that are `Same`. -/
theorem selected_same (G : Hex.SparseGraph n) (level : Nat) {a b : RefineSt n} (ha : a.Valid level)
    (hb : b.Valid level) (h : Same a b) {pos : Nat} (hp : pos < a.queue.size) :
    Same (RefineSt.selected (.ofGraph G) level pos a) (RefineSt.selected (.ofGraph G) level pos b) :=
  Same.of_equiv (h.equiv.selected G G (Hex.GraphIso.Perm.id n) (by intro u v; simp) ha hb _ hp)
    (h.equiv.selected_lab G ha hb h.lab.symm _ hp).symm

/-- One iteration of the main loop, after its test held. -/
theorem wp_iter (hT : TrivialPass (xi := xi)) (hN : NontrivialPass (xi := xi)) {Q : Post} {le : temp_env} {m : mem}
    (hok : Ok n L) {t : RefineSt n} {S : Scr} (hm : Mem m L G t S) (hr : Rep L t S)
    (ht : Tmp le L t) (hv : t.Valid L.level) (hb : Budget L.level t) (hc : t.longcode < 2 ^ 62)
    (hq : 0 < t.queue.size)
    (hQ : ∀ le' m' t' S', Mem m' L G t' S' → Rep L t' S' → Tmp le' L t' → t'.Valid L.level →
      Budget L.level t' → t'.longcode < 2 ^ 62 → Frame L m m' →
      Same (RefineSt.selected (.ofGraph G) L.level (RefineSt.position L.level t) t) t' →
      (∀ x, x ∉ loopTemps → x ∉ args → x ≠ id.longcode → x ≠ id.nactive →
        PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (.Ssequence (.Ssequence (sk (.Sset id.«i» (ci 0 tint))) selectLoop) (.Ssequence pick splitS))
      Q empty_env le m := by
  have hnl := hok.nlt
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  refine wp_selectLoop hok hm hr (ht.set (x := id.«i») _ (by decide)) hv (by simp) ?_
  intro i le1 hi hpre hsing hil1 ho1
  simp only [E0_append]
  wp_step
  refine wp_pick hok hm hr (ht.frame (ws := [id.«i», idOf 730]) (fun x hx => by
      rw [ho1 x hx, temps_gso _ _ (fun h => hx (by simp [h]))]) (by decide)) hv hq hi hpre hsing hil1 ?_
  intro le2 m2 hm2 hf2 ht2 hsp2 htr2 ho2
  simp only [E0_append]
  have hp : RefineSt.position L.level t < t.queue.size := RefineSt.position_lt L.level t hq
  have hcell := hv.queue_cell hp
  have hqn : t.queue.size ≤ n := queue_size_le hv.queue.set
  have hr2 : Rep L (dropAt t (RefineSt.position L.level t))
      { S with w2 := upd S.w2 (RefineSt.position L.level t) (S.w2 (t.queue.size - 1)) } := by
    refine ⟨hr.starts, fun i hi => ?_, hr.w3size, hr.w3small, hr.ptnSmall⟩
    have hi' : i < t.queue.size - 1 := by simpa using hi
    show upd S.w2 _ _ i = _
    rw [dropAt_get hp hi']
    by_cases h : i = RefineSt.position L.level t
    · rw [h, upd_same, ite_eq_left rfl, hr.queue _ (by omega)]
    · rw [upd_ne _ _ h, ite_eq_right h, hr.queue _ (by omega)]
  wp_step
  refine wp_delAct hok hm2 ht2 (c := t.queue[RefineSt.position L.level t]!)
    (by simp only [Exec.evalExpr]; exact hsp2) rfl hcell.1 ?_
  intro m3 aw hm3 hf3
  simp only [E0_append]
  wp_step; wp_step; wp_step
  refine wp_mash ht2.longcode hc (by simp only [Exec.evalExpr]; exact hsp2) rfl (by omega) ?_
  simp only [E0_append]
  have ht3 := ((ht2.congr (t' := { dropAt t (RefineSt.position L.level t) with
      active := (dropAt t (RefineSt.position L.level t)).active.erase
        t.queue[RefineSt.position L.level t]! }) rfl rfl).hash t.queue[RefineSt.position L.level t]!)
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr]
  rw [temps_gso _ _ (by decide), htr2]
  by_cases hsing : t.ptn[t.queue[RefineSt.position L.level t]!]! ≤ L.level
  · simp (config := {decide := true}) only [hsing, decide_true, typeof, Val.of_bool, cop, ite_true]
    let S3 : Scr := { S with w2 := upd S.w2 (RefineSt.position L.level t) (S.w2 (t.queue.size - 1)), aw }
    have hva := withScr_valid (((hv.remove hp).hash t.queue[RefineSt.position L.level t]!)) S3
    refine hT (s := withScr ((({ t with
          active := t.active.erase t.queue[RefineSt.position L.level t]!
          queue := (t.queue.setIfInBounds (RefineSt.position L.level t) t.queue[t.queue.size - 1]!).pop }
          : RefineSt n)).hash t.queue[RefineSt.position L.level t]!) S3)
      hok (hm3.congr rfl rfl rfl rfl) ⟨hr2.starts, hr2.queue, hr2.w3size, hr2.w3small, hr2.ptnSmall⟩
      (ht3.congr rfl rfl) hva (withScr_fresh _ _) hb (Nat.lt_trans (Refine.mash_lt _ _) (by decide))
      hcell.1 hsing hcell.2.1.2.1 (by rw [temps_gso _ _ (by decide)]; exact hsp2) ?_
    intro le' m' S' ha
    have hst := hva.singleton G _ hcell.1
    have hsame : Same (RefineSt.selected (.ofGraph G) L.level (RefineSt.position L.level t) t)
        (splitSingleton (.ofGraph G) L.level t.queue[RefineSt.position L.level t]! (withScr ((({ t with
          active := t.active.erase t.queue[RefineSt.position L.level t]!
          queue := (t.queue.setIfInBounds (RefineSt.position L.level t) t.queue[t.queue.size - 1]!).pop }
          : RefineSt n)).hash t.queue[RefineSt.position L.level t]!) S3)) := by
      have h := selected_same G L.level hv (withScr_valid hv S3) (withScr_same t S3) hp
      have heq : RefineSt.selected (.ofGraph G) L.level (RefineSt.position L.level t) (withScr t S3) =
          splitSingleton (.ofGraph G) L.level t.queue[RefineSt.position L.level t]! (withScr ((({ t with
            active := t.active.erase t.queue[RefineSt.position L.level t]!
            queue := (t.queue.setIfInBounds (RefineSt.position L.level t) t.queue[t.queue.size - 1]!).pop }
            : RefineSt n)).hash t.queue[RefineSt.position L.level t]!) S3) := by
        unfold RefineSt.selected
        simp only [withScr, RefineSt.hash, hsing, ite_true]
        rfl
      exact heq ▸ h
    refine hQ le' m' _ S' ha.mem ha.rep ha.tmp hst.1 (Budget.step hst.2 hb) ha.code
      (hf2.trans (hf3.trans ha.frame)) hsame fun x hx h1 h2 h3 => ?_
    have hx' : x ∉ passTemps := fun h => hx (List.mem_append_left _ h)
    rw [ha.temps x hx' h1 h2 h3, temps_gso _ _ h2, ho2 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨h3, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> exact hx (by unfold loopTemps passTemps cellTemps; decide))]
    rw [ho1 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_⟩ <;> intro e <;> subst e <;> exact hx (by unfold loopTemps passTemps cellTemps; decide)),
      temps_gso _ _ (by intro e; subst e; exact hx (by unfold loopTemps passTemps cellTemps; decide))]
  · simp (config := {decide := true}) only [hsing, decide_false, typeof, Val.of_bool, cop, ite_false]
    let S3 : Scr := { S with w2 := upd S.w2 (RefineSt.position L.level t) (S.w2 (t.queue.size - 1)), aw }
    have hva := withScr_valid (((hv.remove hp).hash t.queue[RefineSt.position L.level t]!)) S3
    have hlen : 1 < t.cellend[t.queue[RefineSt.position L.level t]!]! + 1 - t.queue[RefineSt.position L.level t]! := by
      have hc2 := hcell.2.1
      rcases Nat.lt_or_ge 1 (t.cellend[t.queue[RefineSt.position L.level t]!]! + 1 -
        t.queue[RefineSt.position L.level t]!) with h | h
      · exact h
      · have h1 : t.cellend[t.queue[RefineSt.position L.level t]!]! + 1 - t.queue[RefineSt.position L.level t]! = 1 := by
          have := hc2.1; omega
        have := hc2.2.2.2
        rw [h1, Nat.add_sub_cancel] at this
        exact absurd this hsing
    refine hN (s := withScr ((({ t with
          active := t.active.erase t.queue[RefineSt.position L.level t]!
          queue := (t.queue.setIfInBounds (RefineSt.position L.level t) t.queue[t.queue.size - 1]!).pop }
          : RefineSt n)).hash t.queue[RefineSt.position L.level t]!) S3)
      hok (hm3.congr rfl rfl rfl rfl) ⟨hr2.starts, hr2.queue, hr2.w3size, hr2.w3small, hr2.ptnSmall⟩
      (ht3.congr rfl rfl) hva (withScr_fresh _ _) hb (Nat.lt_trans (Refine.mash_lt _ _) (by decide))
      (fun v hv => (withScr_hits _ S3 hv).symm) hcell.2.1 (by omega) hlen
      (by rw [temps_gso _ _ (by decide)]; exact hsp2) ?_
    intro le' m' S' ha
    have hst := hva.nontrivial G _ _ hcell.2.1 (by omega)
    have hsame : Same (RefineSt.selected (.ofGraph G) L.level (RefineSt.position L.level t) t)
        (splitNontrivial (.ofGraph G) L.level t.queue[RefineSt.position L.level t]! (withScr ((({ t with
          active := t.active.erase t.queue[RefineSt.position L.level t]!
          queue := (t.queue.setIfInBounds (RefineSt.position L.level t) t.queue[t.queue.size - 1]!).pop }
          : RefineSt n)).hash t.queue[RefineSt.position L.level t]!) S3)) := by
      have h := selected_same G L.level hv (withScr_valid hv S3) (withScr_same t S3) hp
      have heq : RefineSt.selected (.ofGraph G) L.level (RefineSt.position L.level t) (withScr t S3) =
          splitNontrivial (.ofGraph G) L.level t.queue[RefineSt.position L.level t]! (withScr ((({ t with
            active := t.active.erase t.queue[RefineSt.position L.level t]!
            queue := (t.queue.setIfInBounds (RefineSt.position L.level t) t.queue[t.queue.size - 1]!).pop }
            : RefineSt n)).hash t.queue[RefineSt.position L.level t]!) S3) := by
        unfold RefineSt.selected
        simp only [withScr, RefineSt.hash, hsing, ite_false]
        rfl
      exact heq ▸ h
    refine hQ le' m' _ S' ha.mem ha.rep ha.tmp hst.1 (Budget.step hst.2 hb) ha.code
      (hf2.trans (hf3.trans ha.frame)) hsame fun x hx h1 h2 h3 => ?_
    have hx' : x ∉ passTemps := fun h => hx (List.mem_append_left _ h)
    rw [ha.temps x hx' h1 h2 h3, temps_gso _ _ h2, ho2 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨h3, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> exact hx (by unfold loopTemps passTemps cellTemps; decide))]
    rw [ho1 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_⟩ <;> intro e <;> subst e <;> exact hx (by unfold loopTemps passTemps cellTemps; decide)),
      temps_gso _ _ (by intro e; subst e; exact hx (by unfold loopTemps passTemps cellTemps; decide))]


/-- The main loop, from its invariant, given that HexGraphIso's loop stops at
`fin` by its own test. -/
theorem wp_mainLoop (hT : TrivialPass (xi := xi)) (hN : NontrivialPass (xi := xi)) {Q : Post}
    {le : temp_env} {m : mem} (hok : Ok n L) {fin : RefineSt n}
    (hsat : fin.queue.isEmpty = true ∨ n ≤ fin.numcells) {k : Nat} (h0 : LoopInv L G fin m le k le m)
    (hQ : ∀ le' m' t S, Mem m' L G t S → Rep L t S → Tmp le' L t → t.Valid L.level →
      Same fin t → Frame L m m' →
      (∀ x, x ∉ loopTemps → x ∉ args → x ≠ id.longcode → x ≠ id.nactive →
        PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F mainLoop Q empty_env le m := by
  have hnl := hok.nlt
  rw [mainLoop_eq]
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ LoopInv L G fin m le v le' m'
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ v' < v, LoopInv L G fin m le v' le' m'
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := k) ⟨rfl, rfl, h0⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, t, S, hm, hr, ht, hv, hb, hc, hf, hsame, ho⟩
    have hbc := Hex.GraphIso.Nauty.bcount_le t.ptn L.level n
    have hnc : t.numcells ≤ 2 * n := by unfold Budget at hb; omega
    have hqn : t.queue.size ≤ n := queue_size_le hv.queue.set
    wp_step; wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, ht.nactive, typeof, cop]
    rw [ir_lt (a := 0) (b := (t.queue.size : Int)) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩]
    have hstopQ : ∀ le'', (t.queue.isEmpty || decide (t.numcells ≥ n)) = true →
        (∀ x, x ∉ [idOf 729] → PTree.get x le'' = PTree.get x le') →
        Q.normal E0 empty_env le'' m' := fun le'' hst ho' =>
      hQ le'' m' t S hm hr (ht.frame ho' (by decide)) hv (by rwa [iterF_stop hst] at hsame) hf
        fun x hx h1 h2 h3 => by
          rw [ho' x (by intro e; simp at e; subst e; exact hx (by unfold loopTemps passTemps cellTemps; decide)),
            ho x hx h1 h2 h3]
    by_cases hq0 : 0 < t.queue.size
    · rw [ite_eq_left (by simpa using hq0)]
      wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, eval_binop (eval_nc hm ht) (show Exec.evalExpr sge empty_env le' m' (tv id.«n») = _
        from ht.n)]
      simp only [typeof, cop, cast_b]
      rw [ir_lt (a := (t.numcells : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof]
      by_cases hn : t.numcells < n
      · rw [show decide ((t.numcells : Int) < n) = true from decide_eq_true (by omega)]
        simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
        apply wp_skip
        simp only [E0_append]
        have hne : t.queue.isEmpty = false := by
          cases hqe : t.queue.isEmpty
          · rfl
          · rw [Array.isEmpty_iff_size_eq_zero] at hqe; omega
        have hgo : (t.queue.isEmpty || decide (t.numcells ≥ n)) = false := by
          rw [hne, Bool.false_or]; exact decide_eq_false (by omega)
        obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := by
          rcases v with _ | v'
          · exfalso
            have hs : Same fin t := hsame
            rcases hsat with h | h
            · rw [hs.queue, hne] at h; exact absurd h (by decide)
            · rw [hs.numcells] at h; omega
          · exact ⟨v', rfl⟩
        rw [iterF_go v' hgo] at hsame
        refine wp_iter hT hN hok hm hr (ht.set (x := idOf 729) _ (by decide)) hv hb hc hq0 ?_
        intro le2 m2 t2 S2 hm2 hr2 ht2 hv2 hb2 hc2 hf2 hs2 ho2
        have hl := loop_same G L.level v' _ _ (hv.selected G L.level _ t (RefineSt.position_lt L.level t hq0))
          hv2 hs2
        refine ⟨by simp, rfl, v', by omega, t2, S2, hm2, hr2, ht2, hv2, hb2, hc2, hf.trans hf2,
          hsame.trans hl.2.2, fun x hx h1 h2 h3 => ?_⟩
        rw [ho2 x hx h1 h2 h3, temps_gso _ _ (by intro e; subst e; exact hx (by
          unfold loopTemps passTemps cellTemps; decide)), ho x hx h1 h2 h3]
      · rw [show decide ((t.numcells : Int) < n) = false from decide_eq_false (by omega)]
        simp (config := {decide := true}) only [Val.of_bool, cop]
        apply wp_break
        exact hstopQ _ (by rw [Bool.or_eq_true]; exact Or.inr (decide_eq_true (by omega))) fun x hx => temps_gso _ _ (by intro e; subst e; simp at hx)
    · rw [ite_eq_right (by simpa using hq0)]
      wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp (config := {decide := true}) only [ite_false]
      apply wp_break
      exact hstopQ _ (by rw [Bool.or_eq_true]; exact Or.inl ((Array.isEmpty_iff_size_eq_zero).2 (by omega)))
        fun x hx => temps_gso _ _ (by intro e; subst e; simp at hx)
  · rintro v tr e' le' m' ⟨rfl, rfl, v', hv', hinv⟩
    apply wp_skip
    exact ⟨v', hv', by simp, rfl, hinv⟩

end NautyVerified.Proofs.Sparse.Refine

import NautyVerified.Proofs.Search.Node.Em
import HexGraphIso.Nauty.Policy.Emission
import HexGraphIso.Nauty.Policy.Scatter

/-!
# The emission of a node: HexGraphIso's `emitted`

HexGraphIso's search records, in `SearchState.emitted`, each permutation nauty
passes to `userautomproc`: `leafExit` pushes `workperm` exactly where it
increments `numgenerators` (every code-1 automorphism, and each code-2
automorphism that merges orbits). Every other step of the search leaves
`emitted` unchanged, so a node's run only appends to it.

`emWords ctx first level numcells st` is the `gensWords` of what the node's
run appends. `emLawOff` and `emLawFirst` prove that it satisfies `EmLawOff` and
`EmLawFirst`; `emWords_root` identifies its value at the root with the words of
`TraceRun.emitted`.
-/

namespace NautyVerified.Proofs.Search

open NautyVerified NautyVerified.Spec
open Hex.GraphIso.Nauty

variable {n : Nat}

/-- The emissions appended between the states `a` and `b`. -/
abbrev added (a b : Search n) : List (Array Nat) := b.emitted.toList.drop a.emitted.size

/-- The words a node at `level` emits: those of the permutations its run
appends to `emitted`. -/
def emWords (ctx : Ctx n) (first : Bool) (level numcells : Nat) (st : Search n) : List Int :=
  gensWords (added st (hexNode first ctx level numcells st).2) n

theorem gensWords_append (a b : List (Array Nat)) :
    gensWords (a ++ b) n = gensWords a n ++ gensWords b n := by
  simp [gensWords, List.flatMap_append]

theorem added_trans {a b c : Search n} (hab : a.emitted.toList <+: b.emitted.toList)
    (hbc : b.emitted.toList <+: c.emitted.toList) : added a c = added a b ++ added b c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  simp only [added, ← Array.length_toList]
  rw [← hy, ← hx]
  generalize a.emitted.toList = A
  rw [show List.drop (A ++ x).length ((A ++ x) ++ y) = y from List.drop_left ..,
    show List.drop A.length (A ++ x) = x from List.drop_left ..,
    List.append_assoc, List.drop_left]

theorem added_self (a : Search n) : added a a = [] := by
  simp [added]

theorem added_congr {a a' b b' : Search n} (ha : a'.emitted = a.emitted)
    (hb : b'.emitted = b.emitted) : added a' b' = added a b := by
  simp only [added, ha, hb]

/-! ## Steps that leave `emitted` alone -/

theorem classify_log (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    Emission.log (classify ctx level numcells st).2 = Emission.log st := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, apply_ite Emission.log,
    scatter_eq]
  simp only [Emission.log, ite_self]

theorem target_log (first : Bool) (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    Emission.log (chooseTarget first ctx tcLevel level numcells st).2.2.2 = Emission.log st := by
  unfold chooseTarget
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, apply_ite Emission.log]
  repeat' first | rfl | split

theorem emitted_of_log {a b : Search n} (h : Emission.log a = Emission.log b) :
    a.emitted = b.emitted :=
  congrArg Emission.Log.emitted h

theorem leafExit_workperm (leaf : Leaf) (level : Nat) (st : Search n)
    (h : leaf = .autoFirst ∨ leaf = .autoCanon) :
    (leafExit leaf level st).2.workperm = st.workperm := by
  rcases h with rfl | rfl <;> unfold leafExit admit pushAuto <;>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd] <;>
    repeat' first | rfl | split

/-- A leaf appends `workperm` exactly when it counts a new generator. -/
theorem leaf_added (leaf : Leaf) (level : Nat) (st : Search n) :
    added st (leafExit leaf level st).2 =
      if (leafExit leaf level st).2.numgenerators = st.numgenerators + 1 then
        [(leafExit leaf level st).2.workperm] else [] := by
  have hl := Emission.leaf_log leaf level st
  have hw := leafExit_workperm leaf level st
  cases leaf with
  | autoFirst =>
    have he := congrArg Emission.Log.emitted hl
    have hg := congrArg Emission.Log.numgenerators hl
    simp only [Emission.log, Emission.Log.emit, Emission.Log.join] at he hg
    rw [added, he, hg, hw (.inl rfl)]
    simp
  | autoCanon =>
    dsimp only at hl
    split at hl
    · have he := congrArg Emission.Log.emitted hl
      have hg := congrArg Emission.Log.numgenerators hl
      simp only [Emission.log, Emission.Log.join] at he hg
      rw [added, he, hg]
      simp
    · have he := congrArg Emission.Log.emitted hl
      have hg := congrArg Emission.Log.numgenerators hl
      simp only [Emission.log, Emission.Log.emit, Emission.Log.join] at he hg
      rw [added, he, hg, hw (.inr rfl)]
      simp
  | _ =>
    have he := congrArg Emission.Log.emitted hl
    have hg := congrArg Emission.Log.numgenerators hl
    simp only [Emission.log] at he hg
    rw [added, he, hg]
    simp

/-! ## A node's run only appends -/

theorem leaf_prefix (E : List (Array Nat)) (leaf : Leaf) (level : Nat) (st : Search n)
    (h : E <+: (Emission.log st).emitted.toList) :
    E <+: (Emission.log (leafExit leaf level st).2).emitted.toList := by
  rw [Emission.leaf_log]
  have hj : ((Emission.log st).join st.workperm n).emitted = (Emission.log st).emitted := rfl
  have he : E <+: (((Emission.log st).join st.workperm n).emit st.workperm).emitted.toList := by
    simp only [Emission.Log.emit, Array.toList_push, hj]
    exact h.trans (List.prefix_append _ _)
  cases leaf
  all_goals first | exact h | exact he | (dsimp only; split <;> first | exact he | exact h)

theorem node_prefix (first : Bool) (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat)
    (st : Search n) :
    st.emitted.toList <+: (node first ctx inf tcLevel fuel level numcells st).2.emitted.toList := by
  rw [node_eq_generic]
  exact Generic.node_sound
    (Emission.preserve ctx inf tcLevel (fun l => st.emitted.toList <+: l.emitted.toList)
      (fun v l s h => leaf_prefix _ v l s h)).sound
    first fuel level numcells st (List.prefix_refl _)

/-! ## The sweeps -/

theorem otherChild_emitted (ctx : Ctx n) (inf tl fuel level nc tc tv1 tv : Nat) (tcell : VSet n)
    (st : Search n) :
    (otherChild ctx inf tl fuel level nc tc tv1 tv tcell st).2.2.emitted =
      (node false ctx inf tl fuel (level + 1) (nc + 1) (child false level tc tv st)).2.emitted := by
  unfold otherChild
  generalize node false ctx inf tl fuel (level + 1) (nc + 1) (child false level tc tv st) = r
  obtain ⟨e, s⟩ := r
  cases e with
  | fuel => rfl
  | unwind target short =>
    dsimp only
    split
    · rfl
    · exact emitted_of_log (Emission.recover_log _ _ _)
  | done => exact emitted_of_log (Emission.recover_log _ _ _)

theorem firstChild_emitted (ctx : Ctx n) (inf tl fuel level nc tc tv1 tv : Nat) (tcell : VSet n)
    (st : Search n) :
    (firstChild ctx inf tl fuel level nc tc tv1 tv tcell st).2.2.emitted =
      if st.orbits[tv]! == tv then
        (node (tv == tv1) ctx inf tl fuel (level + 1) (nc + 1) (child true level tc tv st)).2.emitted
      else st.emitted := by
  unfold firstChild
  split
  · generalize node (tv == tv1) ctx inf tl fuel (level + 1) (nc + 1) (child true level tc tv st) = r
    obtain ⟨e, s⟩ := r
    have hs : (if (tv == tv1) = true then afterChildFirst level tv1 s else s).emitted = s.emitted := by
      split <;> rfl
    cases e with
    | fuel => exact hs
    | unwind target short =>
      dsimp only
      split
      · exact hs
      · exact (emitted_of_log (Emission.recover_log _ _ _)).trans hs
    | done => exact (emitted_of_log (Emission.recover_log _ _ _)).trans hs
  · rfl

theorem child_emitted (first : Bool) (level tc tv : Nat) (st : Search n) :
    (child first level tc tv st).emitted = st.emitted :=
  emitted_of_log (Emission.child_log first level tc tv st)

theorem sweep_prefix (first : Bool) (ctx : Ctx n) (inf tcLevel fuel cfuel level nc tc tv1 : Nat)
    (tv? : Option Nat) (tcell : VSet n) (index : Nat) (st : Search n) :
    st.emitted.toList <+: (sweep first ctx inf tcLevel fuel cfuel level nc tc tv1 tv? tcell index
      st).2.2.emitted.toList := by
  rw [sweep_eq_generic]
  exact Generic.sweep_sound
    (Emission.preserve ctx inf tcLevel (fun l => st.emitted.toList <+: l.emitted.toList)
      (fun v l s h => leaf_prefix _ v l s h)).sound
    first fuel cfuel level nc tc tv1 tv? tcell index st (List.prefix_refl _)

/-- What an off-path sweep appends is `sweepEm` of `emWords`. -/
theorem sweep_false_added (ctx : Ctx n) (level nc tc tv1 : Nat) :
    ∀ (cfuel : Nat) (tv? : Option Nat) (tcell : VSet n) (index : Nat) (st : Search n),
      gensWords (added st (sweep false ctx nautyInf 100 (nodeFuel n (level + 1)) cfuel level nc
        tc tv1 tv? tcell index st).2.2) n =
        sweepEm (emWords ctx) ctx level nc tc tv1 cfuel tv? tcell st
  | _, none, tcell, index, st => by
    rw [sweep_false_none, sweepEm, added_self]; rfl
  | 0, some tv, tcell, index, st => by
    rw [sweep, sweepEm, added_self]; rfl
  | cfuel + 1, some tv, tcell, index, st => by
    rw [sweep_false_some, sweepEm]
    have hc : (child false level tc tv st).emitted = st.emitted := child_emitted _ _ _ _ _
    have hnode := node_prefix false ctx nautyInf 100 (nodeFuel n (level + 1)) (level + 1) (nc + 1)
      (child false level tc tv st)
    rw [hc] at hnode
    have hEm : emWords ctx false (level + 1) (nc + 1) (child false level tc tv st) =
        gensWords (added st (otherChild ctx nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv
          tcell st).2.2) n := by
      rw [emWords, added_congr hc (otherChild_emitted ..).symm]
    rw [hEm]
    have hpre : st.emitted.toList <+: (otherChild ctx nautyInf 100 (nodeFuel n (level + 1)) level
        nc tc tv1 tv tcell st).2.2.emitted.toList := by
      rw [otherChild_emitted]; exact hnode
    generalize otherChild ctx nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv tcell st = r
      at hpre ⊢
    obtain ⟨e, tcell', st'⟩ := r
    cases e with
    | done =>
      dsimp only
      rw [added_trans hpre (sweep_prefix ..), gensWords_append,
        sweep_false_added ctx level nc tc tv1 cfuel]
    | _ => simp

/-- What a first-path sweep appends is `sweepEmFirst` of `emWords`. -/
theorem sweep_true_added (ctx : Ctx n) (level nc tc tv1 : Nat) :
    ∀ (cfuel : Nat) (tv? : Option Nat) (tcell : VSet n) (index : Nat) (st : Search n),
      gensWords (added st (sweep true ctx nautyInf 100 (nodeFuel n (level + 1)) cfuel level nc
        tc tv1 tv? tcell index st).2.2) n =
        sweepEmFirst (emWords ctx) ctx level nc tc tv1 cfuel tv? tcell st
  | _, none, tcell, index, st => by
    rw [sweep_true_none, sweepEmFirst, added_self]; rfl
  | 0, some tv, tcell, index, st => by
    rw [sweep, sweepEmFirst, added_self]; rfl
  | cfuel + 1, some tv, tcell, index, st => by
    rw [sweep_true_some, sweepEmFirst]
    have hc : (child true level tc tv st).emitted = st.emitted := child_emitted _ _ _ _ _
    have hpre : st.emitted.toList <+: (firstChild ctx nautyInf 100 (nodeFuel n (level + 1)) level
        nc tc tv1 tv tcell st).2.2.emitted.toList := by
      rw [firstChild_emitted]
      split
      · have hnode := node_prefix (tv == tv1) ctx nautyInf 100 (nodeFuel n (level + 1)) (level + 1)
          (nc + 1) (child true level tc tv st)
        rwa [hc] at hnode
      · exact List.prefix_refl _
    have hEm : (if st.orbits[tv]! == tv then
          emWords ctx (tv == tv1) (level + 1) (nc + 1) (child true level tc tv st) else []) =
        gensWords (added st (firstChild ctx nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv
          tcell st).2.2) n := by
      have he := firstChild_emitted ctx nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv
        tcell st
      split
      · rename_i ho
        rw [ho, ite_eq_left rfl] at he
        rw [emWords, added_congr hc he.symm]
      · rename_i ho
        rw [ite_eq_right ho] at he
        rw [added_congr rfl he, added_self]; rfl
    rw [hEm]
    generalize firstChild ctx nautyInf 100 (nodeFuel n (level + 1)) level nc tc tv1 tv tcell st = r
      at hpre ⊢
    obtain ⟨e, tcell', st'⟩ := r
    cases e with
    | done =>
      dsimp only
      rw [added_trans hpre (sweep_prefix ..), gensWords_append,
        sweep_true_added ctx level nc tc tv1 cfuel]
    | _ => simp

/-! ## The laws -/

theorem nodeFuel_succ {level : Nat} (hn : level ≤ n) :
    nodeFuel n level = nodeFuel n (level + 1) + 1 := by
  simp only [nodeFuel]; omega

/-- `processnode` appends what it writes. -/
theorem procExit_added (ctx : Ctx n) (level nc : Nat) (s : Search n) :
    gensWords (added s (procExit ctx level nc s).2) n = procWords ctx level nc s := by
  have hl := classify_log ctx level nc s
  have ecl := emitted_of_log hl
  have gcl := congrArg Emission.Log.numgenerators hl
  simp only [Emission.log] at gcl
  rw [procExit, added_congr ecl.symm rfl, leaf_added, gcl]
  unfold procWords procExit
  split <;> simp [gensWords]

theorem procExit_prefix (ctx : Ctx n) (level nc : Nat) (s : Search n) :
    s.emitted.toList <+: (procExit ctx level nc s).2.emitted.toList := by
  have ecl := emitted_of_log (classify_log ctx level nc s)
  exact leaf_prefix _ _ _ _ (by rw [Emission.log, ecl]; exact List.prefix_refl _)

theorem emLawOff (ctx : Ctx n) : EmLawOff (emWords ctx) ctx := by
  intro level nc st h1 hn
  rw [emWords, hexNode, nodeFuel_succ hn, node_false_succ]
  dsimp only
  have e0 : (chooseTarget false ctx 100 level (visit ctx level nc st).1
      (compareCodes level (visit ctx level nc st).2.1 (visit ctx level nc st).2.2)).2.2.2.emitted =
      st.emitted :=
    (emitted_of_log (target_log ..)).trans (emitted_of_log (Emission.compare_log ..))
  rw [added_congr (a := (chooseTarget false ctx 100 level (visit ctx level nc st).1
      (compareCodes level (visit ctx level nc st).2.1 (visit ctx level nc st).2.2)).2.2.2)
      e0.symm rfl]
  generalize (chooseTarget false ctx 100 level (visit ctx level nc st).1
      (compareCodes level (visit ctx level nc st).2.1 (visit ctx level nc st).2.2)) = ct
  generalize (visit ctx level nc st).1 = nc1
  obtain ⟨tc, tcell, size, s⟩ := ct
  dsimp only
  rw [← procExit_added]
  have hpre := procExit_prefix ctx level nc1 s
  simp only [procExit] at hpre ⊢
  generalize leafExit (classify ctx level nc1 s).1 level (classify ctx level nc1 s).2 = x at hpre ⊢
  obtain ⟨e, s'⟩ := x
  cases e with
  | done =>
    dsimp only
    have hc : (cheapCheck false level s').emitted = s'.emitted :=
      emitted_of_log (Emission.cheap_log ..)
    have hsw := sweep_prefix false ctx nautyInf 100 (nodeFuel n (level + 1)) (n + 1) level nc1
      tc.toNat ((tcell.nextElem none).getD 0) (tcell.nextElem none) tcell 0 (cheapCheck false level s')
    rw [hc] at hsw
    dsimp only at hpre
    rw [ite_eq_left rfl]
    rw [← sweep_false_added ctx level nc1 tc.toNat ((tcell.nextElem none).getD 0) (n + 1)
      (tcell.nextElem none) tcell 0, added_congr hc rfl, ← gensWords_append, ← added_trans hpre hsw]
    generalize sweep false ctx nautyInf 100 (nodeFuel n (level + 1)) (n + 1) level nc1
      tc.toNat ((tcell.nextElem none).getD 0) (tcell.nextElem none) tcell 0
      (cheapCheck false level s') = out
    obtain ⟨e2, idx, s2⟩ := out
    cases e2 with
    | done =>
      exact congrArg (gensWords · n) (added_congr rfl (emitted_of_log (Emission.afterSweep_log ..)))
    | _ => rfl
  | _ => simp

theorem emLawFirst (ctx : Ctx n) : EmLawFirst (emWords ctx) ctx := by
  intro level nc st h1 hn
  rw [emWords, hexNode, nodeFuel_succ hn, node_true_succ]
  dsimp only
  have e0 : (chooseTarget true ctx 100 level (visit ctx level nc st).1
      (recordFirst level (visit ctx level nc st).2.1 (visit ctx level nc st).2.2)).2.2.2.emitted =
      st.emitted :=
    emitted_of_log (target_log ..)
  rw [added_congr (a := (chooseTarget true ctx 100 level (visit ctx level nc st).1
      (recordFirst level (visit ctx level nc st).2.1 (visit ctx level nc st).2.2)).2.2.2)
      e0.symm rfl]
  generalize (chooseTarget true ctx 100 level (visit ctx level nc st).1
      (recordFirst level (visit ctx level nc st).2.1 (visit ctx level nc st).2.2)) = ct
  generalize (visit ctx level nc st).1 = nc1
  obtain ⟨tc, tcell, size, s⟩ := ct
  dsimp only
  by_cases hnc : nc1 = n
  · rw [ite_eq_left hnc, ite_eq_left hnc]
    rw [added_congr rfl (show (firstterminal level s).emitted = s.emitted from rfl), added_self]
    rfl
  · rw [ite_eq_right hnc, ite_eq_right hnc]
    have hc : (cheapCheck true level s).emitted = s.emitted :=
      emitted_of_log (Emission.cheap_log ..)
    rw [← sweep_true_added ctx level nc1 tc.toNat ((tcell.nextElem none).getD 0) (n + 1)
      (tcell.nextElem none) tcell 0, added_congr hc rfl]
    generalize sweep true ctx nautyInf 100 (nodeFuel n (level + 1)) (n + 1) level nc1
      tc.toNat ((tcell.nextElem none).getD 0) (tcell.nextElem none) tcell 0
      (cheapCheck true level s) = out
    obtain ⟨e2, idx, s2⟩ := out
    cases e2 with
    | done =>
      exact congrArg (gensWords · n) (added_congr rfl (emitted_of_log (Emission.afterSweep_log ..)))
    | _ => rfl

end NautyVerified.Proofs.Search

import NautyVerified.Spec.SearchInf
import NautyVerified.Spec.LeafInv
import HexGraphIso.Nauty.Policy.Boundary
import HexGraphIso.Nauty.Policy.Depth
import HexGraphIso.Nauty.Policy.First.State
import HexGraphIso.Nauty.Policy.First.Path

/-!
# The search with `inf = 2000000002`

`node_inf`: HexGraphIso's search run with `ptn`'s "infinity" `2000000002`
from a state whose `ptn` uses `2000000002` where HexGraphIso's uses `n + 2`,
and whose `firsttc` may differ before it is written, returns the same exit
and the same state up to those two fields.

Two runs are related by `tw (phi (n + 2) B) t`: the second has the first's
state with `ptn` mapped and `firsttc` replaced by `t`. Before the first leaf
the search is on the first path, which writes `firsttc[level]` before
anything reads it; `t` agrees with the first run's `firsttc` on the levels
already written (`AgreeTo`). After the first leaf at level `last`,
HexGraphIso's `Depth last` keeps every hinted read at a level at most
`last`, where the two agree. The proof is a `Generic.SoundPolicy` for a
contract extending HexGraphIso's partition-reachability contract, whose
`SearchOk` bounds every level by `n`.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n k : Nat}

/-- `t` agrees with `s` on positions `1 … A`. -/
def AgreeTo (A : Nat) (t s : Array Int) : Prop :=
  t.size = s.size ∧ ∀ i, 1 ≤ i → i ≤ A → t[i]! = s[i]!

theorem AgreeTo.mono {A B : Nat} {t s : Array Int} (h : AgreeTo A t s) (hBA : B ≤ A) :
    AgreeTo B t s := ⟨h.1, fun i h1 h2 => h.2 i h1 (by omega)⟩

theorem AgreeTo.set {A : Nat} {t s : Array Int} (h : AgreeTo A t s) (v : Int) :
    AgreeTo (A + 1) (t.set! (A + 1) v) (s.set! (A + 1) v) := by
  refine ⟨by simp [h.1], fun i h1 h2 => ?_⟩
  by_cases hi : i = A + 1
  · subst hi
    by_cases hs : A + 1 < s.size
    · rw [Array.getElem!_set!_self _ _ _ (by rw [h.1]; exact hs), Array.getElem!_set!_self _ _ _ hs]
    · rw [getElem!_neg _ _ (by simp [h.1]; omega), getElem!_neg _ _ (by simp; omega)]
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hi), Array.getElem!_set!_ne _ _ _ _ (Ne.symm hi)]
    exact h.2 i h1 (by omega)

/-- No automorphism has been found: every vertex is its own orbit. -/
def OrbId (st : Search n) : Prop := ∀ v, v < n → st.orbits[v]! = v

/-- Facts every call keeps: the `noncheaplevel` bound the leaf code's `fmptn`
needs, the size of the first-path codes, and what a leaf may rely on (`LeafI`). -/
def Inv (st : Search n) : Prop := st.noncheaplevel ≤ n + 1 ∧ st.firstcode.size = n + 2 ∧ LeafI st

/-- The initial state meets `Inv`: no first leaf yet, `noncheaplevel = 1`, coset index `0`. -/
theorem initial_inv (hn0 : 0 < n) (lab0 : Array Nat) (cellEnds : List Nat) :
    Inv (initial n lab0 cellEnds) :=
    ⟨by show 1 ≤ n + 1; omega, by simp [initial], Nat.le_refl 1, hn0, fun ⟨i, hi⟩ => by
      change (Array.replicate (n + 2) 0)[i]! = codeSentinel at hi
      by_cases h : i < n + 2
      · rw [getElem!_pos _ i (by simpa using h)] at hi; simp [codeSentinel] at hi
      · rw [getElem!_neg _ i (by simpa using h)] at hi; simp [codeSentinel] at hi⟩

theorem level_le_of_ok {G : Colored n k} {level numcells : Nat} {st : Search n}
    (h : SearchOk G level numcells st) : level ≤ n :=
  Nat.le_trans h.bc (bcount_le _ _ _)

/-- A first-path node that is not a leaf has a nonempty target cell. -/
theorem first_cell_some {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (hn0 : 0 < n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (hnc : numcells ≠ n) :
    ∃ v, (chooseTarget true ctx tcLevel level numcells st).2.1.nextElem none = some v := by
  have hend := searchOk_end hn0 hok hlevel
  have hlive : bcount st.ptn level n < n := by
    have hc := hok.count
    have := bcount_le st.ptn level n
    change numcells = bcount st.ptn level n at hc
    omega
  obtain ⟨tc, len, hr, -, hlen, hrange⟩ :=
    maketargetcell_open (ctx := ctx) (lab := st.lab) (ptn := st.ptn) (tcLevel := tcLevel)
      (hint := -1) hlevel hok.ptnSize hend hlive
  have hcell : (chooseTarget true ctx tcLevel level numcells st).2.1 =
      worksetOf n st.lab tc (tc + len - 1) := by
    unfold chooseTarget
    simp only [Id.run, ite_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false,
      show (numcells != n) = true by simpa using hnc, hr]
    rfl
  have hv : (worksetOf n st.lab tc (tc + len - 1)).mem st.lab[tc]! = true := by
    rw [mem_worksetOf_iff]
    refine ⟨cellsReach_lt hok.reach tc (by omega), ?_⟩
    simp only [segN, List.mem_map, List.mem_range]
    exact ⟨0, by omega, by simp⟩
  rcases hs : (chooseTarget true ctx tcLevel level numcells st).2.1.nextElem none with _ | v
  · have := VSet.nextElem_none hs st.lab[tc]! (Nat.zero_le _)
    rw [hcell, hv] at this; cases this
  · exact ⟨v, rfl⟩

/-- The relation between the two runs: HexGraphIso's partition-reachability
contract, and under `Inv` the second run (with infinity `B`, from the first
run's state related by `tw (phi (n + 2) B) t`) returns the related result. -/
def infContract (G : Colored n k) (ctx : Ctx n) (tcLevel B : Nat) : Generic.Contract (Search n) n where
  nodePre _ _ level numcells st := 1 ≤ level ∧ SearchOk G level numcells st
  nodePost fuel first level numcells st r :=
    SearchOut G (level - 1) level st r.2 ∧ (Inv st →
      (first = false → ∀ last t, Depth last st → AgreeTo (last + 1) t st.firsttc →
        Generic.node false ctx B tcLevel fuel level numcells (tw (phi (n + 2) B) t st) =
          (r.1, tw (phi (n + 2) B) t r.2) ∧ Depth last r.2 ∧ r.2.firsttc = st.firsttc ∧ Inv r.2) ∧
      (first = true → ∀ t, OrbId st → AgreeTo (level - 1) t st.firsttc →
        ∃ t', Generic.node true ctx B tcLevel fuel level numcells (tw (phi (n + 2) B) t st) =
          (r.1, tw (phi (n + 2) B) t' r.2) ∧
          (r.1 = .fuel ∨ ∃ last, Depth last r.2 ∧ AgreeTo (last + 1) t' r.2.firsttc) ∧ Inv r.2))
  sweepPre _ _ _ level numcells tc _ cursor cell _ st :=
    1 ≤ level ∧ SearchOk G level numcells st ∧ Generic.Target (fun st => st) level tc cell st ∧
      ∀ v, cursor = some v → cell.mem v = true
  sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st r :=
    SearchOut G level level st r.2.2 ∧ (Inv st →
      (Generic.Past first tv1 cursor → ∀ last t, Depth last st → AgreeTo (last + 1) t st.firsttc →
        Generic.sweep first ctx B tcLevel fuel cfuel level numcells tc tv1 cursor cell index
            (tw (phi (n + 2) B) t st) = (r.1, r.2.1, tw (phi (n + 2) B) t r.2.2) ∧
          Depth last r.2.2 ∧ r.2.2.firsttc = st.firsttc ∧ Inv r.2.2) ∧
      (first = true → cursor = some tv1 → ∀ t, OrbId st → AgreeTo level t st.firsttc →
        ∃ t', Generic.sweep true ctx B tcLevel fuel cfuel level numcells tc tv1 cursor cell index
            (tw (phi (n + 2) B) t st) = (r.1, r.2.1, tw (phi (n + 2) B) t' r.2.2) ∧
          (r.1 = .fuel ∨ ∃ last, Depth last r.2.2 ∧ AgreeTo (last + 1) t' r.2.2.firsttc) ∧ Inv r.2.2))

section
variable {G : Colored n k} {ctx : Ctx n} {tcLevel B : Nat}

theorem infContract_node_zero (first : Bool) (level numcells : Nat) (st : Search n)
    (hin : (infContract G ctx tcLevel B).nodePre 0 first level numcells st) :
    (infContract G ctx tcLevel B).nodePost 0 first level numcells st (.fuel, st) := by
  refine ⟨SearchOut.refl G (level - 1) level hin.2.reach, fun hinv => ⟨?_, ?_⟩⟩
  · intro _ last t hd _
    exact ⟨by simp [Generic.node], hd, rfl, hinv⟩
  · intro _ t _ _
    exact ⟨t, by simp [Generic.node], .inl rfl, hinv⟩

theorem infContract_sweep_none (fuel cfuel : Nat) (first : Bool) (level numcells tc tv1 : Nat)
    (cell : VSet n) (index : Nat) (st : Search n)
    (hin : (infContract G ctx tcLevel B).sweepPre fuel cfuel first level numcells tc tv1 none cell
      index st) :
    (infContract G ctx tcLevel B).sweepPost fuel cfuel first level numcells tc tv1 none cell index st
      (.done, index, st) := by
  refine ⟨SearchOut.refl G level level hin.2.1.reach, fun hinv => ⟨?_, ?_⟩⟩
  · intro _ last t hd _
    exact ⟨by simp [Generic.sweep], hd, rfl, hinv⟩
  · intro _ h; cases h

theorem infContract_sweep_zero (fuel : Nat) (first : Bool) (level numcells tc tv1 tv : Nat)
    (cell : VSet n) (index : Nat) (st : Search n)
    (hin : (infContract G ctx tcLevel B).sweepPre fuel 0 first level numcells tc tv1 (some tv) cell
      index st) :
    (infContract G ctx tcLevel B).sweepPost fuel 0 first level numcells tc tv1 (some tv) cell index st
      (.fuel, index, st) := by
  refine ⟨SearchOut.refl G level level hin.2.1.reach, fun hinv => ⟨?_, ?_⟩⟩
  · intro _ last t hd _
    exact ⟨by simp [Generic.sweep], hd, rfl, hinv⟩
  · intro _ _ t _ _
    exact ⟨t, by simp [Generic.sweep], .inl rfl, hinv⟩

theorem nodeStep_off (hn0 : 0 < n) (hB : n + 2 < B) (fuel : Nat) (next : Generic.SweepFn (Search n) n)
    (hnext : (infContract G ctx tcLevel B).sweepValid fuel (n + 1) next)
    (level numcells : Nat) (st : Search n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (hinv : Inv st) (last : Nat) (t : Array Int) (hd : Depth last st)
    (ha : AgreeTo (last + 1) t st.firsttc) :
    Generic.nodeStep ctx tcLevel (fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first ctx B tcLevel fuel (n + 1) level numcells tc tv1 cursor cell index st)
        false level numcells (tw (phi (n + 2) B) t st) =
      ((Generic.nodeStep ctx tcLevel next false level numcells st).1,
        tw (phi (n + 2) B) t (Generic.nodeStep ctx tcLevel next false level numcells st).2) ∧
      Depth last (Generic.nodeStep ctx tcLevel next false level numcells st).2 ∧
      (Generic.nodeStep ctx tcLevel next false level numcells st).2.firsttc = st.firsttc ∧
      Inv (Generic.nodeStep ctx tcLevel next false level numcells st).2 := by
  have hln := level_le_of_ok hok
  have hL1 : level < n + 2 := by omega
  have hL2 : level < B := by omega
  have R := reachPolicy G ctx tcLevel hn0
  have D := depthPolicy ctx (n + 2) tcLevel last
  have F := referencePolicy ctx (n + 2) tcLevel
  have hrf : ∀ {x y : Search n}, x.reference = y.reference → x.firsttc = y.firsttc ∧
      x.firstcode = y.firstcode := fun h =>
    ⟨congrArg (fun r => r.2.1) h, congrArg (fun r => r.1) h⟩
  -- refinement
  have hv := R.visit level numcells st hlevel hok
  have hvd := D.visit level numcells st hd
  have hvf := F.visit level numcells st
  have hcode := D.code level numcells st
  have hvi : Inv (visit ctx level numcells st).2.2 := hinv
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.firstterminal,
    Generic.Policy.classify, Generic.Policy.leafExit, Generic.Policy.cheapCheck,
    Generic.Policy.afterSweep] at hv hvd hvf hcode ⊢
  rw [visit_tw t ctx level numcells st hL1 hL2]
  generalize visit ctx level numcells st = r at hv hvd hvf hcode hvi ⊢
  obtain ⟨nc, code, s1⟩ := r
  obtain ⟨hok1, -⟩ := hv
  dsimp only at hok1 hvd hvf hcode hvi ⊢
  simp only [Bool.false_eq_true, ite_false]
  -- code comparison
  have hcd := compareCodes_depth (level := level) hvd hcode
  have hcf := F.compare level code s1
  have hcl := R.compare level code nc s1 hok1
  dsimp only [policy, Generic.Policy.compareCodes] at hcf hcl
  have hci : Inv (compareCodes level code s1) :=
    ⟨by rw [compare_noncheap]; exact hvi.1, by rw [(hrf hcf).2]; exact hvi.2.1,
      leafI_compare hvi.2.2 level code⟩
  rw [compareCodes_tw]
  generalize compareCodes level code s1 = s2 at hcd hcf hcl hci ⊢
  -- target
  have ht : false = false → s2.eqlevFirst = level → t[level]! = s2.firsttc[level]! := by
    intro _ he
    rw [(hrf hcf).1, (hrf hvf).1]
    exact ha.2 level hlevel (by have := hcd.1; omega)
  rw [chooseTarget_tw t false ctx tcLevel level nc s2 hL1 hL2 ht]
  have htd := D.target level nc s2 hcd
  have htf := F.target level nc s2
  have htr := R.target false level nc s2 hlevel hcl.ok
  dsimp only [policy, Generic.Policy.chooseTarget] at htd htf htr
  have hti : Inv (chooseTarget false ctx tcLevel level nc s2).2.2.2 :=
    ⟨by rw [target_noncheap]; exact hci.1, by rw [(hrf htf).2]; exact hci.2.1,
      leafI_target hci.2.2 false ctx tcLevel level nc⟩
  generalize chooseTarget false ctx tcLevel level nc s2 = c at htd htf htr hti ⊢
  obtain ⟨tc, cell, size, s3⟩ := c
  obtain ⟨htl, htarget⟩ := htr
  dsimp only at htd htf htl htarget hti ⊢
  simp only [Bool.false_eq_true, ite_false]
  -- classification
  rw [classify_tw]
  have hcld := (D.classify level nc s3 htd).1
  have hclf := F.classify level nc s3
  have hclr := R.classify level nc s3 htl.ok
  dsimp only [policy, Generic.Policy.classify] at hcld hclf hclr
  have hcli : Inv (classify ctx level nc s3).2 :=
    ⟨by rw [classify_noncheap]; exact hti.1, by rw [(hrf hclf).2]; exact hti.2.1,
      leafI_classify hti.2.2 ctx level nc⟩
  generalize classify ctx level nc s3 = cl at hcld hclf hclr hcli ⊢
  obtain ⟨leaf, s4⟩ := cl
  dsimp only at hcld hclf hclr hcli ⊢
  -- leaf action
  rw [leafExit_tw t leaf level s4 (by have := hcli.1; omega) (by have := hcli.1; omega)]
  have hled := D.leaf leaf level s4 trivial hcld
  have hlef := F.leaf leaf level s4
  have hler := R.leaf leaf level nc s4 hclr.ok
  dsimp only [policy, Generic.Policy.leafExit] at hled hlef hler
  have hlei : Inv (leafExit leaf level s4).2 :=
    ⟨by rw [leafExit_noncheap]; exact hcli.1, by rw [(hrf hlef).2]; exact hcli.2.1,
      leafI_leafExit hcli.2.2 leaf level (labPerm_of_ok hn0 hclr.ok)⟩
  generalize leafExit leaf level s4 = le at hled hlef hler hlei ⊢
  obtain ⟨exit, s5⟩ := le
  dsimp only at hled hlef hler hlei ⊢
  have hf5 : s5.firsttc = st.firsttc := by
    rw [(hrf hlef).1, (hrf hclf).1, (hrf htf).1, (hrf hcf).1, (hrf hvf).1]
  cases exit with
  | fuel => exact ⟨rfl, hled, hf5, hlei⟩
  | unwind target short => exact ⟨rfl, hled, hf5, hlei⟩
  | done =>
    simp only []
    rw [cheapCheck_tw t false level s5 hL1 hL2]
    have hchd := D.cheap false level s5 hled
    have hchf := F.cheap false level s5
    have hchr := R.cheap false level nc s5 hler.ok
    dsimp only [policy, Generic.Policy.cheapCheck] at hchd hchf hchr
    have hchi : Inv (cheapCheck false level s5) := by
      refine ⟨?_, by rw [(hrf hchf).2]; exact hlei.2.1, leafI_cheap hlei.2.2 false level⟩
      unfold cheapCheck; split
      · show level + 1 ≤ n + 1; omega
      · exact hlei.1
    have htarget6 : Generic.Target (fun st => st) level tc.toNat cell (cheapCheck false level s5) :=
      ((htarget.of_out hclr.effect).of_out hler.effect).of_out hchr.effect
    have hsw := hnext false level nc tc.toNat ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0
      (cheapCheck false level s5) ⟨hlevel, hchr.ok, htarget6, fun v hv => VSet.nextElem_mem hv⟩
    obtain ⟨-, himp⟩ := hsw
    obtain ⟨hoff, -⟩ := himp hchi
    have ha6 : AgreeTo (last + 1) t (cheapCheck false level s5).firsttc := by
      rw [(hrf hchf).1, hf5]; exact ha
    obtain ⟨heq, hd7, hf7, hinv7⟩ := hoff (fun h => absurd h (by decide)) last t hchd ha6
    rw [heq]
    generalize next false level nc tc.toNat ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0
      (cheapCheck false level s5) = r7 at hinv7 hd7 hf7 ⊢
    obtain ⟨exit7, index, s7⟩ := r7
    dsimp only at hinv7 hd7 hf7 ⊢
    have hf7' : s7.firsttc = st.firsttc := by rw [hf7, (hrf hchf).1, hf5]
    cases exit7 with
    | done =>
      simp only []
      rw [afterSweep_tw]
      refine ⟨rfl, ?_, ?_, ?_⟩
      · have := D.afterSweep level size index s7 hd7
        exact this
      · unfold afterSweep; split <;> exact hf7'
      · unfold afterSweep; split <;> exact hinv7
    | fuel => exact ⟨rfl, hd7, hf7', hinv7⟩
    | unwind target short => exact ⟨rfl, hd7, hf7', hinv7⟩

theorem nodeStep_first (hn0 : 0 < n) (hB : n + 2 < B) (fuel : Nat)
    (next : Generic.SweepFn (Search n) n)
    (hnext : (infContract G ctx tcLevel B).sweepValid fuel (n + 1) next)
    (level numcells : Nat) (st : Search n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (hinv : Inv st) (t : Array Int) (horb : OrbId st) (ha : AgreeTo (level - 1) t st.firsttc) :
    ∃ t', Generic.nodeStep ctx tcLevel (fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first ctx B tcLevel fuel (n + 1) level numcells tc tv1 cursor cell index st)
        true level numcells (tw (phi (n + 2) B) t st) =
      ((Generic.nodeStep ctx tcLevel next true level numcells st).1,
        tw (phi (n + 2) B) t' (Generic.nodeStep ctx tcLevel next true level numcells st).2) ∧
      ((Generic.nodeStep ctx tcLevel next true level numcells st).1 = .fuel ∨
        ∃ last, Depth last (Generic.nodeStep ctx tcLevel next true level numcells st).2 ∧
          AgreeTo (last + 1) t' (Generic.nodeStep ctx tcLevel next true level numcells st).2.firsttc) ∧
      Inv (Generic.nodeStep ctx tcLevel next true level numcells st).2 := by
  have hln := level_le_of_ok hok
  have hL1 : level < n + 2 := by omega
  have hL2 : level < B := by omega
  have R := reachPolicy G ctx tcLevel hn0
  -- refinement
  have hv := R.visit level numcells st hlevel hok
  have hvi : Inv (visit ctx level numcells st).2.2 := hinv
  have hvo : OrbId (visit ctx level numcells st).2.2 := horb
  have hva : AgreeTo (level - 1) t (visit ctx level numcells st).2.2.firsttc := ha
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.firstterminal,
    Generic.Policy.classify, Generic.Policy.leafExit, Generic.Policy.cheapCheck,
    Generic.Policy.afterSweep] at hv ⊢
  have hcode := (depthPolicy ctx (n + 2) tcLevel 0).code level numcells st
  dsimp only [policy, Generic.Policy.visit] at hcode
  rw [visit_tw t ctx level numcells st hL1 hL2]
  generalize visit ctx level numcells st = r at hv hvi hvo hva hcode ⊢
  obtain ⟨nc, code, s1⟩ := r
  obtain ⟨hok1, -⟩ := hv
  dsimp only at hok1 hvi hvo hva hcode ⊢
  simp only [ite_true]
  -- the first-path code
  rw [recordFirst_tw]
  have hrl := R.record level code nc s1 hok1
  dsimp only [policy, Generic.Policy.recordFirst] at hrl
  have hri : Inv (recordFirst level code s1) := ⟨hvi.1, by simp [recordFirst, hvi.2.1],
    leafI_record hvi.2.2 hcode⟩
  have hro : OrbId (recordFirst level code s1) := hvo
  have hra : AgreeTo (level - 1) t (recordFirst level code s1).firsttc := hva
  generalize recordFirst level code s1 = s2 at hrl hri hro hra ⊢
  -- target
  rw [chooseTarget_tw t true ctx tcLevel level nc s2 hL1 hL2 (fun h => absurd h (by decide))]
  have htr := R.target true level nc s2 hlevel hrl.ok
  dsimp only [policy, Generic.Policy.chooseTarget] at htr
  have hcs := chooseFirst_fields ctx tcLevel level nc s2
  have hcell := first_cell_some (ctx := ctx) (tcLevel := tcLevel) hn0 hlevel hrl.ok
  generalize chooseTarget true ctx tcLevel level nc s2 = c at htr hcs hcell ⊢
  obtain ⟨tc, cell, size, s3⟩ := c
  obtain ⟨htl, htarget⟩ := htr
  dsimp only at htl htarget hcs hcell ⊢
  simp only [ite_true]
  have hi3 : Inv s3 := by rw [hcs]; exact hri
  have ho3 : OrbId s3 := by rw [hcs]; exact hro
  have ha3 : AgreeTo level (t.set! level tc) s3.firsttc := by
    rw [hcs]
    have := hra.set tc
    rwa [Nat.sub_add_cancel hlevel] at this
  by_cases hleaf : (nc == n) = true
  · simp only [hleaf, ite_true]
    refine ⟨(t.set! level tc).set! (level + 1) (-1), by rw [firstterminal_tw]; rfl, .inr ⟨level, ?_, ?_⟩, ?_⟩
    · refine ⟨Nat.le_refl _, ?_⟩
      show (s3.firstcode.set! (level + 1) codeSentinel)[level + 1]! = codeSentinel
      exact Array.getElem!_set!_self _ _ _ (by rw [hi3.2.1]; omega)
    · exact ha3.set (-1)
    · exact ⟨hi3.1, by show (s3.firstcode.set! (level + 1) codeSentinel).size = n + 2; simp [hi3.2.1],
        leafI_firstterminal hi3.2.2 level (labPerm_of_ok hn0 htl.ok)⟩
  · simp only [hleaf, Bool.false_eq_true, ite_false]
    obtain ⟨v, hv⟩ := hcell (by simpa using hleaf)
    rw [cheapCheck_tw (t.set! level tc) true level s3 hL1 hL2]
    have hchr := R.cheap true level nc s3 htl.ok
    dsimp only [policy, Generic.Policy.cheapCheck] at hchr
    have hcheq : ∃ k', cheapCheck true level s3 = { s3 with noncheaplevel := k' } ∧ k' ≤ n + 1 := by
      unfold cheapCheck; split
      · exact ⟨level + 1, rfl, by omega⟩
      · exact ⟨s3.noncheaplevel, rfl, hi3.1⟩
    obtain ⟨k', hk', hk'le⟩ := hcheq
    have hchi : Inv (cheapCheck true level s3) :=
      ⟨by rw [hk']; exact hk'le, by rw [hk']; exact hi3.2.1, leafI_cheap hi3.2.2 true level⟩
    have hcho : OrbId (cheapCheck true level s3) := by rw [hk']; exact ho3
    have hcha : AgreeTo level (t.set! level tc) (cheapCheck true level s3).firsttc := by
      rw [hk']; exact ha3
    have htarget6 : Generic.Target (fun st => st) level tc.toNat cell (cheapCheck true level s3) :=
      htarget.of_out hchr.effect
    rw [hv]
    have hsw := hnext true level nc tc.toNat v (some v) cell 0
      (cheapCheck true level s3) ⟨hlevel, hchr.ok, htarget6, fun w hw => by
        cases hw; exact VSet.nextElem_mem hv⟩
    obtain ⟨-, himp⟩ := hsw
    obtain ⟨-, hfirst⟩ := himp hchi
    obtain ⟨t'', heq, hph, hinv7⟩ := hfirst rfl rfl (t.set! level tc) hcho hcha
    simp only [Option.getD_some] at heq ⊢
    rw [heq]
    generalize next true level nc tc.toNat v (some v) cell 0 (cheapCheck true level s3) = r7
      at hinv7 hph ⊢
    obtain ⟨exit7, index, s7⟩ := r7
    dsimp only at hinv7 hph ⊢
    refine ⟨t'', ?_⟩
    cases exit7 with
    | done =>
      simp only []
      rw [afterSweep_tw]
      refine ⟨rfl, .inr ?_, ?_⟩
      · rcases hph with h | ⟨last, hd7, ha7⟩
        · cases h
        · refine ⟨last, ?_, ?_⟩
          · unfold afterSweep; split <;> exact hd7
          · unfold afterSweep; split <;> exact ha7
      · unfold afterSweep; split <;> exact hinv7
    | fuel => exact ⟨rfl, .inl rfl, hinv7⟩
    | unwind target short =>
      refine ⟨rfl, ?_, hinv7⟩
      rcases hph with h | h
      · cases h
      · exact .inr h

theorem ref_fields {x y : Search n} (h : x.reference = y.reference) :
    x.firsttc = y.firsttc ∧ x.firstcode = y.firstcode :=
  ⟨congrArg (fun r => r.2.1) h, congrArg (fun r => r.1) h⟩

theorem child_inv {first : Bool} {level tc tv : Nat} {st : Search n} (h : Inv st)
    (htv : first = true → tv < n) : Inv (child first level tc tv st) := by
  have hl := leafI_child h.2.2 first level tc tv htv
  cases first
  · exact ⟨h.1, h.2.1, hl⟩
  · exact ⟨h.1, h.2.1, hl⟩

theorem child_orbId {first : Bool} {level tc tv : Nat} {st : Search n} (h : OrbId st) :
    OrbId (child first level tc tv st) := by
  cases first <;> exact h

/-- The continuation of a sweep after a child returns: prune, recover, sweep on. -/
theorem resume_off (hn0 : 0 < n) (hB : n + 2 < B) (fuel cfuel : Nat)
    (next : Generic.SweepFn (Search n) n)
    (hnext : (infContract G ctx tcLevel B).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv : Nat) (cell cell' : VSet n) (index : Nat)
    (base out : Search n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells base)
    (htarget : Generic.Target (fun st => st) level tc cell base)
    (hout : SearchOut G level level base out) (hsub : ∀ v, cell'.mem v = true → cell.mem v = true)
    (hpast : first = true → tv1 ≤ tv) (hinv : Inv out) (last : Nat) (t : Array Int)
    (hd : Depth last out) (ha : AgreeTo (last + 1) t out.firsttc) :
    Generic.resume B (fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first ctx B tcLevel fuel cfuel level numcells tc tv1 cursor cell index st)
        first level numcells tc tv1 tv cell' index (tw (phi (n + 2) B) t out) =
      ((Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).1,
        (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.1,
        tw (phi (n + 2) B) t (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2) ∧
      Depth last (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2 ∧
      (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2.firsttc =
        out.firsttc ∧
      Inv (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2 ∧
      SearchOut G level level base
        (Generic.resume (n + 2) next first level numcells tc tv1 tv cell' index out).2.2 := by
  have hln := level_le_of_ok hok
  have R := reachPolicy G ctx tcLevel hn0
  have D := depthPolicy ctx (n + 2) tcLevel last
  have F := referencePolicy ctx (n + 2) tcLevel
  have hr := R.recover level numcells base out hlevel hok hout
  have hrd := D.recover level out hd
  have hrf := F.recover level out
  dsimp only [policy, Generic.Policy.recover] at hr hrd hrf
  have hri : Inv (recover (n + 2) level out) := by
    refine ⟨?_, by rw [(ref_fields hrf).2]; exact hinv.2.1, leafI_recover hinv.2.2 (n + 2) level⟩
    rw [recover_noncheap]; split <;> omega
  -- the pruned cell
  let cell'' := if (!first && tv == tv1) = true then longprune cell' out.fixedpts out.autos else cell'
  have hsub' : ∀ v, cell''.mem v = true → cell.mem v = true := by
    intro v hv
    simp only [cell''] at hv
    split at hv
    · exact hsub v (R.long cell' out v hv)
    · exact hsub v hv
  have hsw := hnext first level numcells tc tv1 (cell''.nextElem (some tv)) cell''
    (if (first && (recover (n + 2) level out).orbits[tv]! == tv1) = true then index + 1 else index)
    (recover (n + 2) level out)
    ⟨hlevel, hr.ok, (htarget.subset hsub').of_out hr.effect, fun v hv => VSet.nextElem_mem hv⟩
  obtain ⟨hsout, himp⟩ := hsw
  obtain ⟨hoff, -⟩ := himp hri
  have ha' : AgreeTo (last + 1) t (recover (n + 2) level out).firsttc := by
    rw [(ref_fields hrf).1]; exact ha
  have hP : Generic.Past first tv1 (cell''.nextElem (some tv)) := by
    intro hf v hv
    have := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at this
    have := hpast hf
    omega
  obtain ⟨heq, hd', hf', hinv'⟩ := hoff hP last t hrd ha'
  have hf'' : (next first level numcells tc tv1 (cell''.nextElem (some tv)) cell''
      (if (first && (recover (n + 2) level out).orbits[tv]! == tv1) = true then index + 1 else index)
      (recover (n + 2) level out)).2.2.firsttc = out.firsttc := by
    rw [hf', (ref_fields hrf).1]
  unfold Generic.resume
  dsimp only [policy, Generic.Policy.longprune, Generic.Policy.recover, Generic.Policy.orbit]
  simp only [Id.run]
  rw [recover_tw t level out (by omega) (by omega)]
  by_cases hlp : (!first && tv == tv1) = true
  · simp only [cell'', hlp, ite_true] at heq hd' hf'' hinv' hsout ⊢
    exact ⟨heq, hd', hf'', hinv', hr.effect.trans hsout⟩
  · simp only [cell'', hlp, Bool.false_eq_true, ite_false] at heq hd' hf'' hinv' hsout ⊢
    exact ⟨heq, hd', hf'', hinv', hr.effect.trans hsout⟩

theorem sweepStep_off (hn0 : 0 < n) (hB : n + 2 < B) (fuel cfuel : Nat)
    (descend : Generic.NodeFn (Search n)) (next : Generic.SweepFn (Search n) n)
    (hdescend : (infContract G ctx tcLevel B).nodeValid fuel descend)
    (hnext : (infContract G ctx tcLevel B).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv : Nat) (cell : VSet n) (index : Nat) (st : Search n)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true)
    (hpast : first = true → tv1 < tv) (hinv : Inv st) (last : Nat) (t : Array Int)
    (hd : Depth last st) (ha : AgreeTo (last + 1) t st.firsttc) :
    Generic.sweepStep B (fun first level numcells st => Generic.node first ctx B tcLevel fuel level numcells st)
        (fun first level numcells tc tv1 cursor cell index st =>
          Generic.sweep first ctx B tcLevel fuel cfuel level numcells tc tv1 cursor cell index st)
        first level numcells tc tv1 tv cell index (tw (phi (n + 2) B) t st) =
      ((Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).1,
        (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.1,
        tw (phi (n + 2) B) t (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell
          index st).2.2) ∧
      Depth last (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2 ∧
      (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2.firsttc =
        st.firsttc ∧
      Inv (Generic.sweepStep (n + 2) descend next first level numcells tc tv1 tv cell index st).2.2 := by
  have hln := level_le_of_ok hok
  have R := reachPolicy G ctx tcLevel hn0
  have D := depthPolicy ctx (n + 2) tcLevel last
  have F := referencePolicy ctx (n + 2) tcLevel
  have hft : (first && tv == tv1) = false := by
    cases first
    · rfl
    · simp only [Bool.true_and, beq_eq_false_iff_ne]; have := hpast rfl; omega
  unfold Generic.sweepStep
  dsimp only [policy, Generic.Policy.orbit, Generic.Policy.child, Generic.Policy.afterChildFirst,
    Generic.Policy.leaveChild]
  simp only [Id.run]
  have e0 : (tw (phi (n + 2) B) t st).orbits = st.orbits := rfl
  by_cases hc : (!first || st.orbits[tv]! == tv) = true
  · have hc' : (!first || (tw (phi (n + 2) B) t st).orbits[tv]! == tv) = true := hc
    simp only [hc, hc', ite_true, hft, Bool.false_eq_true, ite_false]
    rw [child_tw t first level tc tv st (by omega)]
    have hch := R.child first level numcells tc tv cell st hlevel hok htarget htv
    have hcd := D.child first level tc tv st hd
    have hcf := F.child first level tc tv st
    dsimp only [policy, Generic.Policy.child] at hch hcd hcf
    obtain ⟨hokc, hceff⟩ := hch
    have hdn := hdescend false (level + 1) (numcells + 1) (child first level tc tv st) ⟨by omega, hokc⟩
    obtain ⟨hdreach, hdimp⟩ := hdn
    obtain ⟨hoff, -⟩ := hdimp (child_inv hinv fun _ => VSet.mem_lt htv)
    have hac : AgreeTo (last + 1) t (child first level tc tv st).firsttc := by
      rw [(ref_fields hcf).1]; exact ha
    obtain ⟨heq, hdd, hfd, hinvd⟩ := hoff rfl last t hcd hac
    rw [heq]
    generalize descend false (level + 1) (numcells + 1) (child first level tc tv st) = rd
      at hdreach hinvd hdd hfd ⊢
    obtain ⟨exit, s8⟩ := rd
    dsimp only at hdreach hinvd hdd hfd ⊢
    simp only [Nat.add_sub_cancel] at hdreach
    rw [leave_tw]
    have hout : SearchOut G level level st { s8 with fixedpts := s8.fixedpts.erase tv } :=
      (R.leave tv s8).out (hceff s8 hdreach)
    have hld : Depth last ({ s8 with fixedpts := s8.fixedpts.erase tv } : Search n) := hdd
    have hli : Inv ({ s8 with fixedpts := s8.fixedpts.erase tv } : Search n) := hinvd
    have hla : AgreeTo (last + 1) t ({ s8 with fixedpts := s8.fixedpts.erase tv } : Search n).firsttc := by
      show AgreeTo (last + 1) t s8.firsttc
      rw [hfd, (ref_fields hcf).1]; exact ha
    have hlf : ({ s8 with fixedpts := s8.fixedpts.erase tv } : Search n).firsttc = st.firsttc := by
      show s8.firsttc = st.firsttc
      rw [hfd, (ref_fields hcf).1]
    unfold Generic.advance
    simp only [Id.run]
    cases exit with
    | fuel => exact ⟨rfl, hld, hlf, hli⟩
    | done =>
      obtain ⟨h1, h2, h3, h4, -⟩ := resume_off (ctx := ctx) (tcLevel := tcLevel) hn0 hB fuel cfuel next
        hnext first level numcells tc tv1 tv cell cell index st _ hlevel hok htarget hout
        (fun _ hv => hv) (fun h => Nat.le_of_lt (hpast h)) hli last t hld hla
      exact ⟨h1, h2, h3.trans hlf, h4⟩
    | unwind target short =>
      by_cases hlt : target < level
      · simp only [hlt, ite_true]; exact ⟨rfl, hld, hlf, hli⟩
      · simp only [hlt, ite_false]
        dsimp only [policy, Generic.Policy.shortprune]
        have e4 : shortprune cell (tw (phi (n + 2) B) t { s8 with fixedpts := s8.fixedpts.erase tv }) =
            shortprune cell ({ s8 with fixedpts := s8.fixedpts.erase tv } : Search n) := rfl
        rw [e4]
        cases short with
        | true =>
          simp only [ite_true]
          obtain ⟨h1, h2, h3, h4, -⟩ := resume_off (ctx := ctx) (tcLevel := tcLevel) hn0 hB fuel cfuel
            next hnext first level numcells tc tv1 tv cell _ index st _ hlevel hok htarget hout
            (fun v hv => R.short cell _ v hv) (fun h => Nat.le_of_lt (hpast h)) hli last t hld hla
          exact ⟨h1, h2, h3.trans hlf, h4⟩
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          obtain ⟨h1, h2, h3, h4, -⟩ := resume_off (ctx := ctx) (tcLevel := tcLevel) hn0 hB fuel cfuel
            next hnext first level numcells tc tv1 tv cell cell index st _ hlevel hok htarget hout
            (fun _ hv => hv) (fun h => Nat.le_of_lt (hpast h)) hli last t hld hla
          exact ⟨h1, h2, h3.trans hlf, h4⟩
  · have hc' : ¬ (!first || (tw (phi (n + 2) B) t st).orbits[tv]! == tv) = true := hc
    simp only [hc, hc', Bool.false_eq_true, ite_false]
    have hsw := hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell
      (if (first && st.orbits[tv]! == tv1) = true then index + 1 else index) st
      ⟨hlevel, hok, htarget, fun v hv => VSet.nextElem_mem hv⟩
    obtain ⟨-, himp⟩ := hsw
    obtain ⟨hoff, -⟩ := himp hinv
    obtain ⟨heq, hd', hf', hinv'⟩ := hoff (Generic.Past.next hpast) last t hd ha
    exact ⟨heq, hd', hf', hinv'⟩

theorem sweepStep_first (hn0 : 0 < n) (hB : n + 2 < B) (fuel cfuel : Nat)
    (descend : Generic.NodeFn (Search n)) (next : Generic.SweepFn (Search n) n)
    (hdescend : (infContract G ctx tcLevel B).nodeValid fuel descend)
    (hnext : (infContract G ctx tcLevel B).sweepValid fuel cfuel next)
    (level numcells tc tv1 : Nat) (cell : VSet n) (index : Nat) (st : Search n)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv1 = true)
    (hinv : Inv st) (t : Array Int) (horb : OrbId st) (ha : AgreeTo level t st.firsttc) :
    ∃ t', Generic.sweepStep B (fun first level numcells st => Generic.node first ctx B tcLevel fuel level numcells st)
        (fun first level numcells tc tv1 cursor cell index st =>
          Generic.sweep first ctx B tcLevel fuel cfuel level numcells tc tv1 cursor cell index st)
        true level numcells tc tv1 tv1 cell index (tw (phi (n + 2) B) t st) =
      ((Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell index st).1,
        (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell index st).2.1,
        tw (phi (n + 2) B) t' (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell
          index st).2.2) ∧
      ((Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell index st).1 = .fuel ∨
        ∃ last, Depth last (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell
            index st).2.2 ∧
          AgreeTo (last + 1) t' (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell
            index st).2.2.firsttc) ∧
      Inv (Generic.sweepStep (n + 2) descend next true level numcells tc tv1 tv1 cell index st).2.2 := by
  have hln := level_le_of_ok hok
  have R := reachPolicy G ctx tcLevel hn0
  have F := referencePolicy ctx (n + 2) tcLevel
  have horb1 : st.orbits[tv1]! = tv1 := horb tv1 (VSet.mem_lt htv)
  unfold Generic.sweepStep
  dsimp only [policy, Generic.Policy.orbit, Generic.Policy.child, Generic.Policy.afterChildFirst,
    Generic.Policy.leaveChild]
  simp only [Id.run]
  have hc : (!true || st.orbits[tv1]! == tv1) = true := by simp [horb1]
  have hc' : (!true || (tw (phi (n + 2) B) t st).orbits[tv1]! == tv1) = true := hc
  simp only [hc, hc', ite_true, Bool.true_and, beq_self_eq_true]
  rw [child_tw t true level tc tv1 st (by omega)]
  have hch := R.child true level numcells tc tv1 cell st hlevel hok htarget htv
  have hcf := F.child true level tc tv1 st
  dsimp only [policy, Generic.Policy.child] at hch hcf
  obtain ⟨hokc, hceff⟩ := hch
  have hdn := hdescend true (level + 1) (numcells + 1) (child true level tc tv1 st) ⟨by omega, hokc⟩
  obtain ⟨hdreach, hdimp⟩ := hdn
  obtain ⟨-, hfirst⟩ := hdimp (child_inv hinv fun _ => VSet.mem_lt htv)
  have hac : AgreeTo (level + 1 - 1) t (child true level tc tv1 st).firsttc := by
    rw [(ref_fields hcf).1, Nat.add_sub_cancel]; exact ha
  obtain ⟨t', heq, hph, hinvd⟩ := hfirst rfl t (child_orbId horb) hac
  rw [heq]
  generalize descend true (level + 1) (numcells + 1) (child true level tc tv1 st) = rd
    at hdreach hinvd hph ⊢
  obtain ⟨exit, s8⟩ := rd
  dsimp only at hdreach hinvd hph ⊢
  simp only [Nat.add_sub_cancel] at hdreach
  rw [afterChildFirst_tw, leave_tw]
  let s9 : Search n := { afterChildFirst level tv1 s8 with
    fixedpts := (afterChildFirst level tv1 s8).fixedpts.erase tv1 }
  have hout : SearchOut G level level st s9 :=
    (R.leave tv1 _).out ((R.afterChild level tv1 s8).out (hceff s8 hdreach))
  have hli : Inv s9 := hinvd
  refine ⟨t', ?_⟩
  unfold Generic.advance
  simp only [Id.run]
  cases exit with
  | fuel => exact ⟨rfl, .inl rfl, hli⟩
  | done =>
    obtain ⟨last, hd8, ha8⟩ := hph.resolve_left (by intro h; cases h)
    obtain ⟨h1, h2, h3, h4, -⟩ := resume_off (ctx := ctx) (tcLevel := tcLevel) hn0 hB fuel cfuel next
      hnext true level numcells tc tv1 tv1 cell cell index st s9 hlevel hok htarget hout
      (fun _ hv => hv) (fun _ => Nat.le_refl _) hli last t' hd8 ha8
    have ha9 : AgreeTo (last + 1) t' s9.firsttc := ha8
    exact ⟨h1, .inr ⟨last, h2, by rw [← h3] at ha9; exact ha9⟩, h4⟩
  | unwind target short =>
    obtain ⟨last, hd8, ha8⟩ := hph.resolve_left (by intro h; cases h)
    have hd9 : Depth last s9 := hd8
    have ha9 : AgreeTo (last + 1) t' s9.firsttc := ha8
    by_cases hlt : target < level
    · simp only [hlt, ite_true]; exact ⟨rfl, .inr ⟨last, hd9, ha9⟩, hli⟩
    · simp only [hlt, ite_false]
      dsimp only [policy, Generic.Policy.shortprune]
      have e4 : shortprune cell (tw (phi (n + 2) B) t' s9) = shortprune cell s9 := rfl
      rw [e4]
      cases short with
      | true =>
        simp only [ite_true]
        obtain ⟨h1, h2, h3, h4, -⟩ := resume_off (ctx := ctx) (tcLevel := tcLevel) hn0 hB fuel cfuel
          next hnext true level numcells tc tv1 tv1 cell _ index st s9 hlevel hok htarget hout
          (fun v hv => R.short cell _ v hv) (fun _ => Nat.le_refl _) hli last t' hd9 ha9
        exact ⟨h1, .inr ⟨last, h2, by rw [← h3] at ha9; exact ha9⟩, h4⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        obtain ⟨h1, h2, h3, h4, -⟩ := resume_off (ctx := ctx) (tcLevel := tcLevel) hn0 hB fuel cfuel
          next hnext true level numcells tc tv1 tv1 cell cell index st s9 hlevel hok htarget hout
          (fun _ hv => hv) (fun _ => Nat.le_refl _) hli last t' hd9 ha9
        exact ⟨h1, .inr ⟨last, h2, by rw [← h3] at ha9; exact ha9⟩, h4⟩

/-- The two runs' relation is a sound contract for HexGraphIso's search. -/
theorem infPolicy (hn0 : 0 < n) (hB : n + 2 < B) :
    Generic.SoundPolicy ctx (n + 2) tcLevel (infContract G ctx tcLevel B) where
  node_zero := infContract_node_zero
  node_step := by
    intro fuel next hnext first level numcells st hin
    have hnextR : (Generic.reachContract G (fun st => st)).sweepValid fuel (n + 1) next :=
      fun first level numcells tc tv1 cursor cell index st hpre =>
        (hnext first level numcells tc tv1 cursor cell index st hpre).1
    refine ⟨(reachPolicy G ctx tcLevel hn0).node_step hnextR first level numcells st hin.1 hin.2,
      fun hinv => ⟨?_, ?_⟩⟩
    · intro hf last t hd ha
      subst hf
      rw [Generic.node]
      exact nodeStep_off hn0 hB fuel next hnext level numcells st hin.1 hin.2 hinv last t hd ha
    · intro hf t horb ha
      subst hf
      rw [Generic.node]
      exact nodeStep_first hn0 hB fuel next hnext level numcells st hin.1 hin.2 hinv t horb ha
  sweep_none := infContract_sweep_none
  sweep_zero := infContract_sweep_zero
  sweep_step := by
    intro fuel cfuel descend next hdescend hnext first level numcells tc tv1 tv cell index st hin
    obtain ⟨hlevel, hok, htarget, hcur⟩ := hin
    have htv := hcur tv rfl
    have hdR : (Generic.reachContract G (fun st => st)).nodeValid fuel descend :=
      fun first level numcells st hpre => (hdescend first level numcells st hpre).1
    have hnR : (Generic.reachContract G (fun st => st)).sweepValid fuel cfuel next :=
      fun first level numcells tc tv1 cursor cell index st hpre =>
        (hnext first level numcells tc tv1 cursor cell index st hpre).1
    refine ⟨(reachPolicy G ctx tcLevel hn0).sweep_step hdR hnR first level numcells tc tv1 tv index
      cell st hlevel hok htarget htv, fun hinv => ⟨?_, ?_⟩⟩
    · intro hpast last t hd ha
      rw [Generic.sweep]
      exact sweepStep_off hn0 hB fuel cfuel descend next hdescend hnext first level numcells tc tv1 tv
        cell index st hlevel hok htarget htv (fun hf => hpast hf tv rfl) hinv last t hd ha
    · intro hf hc t horb ha
      subst hf
      cases hc
      rw [Generic.sweep]
      exact sweepStep_first hn0 hB fuel cfuel descend next hdescend hnext level numcells tc tv1 cell
        index st hlevel hok htarget htv hinv t horb ha

end

/-- nauty's infinity for `int` partitions. -/
abbrev nautyInfinity : Nat := 2000000002

/-- The search state nauty starts from: HexGraphIso's `initial`, with
`NAUTY_INFINITY` in `ptn` and the zero-filled `firsttc` of the allocator. -/
def initialC (n : Nat) (lab0 : Array Nat) (cellEnds : List Nat) : Search n :=
  { initial n lab0 cellEnds with
    ptn := initPtn n nautyInfinity cellEnds
    firsttc := .replicate (n + 2) 0 }

theorem initPtn_map {a b : Nat} (ha : a ≠ 0) (n : Nat) (cellEnds : List Nat) :
    (initPtn n a cellEnds).map (phi a b) = initPtn n b cellEnds := by
  unfold initPtn
  have h0 : phi a b 0 = 0 := phi_ne (Ne.symm ha)
  suffices ∀ (l : List Nat) (p : Array Nat),
      (l.foldl (fun ptn e => ptn.set! e 0) p).map (phi a b) =
        l.foldl (fun ptn e => ptn.set! e 0) (p.map (phi a b)) by
    rw [this]
    congr 1
    simp [phi]
  intro l
  induction l with
  | nil => intro p; rfl
  | cons e l ih =>
    intro p
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    simp only [Array.set!, Array.map_setIfInBounds, h0]

theorem initialC_eq (n : Nat) (lab0 : Array Nat) (cellEnds : List Nat) :
    initialC n lab0 cellEnds =
      tw (phi (n + 2) nautyInfinity) (.replicate (n + 2) 0) (initial n lab0 cellEnds) := by
  unfold initialC tw
  rw [show (initial n lab0 cellEnds).ptn = initPtn n (n + 2) cellEnds from rfl,
    initPtn_map (by omega)]

theorem finish_tw (ctx : Ctx n) (f : Nat → Nat) (t : Array Int) (st : Search n) :
    finish ctx (tw f t st) = finish ctx st := rfl

/-- nauty's root call, with `NAUTY_INFINITY` and the zero-filled `firsttc`,
ends with HexGraphIso's exit and HexGraphIso's result. -/
theorem node_inf (G : Colored n k) (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) :
    (node true { g := rowsOf G } nautyInfinity 100 (n + 2) 1 (initialPartition G).2.length
        (initialC n (initialPartition G).1 (initialPartition G).2)).1 =
      (node true { g := rowsOf G } (n + 2) 100 (n + 2) 1 (initialPartition G).2.length
        (initial n (initialPartition G).1 (initialPartition G).2)).1 ∧
    finish { g := rowsOf G }
        (node true { g := rowsOf G } nautyInfinity 100 (n + 2) 1 (initialPartition G).2.length
          (initialC n (initialPartition G).1 (initialPartition G).2)).2 =
      finish { g := rowsOf G }
        (node true { g := rowsOf G } (n + 2) 100 (n + 2) 1 (initialPartition G).2.length
          (initial n (initialPartition G).1 (initialPartition G).2)).2 := by
  have hpost := Generic.node_sound (infPolicy (G := G) (ctx := { g := rowsOf G }) (tcLevel := 100)
    (B := nautyInfinity) hn0 hn) true (n + 2) 1 (initialPartition G).2.length
    (initial n (initialPartition G).1 (initialPartition G).2) ⟨Nat.le_refl _, initial_ok G hn0⟩
  obtain ⟨-, himp⟩ := hpost
  have hinv : Inv (initial n (initialPartition G).1 (initialPartition G).2) :=
    initial_inv hn0 _ _
  have horb : OrbId (initial n (initialPartition G).1 (initialPartition G).2) := by
    intro v hv
    show (Array.ofFn (n := n) fun i => i.val)[v]! = v
    rw [getElem!_pos _ v (by simpa using hv)]
    simp
  have hag : AgreeTo (1 - 1) (.replicate (n + 2) 0)
      (initial n (initialPartition G).1 (initialPartition G).2).firsttc :=
    ⟨by simp [initial], fun i h1 h2 => absurd h2 (by omega)⟩
  obtain ⟨-, hfirst⟩ := himp hinv
  obtain ⟨t', heq, -, -⟩ := hfirst rfl _ horb hag
  rw [initialC_eq, node_eq_generic, node_eq_generic, heq]
  exact ⟨rfl, finish_tw _ _ _ _⟩

/-- nauty's root call ends in HexGraphIso's final orbits. -/
theorem orbits_inf (G : Colored n k) (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) :
    (node true { g := rowsOf G } nautyInfinity 100 (n + 2) 1 (initialPartition G).2.length
        (initialC n (initialPartition G).1 (initialPartition G).2)).2.orbits =
      (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2.orbits := by
  have hpost := Generic.node_sound (infPolicy (G := G) (ctx := { g := rowsOf G }) (tcLevel := 100)
    (B := nautyInfinity) hn0 hn) true (n + 2) 1 (initialPartition G).2.length
    (initial n (initialPartition G).1 (initialPartition G).2) ⟨Nat.le_refl _, initial_ok G hn0⟩
  obtain ⟨-, himp⟩ := hpost
  have horb : OrbId (initial n (initialPartition G).1 (initialPartition G).2) := by
    intro v hv
    show (Array.ofFn (n := n) fun i => i.val)[v]! = v
    rw [getElem!_pos _ v (by simpa using hv)]
    simp
  have hag : AgreeTo (1 - 1) (.replicate (n + 2) 0)
      (initial n (initialPartition G).1 (initialPartition G).2).firsttc :=
    ⟨by simp [initial], fun i h1 h2 => absurd h2 (by omega)⟩
  obtain ⟨-, hfirst⟩ := himp (initial_inv hn0 _ _)
  obtain ⟨t', heq, -, -⟩ := hfirst rfl _ horb hag
  unfold runState
  rw [ite_eq_right (by simp; omega), initialC_eq, node_eq_generic, node_eq_generic, heq]
  rfl

/-- The corollary for HexGraphIso's traced run on a nonempty graph. -/
theorem runTraced_inf (G : Colored n k) (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) :
    finish { g := rowsOf G }
        (node true { g := rowsOf G } nautyInfinity 100 (n + 2) 1 (initialPartition G).2.length
          (initialC n (initialPartition G).1 (initialPartition G).2)).2 =
      runTraced n (rowsOf G) (initialPartition G).1 (initialPartition G).2 := by
  rw [(node_inf G hn0 hn).2]
  unfold runTraced runState
  rw [ite_eq_right (by simp; omega)]

end NautyVerified.Spec.SearchInf

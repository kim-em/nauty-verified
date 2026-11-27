import NautyVerified.Proofs.Refine.Frame
import NautyVerified.Proofs.Refine.Mash
import NautyVerified.Proofs.Refine.Scan
import NautyVerified.Proofs.Set.Bit
import NautyVerified.Proofs.Set.Add
import NautyVerified.Spec.Fmptn
import NautyVerified.Proofs.Refine.Step

/-!
# `refine`'s pass for a trivial splitting cell

`trivial`, for a singleton splitter `{lab[split1]}`, splits every cell by
adjacency to `lab[split1]`. `wp_swap`: the two-pointer loop `swapLoop` is
HexGraphIso's `splitCellLoop`. `wp_trivSplit`: the bookkeeping after it is
`trivialSplit`. `wp_trivial`: the whole pass is `refineTrivial`, through its
`@[csimp]` form `refineTrivialFast`, whose cell boundaries come from the
partition at the start of the pass. The C reads `ptn` live, but it writes
`ptn` only at positions inside a cell it has already scanned, so the reads
agree with the snapshot.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (longs BitTable)
open NautyVerified.Proofs.Graph (GraphAt)
open Hex.GraphIso.Nauty (VSet Ctx RefineSt splitCellLoop trivialSplit trivialCell cellEnd)

variable {xi : ExternalCalls}

/-! ## The two-pointer loop -/

theorem splitCellLoop_stop {n : Nat} (gRow : VSet n) (F : Nat) (lab : Array Nat) {c1 c2 : Int}
    (h : c2 < c1) : splitCellLoop gRow F lab c1 c2 = (lab, c1, c2) := by
  cases F <;> simp [splitCellLoop, show ¬ c1 ≤ c2 by omega]

theorem splitCellLoop_step {n : Nat} (gRow : VSet n) (F : Nat) (lab : Array Nat) {c1 c2 : Int}
    (h : c1 ≤ c2) :
    splitCellLoop gRow (F + 1) lab c1 c2 =
      if gRow.mem lab[c1.toNat]! then splitCellLoop gRow F lab (c1 + 1) c2
      else splitCellLoop gRow F ((lab.set! c1.toNat lab[c2.toNat]!).set! c2.toNat lab[c1.toNat]!)
        c1 (c2 - 1) := by
  rw [splitCellLoop, ite_eq_left h]

/-- `ISELEMENT(gptr, a)` for `gptr` at row `v` of the graph. -/
theorem eval_inRow {e : env} {le : temp_env} {m : mem} {n : Nat} {bg : block} {gofs : ptrofs}
    {gw : Nat → Lib.Integers.int64} {rows : Array (VSet n)} {M v c : Nat}
    (hg : GraphAt m bg gofs gw rows M) (hv : v < n) (hM : M < 33554432) (hnM : n ≤ 64 * M)
    (hp : PTree.get dense.id.gptr le = some
      (.Vptr bg (ptrTo (intOfZ (Ptrofs.unsigned gofs)) 8 (M * v))))
    {a : expr} (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n) (hbit : BitTable m Block.naugraphBit)
    (he : PTree.get dense.id.«naugraph:bit» e = none) :
    Exec.evalExpr ge e le m (Set.isElement dense.id.gptr dense.id.«naugraph:bit» a) =
      some (Val.of_bool (rows[v]!.mem c)) := by
  rw [Set.eval_isElement (hg.row hv) (by omega) hp ha hty (by omega) (by omega) hbit he
    find_naugraphBit, (hg.rep v hv).2 c (by omega)]


/-- What `swapLoop` leaves, for the loop started from `lab` on `[cell1, cell2]`. -/
structure SwapOut {n : Nat} (lab lab' : Array Nat) (cell1 cell2 : Nat) (c1 : Nat) (c2 : Int) :
    Prop where
  size : lab'.size = n
  small : ∀ j < n, lab'[j]! < n
  outside : ∀ j, j < cell1 ∨ cell2 < j → lab'[j]! = lab[j]!
  lo : cell1 ≤ c1
  le : (c1 : Int) ≤ c2 + 1
  hi : c2 ≤ cell2

theorem wp_swap {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {n : Nat}
    {bg : block} {gofs : ptrofs} {gw : Nat → Lib.Integers.int64} {rows : Array (VSet n)}
    {M v : Nat} {bl : block} {lofs : ptrofs} {lab : Array Nat} {cell1 cell2 : Nat}
    (hg : GraphAt m bg gofs gw rows M) (hv : v < n) (hM : M < 33554432) (hnM : n ≤ 64 * M)
    (hbit : BitTable m Block.naugraphBit) (hgl : bg ≠ bl) (hbitl : Block.naugraphBit ≠ bl)
    (he : PTree.get dense.id.«naugraph:bit» e = none)
    (harr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n)
    (hsz : lab.size = n) (hsmall : ∀ j < n, lab[j]! < n) (hc12 : cell1 ≤ cell2) (hc2n : cell2 < n)
    (hp : PTree.get dense.id.gptr le = some
      (.Vptr bg (ptrTo (intOfZ (Ptrofs.unsigned gofs)) 8 (M * v))))
    (hlab : PTree.get dense.id.lab le = some (.Vptr bl lofs))
    (hc1 : PTree.get dense.id.c1 le = some (.Vint (ir cell1)))
    (hc2 : PTree.get dense.id.c2 le = some (.Vint (ir cell2)))
    (hQ : ∀ le' m' (lab' : Array Nat) (c1 : Nat) (c2 : Int),
      splitCellLoop rows[v]! (cell2 - cell1 + 2) lab cell1 cell2 = (lab', (c1 : Int), c2) →
      ArrayAt m' .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab') n → Unch m m' (· = bl) →
      SwapOut (n := n) lab lab' cell1 cell2 c1 c2 → (c1 : Int) = c2 + 1 →
      PTree.get dense.id.c1 le' = some (.Vint (ir c1)) →
      PTree.get dense.id.c2 le' = some (.Vint (ir c2)) →
      (∀ x, x ≠ dense.id.c1 → x ≠ dense.id.c2 → x ≠ dense.id.labc1 →
        PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f swapLoop Q e le m := by
  let R := splitCellLoop rows[v]! (cell2 - cell1 + 2) lab cell1 cell2
  have hn : n < 2147483648 := by omega
  let I := fun (k : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e' = e ∧
    ∃ (lab' : Array Nat) (c1 : Nat) (c2 : Int) (F : Nat),
      ArrayAt m' .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab') n ∧ Unch m m' (· = bl) ∧
      SwapOut (n := n) lab lab' cell1 cell2 c1 c2 ∧ k = (c2 - c1 + 1).toNat ∧ k < F ∧
      R = splitCellLoop rows[v]! F lab' c1 c2 ∧
      PTree.get dense.id.c1 le' = some (.Vint (ir c1)) ∧
      PTree.get dense.id.c2 le' = some (.Vint (ir c2)) ∧
      ∀ x, x ≠ dense.id.c1 → x ≠ dense.id.c2 → x ≠ dense.id.labc1 → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := fun k t e' le' m' => ∃ k', k' < k ∧ I k' t e' le' m') ?_ ?_
    (n := cell2 + 1 - cell1)
    ⟨rfl, rfl, lab, cell1, cell2, cell2 - cell1 + 2, harr, Unch.refl _ _,
      ⟨hsz, hsmall, fun _ _ => rfl, Nat.le_refl _, by omega, by omega⟩, by omega, by omega, rfl,
      hc1, hc2, fun _ _ _ _ => rfl⟩
  · rintro k t e' le' m' ⟨rfl, rfl, lab', c1, c2, F, harr', hu, hs, rfl, hF, hR, hc1', hc2', ho⟩
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hc1', hc2', typeof, cop]
    have := hs.le; have := hs.hi; have := hs.lo
    rw [ir_lt (a := c2) (b := (c1 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hlt : c2 < c1
    · rw [ite_eq_right (by simpa using hlt)]
      apply wp_break
      have hRe : R = (lab', (c1 : Int), c2) := by rw [hR]; exact splitCellLoop_stop _ _ _ hlt
      exact hQ le' m' lab' c1 c2 hRe harr' hu hs (by omega) hc1' hc2' ho
    · rw [ite_eq_left (by simpa using hlt)]
      apply wp_skip
      have hc2nat : c2 = (c2.toNat : Int) := by omega
      have hc1n : c1 < n := by omega
      have hc2n' : c2.toNat < n := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hstep := splitCellLoop_step rows[v]! F' lab' (c1 := c1) (c2 := c2) (by omega)
      rw [show (c1 : Int).toNat = c1 from rfl] at hstep
      have hlab' : PTree.get dense.id.lab le' = some (.Vptr bl lofs) := by
        rw [ho _ (by decide) (by decide) (by decide)]; exact hlab
      have hc1e : Exec.evalExpr ge e' le' m' (tv dense.id.c1) = some (.Vint (ir c1)) := hc1'
      have hl1 := eval_at (ge := ge) (e := e') harr' hn dense.id.lab hlab' (tv dense.id.c1) c1 hc1n
        hc1e rfl
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [hl1]
      simp only [ints]
      let le2 := PTree.set dense.id.labc1 (.Vint (ir (lab'[c1]! : Int))) le'
      have ho2 : ∀ x, x ≠ dense.id.labc1 → PTree.get x le2 = PTree.get x le' :=
        fun x hx => temps_gso _ _ hx
      have hl1v : PTree.get dense.id.labc1 le2 = some (.Vint (ir (lab'[c1]! : Int))) := temps_gss _ _ _
      have hgm : GraphAt m' bg gofs gw rows M := ⟨hg.arr.unch hu hgl, hg.rep⟩
      have hbm : BitTable m' Block.naugraphBit := hbit.unch hu hbitl
      have hp2 : PTree.get dense.id.gptr le2 = some
          (.Vptr bg (ptrTo (intOfZ (Ptrofs.unsigned gofs)) 8 (M * v))) := by
        rw [ho2 _ (by decide), ho _ (by decide) (by decide) (by decide)]; exact hp
      wp_step; wp_step
      apply wp_if_eval
      rw [eval_inRow hgm hv hM hnM hp2 (a := tv dense.id.labc1) hl1v rfl (hs.small c1 hc1n) hbm he]
      simp only [typeof, cop]
      by_cases hmem : rows[v]!.mem lab'[c1]! = true
      · rw [ite_eq_left (by simp [hmem])]
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr]
        rw [temps_gso _ _ (by decide), hc1']
        simp only [typeof, cop, ir_add]
        refine ⟨(c2 - (c1 + 1 : Nat) + 1).toNat, by omega, rfl, rfl, lab', c1 + 1, c2, F', harr', hu,
          ⟨hs.size, hs.small, hs.outside, by omega, by omega, hs.hi⟩, rfl, by omega, ?_, ?_, ?_, ?_⟩
        · rw [hR, hstep, ite_eq_left hmem]; push_cast; rfl
        · rw [temps_gss]; push_cast; rfl
        · rw [temps_gso _ _ (by decide), ho2 _ (by decide)]; exact hc2'
        · intro x h1 h2 h3
          rw [temps_gso _ _ h1, ho2 _ h3, ho x h1 h2 h3]
      · rw [ite_eq_right (by simpa using hmem)]
        have hc2e : Exec.evalExpr ge e' le2 m' (tv dense.id.c2) = some (.Vint (ir (c2.toNat : Nat))) := by
          show PTree.get _ _ = _
          rw [ho2 _ (by decide), hc2', ← hc2nat]
        have hc1e2 : Exec.evalExpr ge e' le2 m' (tv dense.id.c1) = some (.Vint (ir c1)) := by
          show PTree.get _ _ = _
          rw [ho2 _ (by decide), hc1']
        have hlab2 : PTree.get dense.id.lab le2 = some (.Vptr bl lofs) := by
          rw [ho2 _ (by decide)]; exact hlab'
        have hl2 := eval_at (ge := ge) (e := e') harr' hn dense.id.lab hlab2 (tv dense.id.c2) c2.toNat
          hc2n' hc2e rfl
        have hsz' := hs.size
        wp_step; wp_step; wp_step
        refine wp_store harr' hn dense.id.lab hlab2 (tv dense.id.c1) c1 hc1n hc1e2 rfl
          (ix dense.id.lab (tv dense.id.c2)) (lab'[c2.toNat]! : Nat) hl2 rfl ?_
        intro m2 harr2 hu2
        rw [← ints_set (by omega)] at harr2
        let lab1 := lab'.set! c1 lab'[c2.toNat]!
        have hsz1 : lab1.size = n := by simp [lab1, hsz']
        wp_step; wp_step; wp_step
        refine wp_store harr2 hn dense.id.lab hlab2 (tv dense.id.c2) c2.toNat hc2n' hc2e rfl
          (tv dense.id.labc1) (lab'[c1]! : Nat) hl1v rfl ?_
        intro m3 harr3 hu3
        rw [← ints_set (by simp [hsz']; omega)] at harr3
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr]
        rw [temps_gso _ _ (by decide), hc2']
        simp only [typeof, cop, ir_sub]
        have hsm := hs.small
        have hsmall2 : ∀ j < n, (lab1.set! c2.toNat lab'[c1]!)[j]! < n := by
          intro j hj
          simp only [lab1]
          by_cases h2 : j = c2.toNat
          · subst h2; rw [Array.getElem!_set!_self _ _ _ (by simp; omega)]
            exact hsm c1 hc1n
          · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm h2)]
            by_cases h1 : j = c1
            · subst h1; rw [Array.getElem!_set!_self _ _ _ (by omega)]; exact hsm _ hc2n'
            · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm h1)]; exact hsm j hj
        refine ⟨(c2 - 1 - c1 + 1).toNat, by omega, rfl, rfl, lab1.set! c2.toNat lab'[c1]!, c1, c2 - 1,
          F', harr3, (hu.trans (hu2.mono fun _ h => h)).trans hu3,
          ⟨by simp [hsz1], hsmall2, fun j hj => ?_, hs.lo, by omega, by omega⟩,
          rfl, by omega, ?_, ?_, ?_, ?_⟩
        · simp only [lab1]
          rw [Array.getElem!_set!_ne _ _ _ _ (by omega), Array.getElem!_set!_ne _ _ _ _ (by omega)]
          exact hs.outside j hj
        · rw [hR, hstep, ite_eq_right (by simpa using hmem)]
        · rw [temps_gso _ _ (by decide), ho2 _ (by decide)]; exact hc1'
        · rw [temps_gss]
        · intro x h1 h2 h3
          rw [temps_gso _ _ h2, ho2 _ h3, ho x h1 h2 h3]
  · rintro k t e' le' m' ⟨k', hk', hI⟩
    apply wp_skip
    exact ⟨k', hk', by rw [show t ++ E0 = t from List.append_nil t]; exact hI⟩


/-! ## The one-`int` cell `*numcells` -/

theorem ofs_cell (ofs : ptrofs) :
    Ptrofs.unsigned ofs = elemOfs .Mint32 (intOfZ (Ptrofs.unsigned ofs)) 0 := by
  unfold elemOfs
  rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ]

theorem eval_cell {e : env} {le : temp_env} {m : mem} {p : Common.AST.ident} {b : block}
    {ofs : ptrofs} {x : Int}
    (h : ArrayAt m .Mint32 b (intOfZ (Ptrofs.unsigned ofs)) (fun _ => .Vint (ir x)) 1)
    (hp : PTree.get p le = some (.Vptr b ofs)) :
    Exec.evalExpr ge e le m (.Ederef (pi p) tint) = some (.Vint (ir x)) := by
  simp only [Exec.evalExpr, hp, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  exact load_array h (i := 0) (by decide) (ofs_cell ofs)

/-- `*p = rhs` for `p` pointing at a one-`int` cell. -/
theorem wp_cellStore {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {p : Common.AST.ident} {b : block} {ofs : ptrofs} {vals : Nat → val} {rhs : expr} {x : Int}
    (h : ArrayAt m .Mint32 b (intOfZ (Ptrofs.unsigned ofs)) vals 1)
    (hp : PTree.get p le = some (.Vptr b ofs))
    (hr : Exec.evalExpr ge e le m rhs = some (.Vint (ir x))) (hty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 b (intOfZ (Ptrofs.unsigned ofs)) (fun _ => .Vint (ir x)) 1 →
      Unch m m' (· = b) → Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (pi p) tint) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array h (show 0 < 1 by decide) (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [hr, hty]
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, typeof, cop, Exec.assignLoc,
    Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [ofs_cell ofs, hst]
  exact hQ m' (harr'.congr fun i hi => by simp [upd, show i = 0 by omega]) (Unch.store hst rfl)

/-- `Tmp` for a new state, from the temporaries holding its scalars. -/
theorem Tmp.update {n : Nat} {le le' : temp_env} {L : Loc} {st st' : RefineSt n}
    (h : Tmp le L st) (hle : ∀ x ∈ args, PTree.get x le' = PTree.get x le)
    (hl : PTree.get dense.id.longcode le' = some (.Vlong (lr st'.longcode)))
    (hh : PTree.get dense.id.hint le' = some (.Vint (ir st'.hint)))
    (hm : PTree.get dense.id.maxpos le' = some (.Vint (ir st'.maxpos))) : Tmp le' L st' where
  g := by rw [hle _ (by simp [args])]; exact h.g
  lab := by rw [hle _ (by simp [args])]; exact h.lab
  ptn := by rw [hle _ (by simp [args])]; exact h.ptn
  level := by rw [hle _ (by simp [args])]; exact h.level
  numcells := by rw [hle _ (by simp [args])]; exact h.numcells
  count := by rw [hle _ (by simp [args])]; exact h.count
  active := by rw [hle _ (by simp [args])]; exact h.active
  code := by rw [hle _ (by simp [args])]; exact h.code
  m := by rw [hle _ (by simp [args])]; exact h.m
  n := by rw [hle _ (by simp [args])]; exact h.n
  longcode := hl
  hint := hh
  maxpos := hm


/-! ## The bookkeeping after the two-pointer loop -/

/-- The fields `trivialSplit` changes before its active-set choice. -/
abbrev splitMid {n : Nat} (level k : Nat) (st : RefineSt n) : RefineSt n :=
  { st with
    ptn := st.ptn.set! k level
    longcode := Hex.GraphIso.Nauty.mash st.longcode k
    numcells := st.numcells + 1 }

theorem trivialSplit_eq {n : Nat} (level cell1 cell2 c1 : Nat) (c2 : Int) (st : RefineSt n)
    (hA : (cell1 : Int) ≤ c2) (hB : c1 ≤ cell2) :
    trivialSplit level cell1 cell2 (c1 : Int) c2 st =
      if st.active.mem cell1 = true ∨ cell2 - c1 ≤ c2.toNat - cell1 then
        { splitMid level c2.toNat st with
          active := st.active.insert c1
          hint := if c1 = cell2 then c1 else st.hint }
      else
        { splitMid level c2.toNat st with
          active := st.active.insert cell1
          hint := if c2.toNat = cell1 then cell1 else st.hint } := by
  unfold trivialSplit
  simp only [Int.ofNat_eq_natCast]
  rw [ite_eq_left ⟨hA, by omega⟩]
  by_cases h1 : st.active.mem cell1 = true ∨ cell2 - c1 ≤ c2.toNat - cell1
  · rw [ite_eq_left (by simpa using h1), ite_eq_left h1]
    by_cases h2 : c1 = cell2
    · rw [ite_eq_left (by simpa using h2), ite_eq_left h2]; rfl
    · rw [ite_eq_right (by simpa using h2), ite_eq_right h2]; rfl
  · rw [ite_eq_right (by simpa using h1), ite_eq_right h1]
    by_cases h2 : c2.toNat = cell1
    · rw [ite_eq_left (by simpa using h2), ite_eq_left h2]
    · rw [ite_eq_right (by simpa using h2), ite_eq_right h2]

theorem trivialSplit_stop {n : Nat} (level cell1 cell2 c1 : Nat) (c2 : Int) (st : RefineSt n)
    (h : ¬ ((cell1 : Int) ≤ c2 ∧ c1 ≤ cell2)) :
    trivialSplit level cell1 cell2 (c1 : Int) c2 st = st := by
  unfold trivialSplit
  simp only [Int.ofNat_eq_natCast]
  rw [ite_eq_right (by intro h'; exact h ⟨h'.1, by omega⟩)]


theorem wp_trivSplit {f : function} {Q : Post} {le : temp_env} {m : mem} {n : Nat} {L : Loc}
    {ctx : Ctx n} {st : RefineSt n} {aw : Nat → Lib.Integers.int64} {cell1 cell2 c1 : Nat}
    {c2 : Int} (hok : Ok n L) (hm : Mem m L ctx st aw) (ht : Tmp le L st)
    (hcode : st.longcode < 2 ^ 62) (hpsz : st.ptn.size = n)
    (hc1c : cell1 ≤ c1) (hcc : (c1 : Int) = c2 + 1) (hc2c : c2 ≤ cell2) (hcn : cell2 < n)
    (hcell1 : PTree.get dense.id.cell1 le = some (.Vint (ir cell1)))
    (hcell2 : PTree.get dense.id.cell2 le = some (.Vint (ir cell2)))
    (hc1 : PTree.get dense.id.c1 le = some (.Vint (ir c1)))
    (hc2 : PTree.get dense.id.c2 le = some (.Vint (ir c2)))
    (hQ : ∀ le' m' aw', Mem m' L ctx (trivialSplit L.level cell1 cell2 c1 c2 st) aw' →
      Tmp le' L (trivialSplit L.level cell1 cell2 c1 c2 st) →
      Unch m m' (fun z => z = L.bp ∨ z = L.bn ∨ z = L.ba) →
      (∀ x, x ≠ idOf 715 → x ≠ idOf 716 → x ≠ dense.id.longcode → x ≠ dense.id.hint →
        PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi ge f trivSplit Q empty_env le m := by
  have hn := hok.nlt
  have hc2n : c2 < n := by omega
  -- the cases where nothing is split
  have stop : ∀ v, ¬ ((cell1 : Int) ≤ c2 ∧ c1 ≤ cell2) →
      Q.normal E0 empty_env (PTree.set (idOf 716) v le) m := fun v h => by
    rw [trivialSplit_stop L.level cell1 cell2 c1 c2 st h] at hQ
    exact hQ _ m aw hm (ht.set (x := idOf 716) v (by decide)) (Unch.refl _ _)
      fun x _ h2 _ _ => temps_gso _ _ h2
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hc2, hcell1, typeof, cop]
  rw [ir_lt (a := c2) (b := (cell1 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hA : (cell1 : Int) ≤ c2
  · rw [ite_eq_left (by simp; omega)]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hc1, hcell2, typeof, cop]
    rw [ir_lt (a := (cell2 : Int)) (b := (c1 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hB : c1 ≤ cell2
    · rw [show (!decide ((cell2 : Int) < c1)) = true by simp; omega]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      rw [ite_eq_left (by decide)]
      generalize hv716 : PTree.set (idOf 716) _ le = le2
      have ho2 : ∀ x, x ≠ idOf 716 → PTree.get x le2 = PTree.get x le := fun x hx => by
        rw [← hv716]; exact temps_gso _ _ hx
      have ht2 : Tmp le2 L st := by rw [← hv716]; exact ht.set _ (by decide)
      obtain ⟨k, hk⟩ : ∃ k : Nat, c2 = k := ⟨c2.toNat, by omega⟩
      subst hk
      have hkn : k < n := by omega
      have hc2e : ∀ mm, Exec.evalExpr ge empty_env le2 mm (tv dense.id.c2) = some (.Vint (ir k)) :=
        fun _ => by show PTree.get _ _ = _; rw [ho2 _ (by decide)]; exact hc2
      -- ptn[c2] = level
      wp_step; wp_step; wp_step
      refine wp_store hm.ptn (by omega) dense.id.ptn ht2.ptn (tv dense.id.c2) k hkn (hc2e _) rfl
        (tv dense.id.level) L.level ht2.level rfl ?_
      intro m1 hp1 hu1
      rw [← ints_set (by omega)] at hp1
      -- longcode = MASH(longcode, c2)
      wp_step; wp_step; wp_step
      refine wp_mash ht2.longcode hcode (hc2e _) rfl (by omega) ?_
      generalize hv3 : PTree.set dense.id.longcode _ le2 = le3
      have ho3 : ∀ x, x ≠ dense.id.longcode → PTree.get x le3 = PTree.get x le2 := fun x hx => by
        rw [← hv3]; exact temps_gso _ _ hx
      have hl3 : PTree.get dense.id.longcode le3 =
          some (.Vlong (lr (Hex.GraphIso.Nauty.mash st.longcode k : Nat))) := by
        rw [← hv3]; exact temps_gss _ _ _
      have hnum3 : PTree.get dense.id.numcells le3 = some (.Vptr L.bn L.nofs) := by
        rw [ho3 _ (by decide)]; exact ht2.numcells
      -- *numcells = *numcells + 1
      have hpn := hok.ne 2 3 (by omega)
      have hpa := hok.ne 2 5 (by omega)
      have hna := hok.ne 3 5 (by omega)
      have hnc1 := hm.nc.unch hu1 (Ne.symm hpn)
      have hne : Exec.evalExpr ge empty_env le3 m1
          (.Ebinop .Oadd (.Ederef (pi dense.id.numcells) tint) (ci 1 tint) tint) =
          some (.Vint (ir ((st.numcells + 1 : Nat) : Int))) := by
        rw [Exec.evalExpr, eval_cell hnc1 hnum3]
        simp only [Exec.evalExpr, typeof, cop, ir_add]
        push_cast; rfl
      wp_step; wp_step; wp_step
      refine wp_cellStore hnc1 hnum3 hne rfl ?_
      intro m2 hnc2 hu2
      have hu12 : Unch m m2 (fun z => z = L.bp ∨ z = L.bn ∨ z = L.ba) :=
        (hu1.mono fun _ h => .inl h).trans (hu2.mono fun _ h => .inr (.inl h))
      have hact2 := (hm.act.unch hu1 (Ne.symm hpa)).unch hu2 (Ne.symm hna)
      have hbit2 : BitTable m2 Block.naugraphBit :=
        hm.bit.unch hu12 (by
          rintro (h | h | h)
          · exact (hok.ne 2 16 (by omega)) h.symm
          · exact (hok.ne 3 16 (by omega)) h.symm
          · exact (hok.ne 5 16 (by omega)) h.symm)
      have hact3 : PTree.get dense.id.active le3 = some (.Vptr L.ba L.aofs) := by
        rw [ho3 _ (by decide)]; exact ht2.active
      have hcl3 : PTree.get dense.id.cell1 le3 = some (.Vint (ir cell1)) := by
        rw [ho3 _ (by decide), ho2 _ (by decide)]; exact hcell1
      have hmem := Set.eval_isElement (e := empty_env) (le := le3) (m := m2) (s := dense.id.active)
        (bitId := dense.id.«naugraph:bit») (a := tv dense.id.cell1) hact2 (by have := hok.Mlt; omega) hact3 hcl3 rfl
        (by have := hok.nM; omega) (by have := hok.nlt; omega) hbit2 rfl find_naugraphBit
      rw [hm.actRep.2 cell1 (by have := hok.nM; omega)] at hmem
      wp_step; wp_step; wp_step
      -- the end: `active` gets `x`, `hint` becomes `h'`
      have fin : ∀ (x h' : Nat) (le' : temp_env) (m' : mem), x < n →
          trivialSplit L.level cell1 cell2 c1 k st =
            { splitMid L.level k st with active := st.active.insert x, hint := h' } →
          ArrayAt m' .Mint64 L.ba L.ab (longs (Set.addW aw x)) L.M → Unch m2 m' (· = L.ba) →
          PTree.get dense.id.hint le' = some (.Vint (ir h')) →
          (∀ y, y ≠ dense.id.hint → y ≠ idOf 715 → PTree.get y le' = PTree.get y le3) →
          Q.normal E0 empty_env le' m' := by
        intro x h' le' m' hx heq harr' hu' hh ho'
        have hu : Unch m m' (fun z => z = L.bp ∨ z = L.bn ∨ z = L.ba) :=
          hu12.trans (hu'.mono fun _ h => .inr (.inr h))
        have hw : Unch m m' L.writes := hu.mono fun _ h => by
          rcases h with h | h | h
          · exact .inr (.inl h)
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr (.inr (.inl h))))
        have nk : ∀ i j : Nat, (hij : i < j) → (hj : j < L.blocks.length) → j ∈ [7, 8, 9] →
            i ∈ [2, 3, 5] → ¬ (L.blocks[j] = L.bp ∨ L.blocks[j] = L.bn ∨ L.blocks[j] = L.ba) := by
          intro i j hij hj hjm him
          rintro (h | h | h)
          · exact (hok.ne 2 j (by simp at hjm; omega) hj) h.symm
          · exact (hok.ne 3 j (by simp at hjm; omega) hj) h.symm
          · exact (hok.ne 5 j (by simp at hjm; omega) hj) h.symm
        have kW : Keep m m' L.bW := Keep.unch hu (nk 2 7 (by omega) (by simp [Loc.blocks]) (by simp) (by simp))
        have kS : Keep m m' L.bS := Keep.unch hu (nk 2 8 (by omega) (by simp [Loc.blocks]) (by simp) (by simp))
        have kB : Keep m m' L.bB := Keep.unch hu (nk 2 9 (by omega) (by simp [Loc.blocks]) (by simp) (by simp))
        have hlp := hok.ne 1 2 (by omega)
        have hln := hok.ne 1 3 (by omega)
        have hla := hok.ne 1 5 (by omega)
        have hcp := hok.ne 2 4 (by omega)
        have hcnb := hok.ne 3 4 (by omega)
        have hca := hok.ne 4 5 (by omega)
        obtain ⟨cv, hcv⟩ := hm.cnt
        have hmem' : Mem m' L ctx (trivialSplit L.level cell1 cell2 c1 k st) (Set.addW aw x) := by
          rw [heq]
          refine Mem.frame hok hm hw kW kS kB ?_ ?_ ?_ ?_ ?_ ?_
          · refine hm.lab.unch hu ?_
            rintro (h | h | h)
            · exact hlp h
            · exact hln h
            · exact hla h
          · exact (hp1.unch hu2 hpn).unch hu' hpa
          · exact hnc2.unch hu' hna
          · exact harr'
          · exact Set.setRep_add hm.actRep hx
          · refine ⟨cv, hcv.unch hu ?_⟩
            rintro (h | h | h)
            · exact hcp h.symm
            · exact hcnb h.symm
            · exact hca h
        refine hQ le' m' (Set.addW aw x) hmem' ?_ hu ?_
        · rw [heq]
          refine ht.update (fun y hy => ?_) ?_ hh ?_
          · rw [ho' y (by rintro rfl; revert hy; decide) (by rintro rfl; revert hy; decide),
              ho3 _ (by rintro rfl; revert hy; decide), ho2 _ (by rintro rfl; revert hy; decide)]
          · rw [ho' _ (by decide) (by decide)]; exact hl3
          · rw [ho' _ (by decide) (by decide), ho3 _ (by decide), ho2 _ (by decide)]; exact ht.maxpos
        · intro y h1 h2 h3 h4
          rw [ho' y h4 h1, ho3 y h3, ho2 y h2]
      apply wp_if_eval
      rw [hmem]
      simp only [typeof, cop]
      by_cases hM : st.active.mem cell1 = true
      · rw [ite_eq_left (by simp [hM])]
        apply wp_set_eval
        simp only [Exec.evalExpr]
        apply wp_if_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop]
        rw [ite_eq_left (by decide)]
        generalize hv4 : PTree.set (idOf 715) _ le3 = le4
        -- ADDELEMENT(active, c1); if (c1 == cell2) hint = c1;
        have hD : st.active.mem cell1 = true ∨ cell2 - c1 ≤ k - cell1 := .inl hM
        have ho4 : ∀ y, y ≠ idOf 715 → PTree.get y le4 = PTree.get y le3 := fun y hy => by rw [← hv4]; exact temps_gso _ _ hy
        have hc1_4 : Exec.evalExpr ge empty_env le4 m2 (tv dense.id.c1) = some (.Vint (ir c1)) := by
          show PTree.get _ _ = _
          rw [ho4 _ (by decide), ho3 _ (by decide), ho2 _ (by decide)]; exact hc1
        wp_step
        refine Set.wp_addElementB hact2 (by have := hok.Mlt; omega)
          (by rw [ho4 _ (by decide)]; exact hact3) hc1_4 rfl
          (by have := hok.nM; omega) (by omega) find_naugraphBit hbit2 rfl ?_
        intro m4 harr4 hu4 _
        wp_step; wp_step; wp_step
        simp only [show PTree.get dense.id.c1 le4 = _ from hc1_4,
          show PTree.get dense.id.cell2 le4 = some (.Vint (ir cell2)) by
            rw [ho4 _ (by decide), ho3 _ (by decide), ho2 _ (by decide)]; exact hcell2,
          typeof, cop]
        rw [ir_eq (a := (c1 : Int)) (b := (cell2 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
        have heq0 := trivialSplit_eq L.level cell1 cell2 c1 (k : Int) st hA hB
        rw [ite_eq_left (by simpa using hD)] at heq0
        by_cases he : c1 = cell2
        · rw [ite_eq_left (by simp; omega)]
          wp_step; wp_step
          apply wp_set_eval
          rw [show Exec.evalExpr ge empty_env le4 m4 (tv dense.id.c1) = some (.Vint (ir c1)) from hc1_4]
          refine fin c1 c1 _ m4 (by omega) ?_ harr4 hu4 (temps_gss _ _ _) fun y h1 h2 => ?_
          · rw [heq0, ite_eq_left he]; rfl
          · rw [temps_gso _ _ h1, ho4 _ h2]
        · rw [ite_eq_right (by simp; omega)]
          apply wp_skip
          refine fin c1 st.hint _ m4 (by omega) ?_ harr4 hu4 ?_ fun y _ h2 => ho4 _ h2
          · rw [heq0, ite_eq_right he]; rfl
          · rw [ho4 _ (by decide), ho3 _ (by decide), ho2 _ (by decide)]; exact ht.hint
      · rw [ite_eq_right (by simp [hM])]
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, show PTree.get dense.id.c2 le3 = some (.Vint (ir k)) by
            rw [ho3 _ (by decide), ho2 _ (by decide)]; exact hc2, hcl3,
          show PTree.get dense.id.cell2 le3 = some (.Vint (ir cell2)) by
            rw [ho3 _ (by decide), ho2 _ (by decide)]; exact hcell2,
          show PTree.get dense.id.c1 le3 = some (.Vint (ir c1)) by
            rw [ho3 _ (by decide), ho2 _ (by decide)]; exact hc1, typeof, cop, ir_sub]
        rw [ir_lt (a := (k : Int) - cell1) (b := (cell2 : Int) - c1) ⟨by omega, by omega⟩
          ⟨by omega, by omega⟩]
        by_cases hd : cell2 - c1 ≤ k - cell1
        · rw [show (!decide ((k : Int) - cell1 < cell2 - c1)) = true by simp; omega]
          apply wp_if_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop]
          rw [ite_eq_left (by decide)]
          generalize hv4 : PTree.set (idOf 715) _ le3 = le4
          
          -- ADDELEMENT(active, c1); if (c1 == cell2) hint = c1;
          have hD : st.active.mem cell1 = true ∨ cell2 - c1 ≤ k - cell1 := .inr hd
          have ho4 : ∀ y, y ≠ idOf 715 → PTree.get y le4 = PTree.get y le3 := fun y hy => by rw [← hv4]; exact temps_gso _ _ hy
          have hc1_4 : Exec.evalExpr ge empty_env le4 m2 (tv dense.id.c1) = some (.Vint (ir c1)) := by
            show PTree.get _ _ = _
            rw [ho4 _ (by decide), ho3 _ (by decide), ho2 _ (by decide)]; exact hc1
          wp_step
          refine Set.wp_addElementB hact2 (by have := hok.Mlt; omega)
            (by rw [ho4 _ (by decide)]; exact hact3) hc1_4 rfl
            (by have := hok.nM; omega) (by omega) find_naugraphBit hbit2 rfl ?_
          intro m4 harr4 hu4 _
          wp_step; wp_step; wp_step
          simp only [show PTree.get dense.id.c1 le4 = _ from hc1_4,
            show PTree.get dense.id.cell2 le4 = some (.Vint (ir cell2)) by
              rw [ho4 _ (by decide), ho3 _ (by decide), ho2 _ (by decide)]; exact hcell2,
            typeof, cop]
          rw [ir_eq (a := (c1 : Int)) (b := (cell2 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
          have heq0 := trivialSplit_eq L.level cell1 cell2 c1 (k : Int) st hA hB
          rw [ite_eq_left (by simpa using hD)] at heq0
          by_cases he : c1 = cell2
          · rw [ite_eq_left (by simp; omega)]
            wp_step; wp_step
            apply wp_set_eval
            rw [show Exec.evalExpr ge empty_env le4 m4 (tv dense.id.c1) = some (.Vint (ir c1)) from hc1_4]
            refine fin c1 c1 _ m4 (by omega) ?_ harr4 hu4 (temps_gss _ _ _) fun y h1 h2 => ?_
            · rw [heq0, ite_eq_left he]; rfl
            · rw [temps_gso _ _ h1, ho4 _ h2]
          · rw [ite_eq_right (by simp; omega)]
            apply wp_skip
            refine fin c1 st.hint _ m4 (by omega) ?_ harr4 hu4 ?_ fun y _ h2 => ho4 _ h2
            · rw [heq0, ite_eq_right he]; rfl
            · rw [ho4 _ (by decide), ho3 _ (by decide), ho2 _ (by decide)]; exact ht.hint
        · rw [show (!decide ((k : Int) - cell1 < cell2 - c1)) = false by simp; omega]
          apply wp_if_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop]
          rw [ite_eq_right (by decide)]
          generalize hv4 : PTree.set (idOf 715) _ le3 = le4
          
          -- ADDELEMENT(active, cell1); if (c2 == cell1) hint = cell1;
          have hD : ¬ (st.active.mem cell1 = true ∨ cell2 - c1 ≤ k - cell1) := by rintro (h | h) <;> contradiction
          have ho4 : ∀ y, y ≠ idOf 715 → PTree.get y le4 = PTree.get y le3 := fun y hy => by rw [← hv4]; exact temps_gso _ _ hy
          have hcl_4 : Exec.evalExpr ge empty_env le4 m2 (tv dense.id.cell1) = some (.Vint (ir cell1)) := by
            show PTree.get _ _ = _
            rw [ho4 _ (by decide)]; exact hcl3
          wp_step
          refine Set.wp_addElementB hact2 (by have := hok.Mlt; omega)
            (by rw [ho4 _ (by decide)]; exact hact3) hcl_4 rfl
            (by have := hok.nM; omega) (by omega) find_naugraphBit hbit2 rfl ?_
          intro m4 harr4 hu4 _
          wp_step; wp_step; wp_step
          simp only [show PTree.get dense.id.cell1 le4 = _ from hcl_4,
            show PTree.get dense.id.c2 le4 = some (.Vint (ir k)) by
              rw [ho4 _ (by decide), ho3 _ (by decide), ho2 _ (by decide)]; exact hc2,
            typeof, cop]
          rw [ir_eq (a := (k : Int)) (b := (cell1 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
          have heq0 := trivialSplit_eq L.level cell1 cell2 c1 (k : Int) st hA hB
          rw [ite_eq_right (by simpa using hD)] at heq0
          by_cases he : k = cell1
          · rw [ite_eq_left (by simp; omega)]
            wp_step; wp_step
            apply wp_set_eval
            rw [show Exec.evalExpr ge empty_env le4 m4 (tv dense.id.cell1) = some (.Vint (ir cell1)) from hcl_4]
            refine fin cell1 cell1 _ m4 (by omega) ?_ harr4 hu4 (temps_gss _ _ _) fun y h1 h2 => ?_
            · rw [heq0, ite_eq_left (show (k : Int).toNat = cell1 from he)]; rfl
            · rw [temps_gso _ _ h1, ho4 _ h2]
          · rw [ite_eq_right (by simp; omega)]
            apply wp_skip
            refine fin cell1 st.hint _ m4 (by omega) ?_ harr4 hu4 ?_ fun y _ h2 => ho4 _ h2
            · rw [heq0, ite_eq_right (show ¬ (k : Int).toNat = cell1 from he)]; rfl
            · rw [ho4 _ (by decide), ho3 _ (by decide), ho2 _ (by decide)]; exact ht.hint
    · rw [show (!decide ((cell2 : Int) < c1)) = false by simp; omega]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      apply wp_skip
      exact stop _ fun h => hB h.2
  · rw [ite_eq_right (by simp; omega)]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    apply wp_skip
    exact stop _ fun h => hA h.1


/-- What `trivialSplit` changes. -/
theorem trivialSplit_fields {n : Nat} (level cell1 cell2 : Nat) (c1 c2 : Int) (st : RefineSt n) :
    trivialSplit level cell1 cell2 c1 c2 st = st ∨
      ((cell1 : Int) ≤ c2 ∧ c1 ≤ cell2 ∧
        (trivialSplit level cell1 cell2 c1 c2 st).lab = st.lab ∧
        (trivialSplit level cell1 cell2 c1 c2 st).maxpos = st.maxpos ∧
        (trivialSplit level cell1 cell2 c1 c2 st).numcells = st.numcells + 1 ∧
        (trivialSplit level cell1 cell2 c1 c2 st).ptn = st.ptn.set! c2.toNat level ∧
        ((trivialSplit level cell1 cell2 c1 c2 st).hint = st.hint ∨
          (trivialSplit level cell1 cell2 c1 c2 st).hint = c1.toNat ∨
          (trivialSplit level cell1 cell2 c1 c2 st).hint = cell1) ∧
        (trivialSplit level cell1 cell2 c1 c2 st).longcode < 32768) := by
  have hm := mash_lt st.longcode c2.toNat
  by_cases h : c2 ≥ (cell1 : Int) ∧ c1 ≤ (cell2 : Int)
  · refine .inr ⟨h.1, h.2, ?_⟩
    simp only [trivialSplit, Int.ofNat_eq_natCast]
    rw [ite_eq_left h]
    split
    · split
      · exact ⟨rfl, rfl, rfl, rfl, .inr (.inl rfl), hm⟩
      · exact ⟨rfl, rfl, rfl, rfl, .inl rfl, hm⟩
    · split
      · exact ⟨rfl, rfl, rfl, rfl, .inr (.inr rfl), hm⟩
      · exact ⟨rfl, rfl, rfl, rfl, .inl rfl, hm⟩
  · left
    simp only [trivialSplit, Int.ofNat_eq_natCast]
    rw [ite_eq_right h]

/-! ## The pass over the cells -/

theorem goT_succ {n : Nat} (level : Nat) (gRow : VSet n) (ptn0 : Array Nat) (F c : Nat)
    (st : RefineSt n) (hc : c < n) :
    Hex.GraphIso.Nauty.refineTrivialFast.go level gRow ptn0 (F + 1) c st =
      Hex.GraphIso.Nauty.refineTrivialFast.go level gRow ptn0 F (cellEnd ptn0 level c + 1)
        (trivialCell level gRow c (cellEnd ptn0 level c) st) := by
  rw [Hex.GraphIso.Nauty.refineTrivialFast.go, ite_eq_left hc]

theorem goT_ge {n : Nat} (level : Nat) (gRow : VSet n) (ptn0 : Array Nat) (F c : Nat)
    (st : RefineSt n) (hc : ¬ c < n) :
    Hex.GraphIso.Nauty.refineTrivialFast.go level gRow ptn0 F c st = st := by
  cases F <;> simp [Hex.GraphIso.Nauty.refineTrivialFast.go, hc]

theorem trivialCell_self {n : Nat} (level : Nat) (gRow : VSet n) (c : Nat) (st : RefineSt n) :
    trivialCell level gRow c c st = st := by
  simp [trivialCell]

theorem trivialCell_ne {n : Nat} (level : Nat) (gRow : VSet n) {c e : Nat} (st : RefineSt n)
    (h : c ≠ e) :
    trivialCell level gRow c e st =
      trivialSplit level c e (splitCellLoop gRow (e - c + 2) st.lab c e).2.1
        (splitCellLoop gRow (e - c + 2) st.lab c e).2.2
        { st with lab := (splitCellLoop gRow (e - c + 2) st.lab c e).1 } := by
  simp [trivialCell, h]

/-- The state of the pass when the next cell starts at `p`: memory and
temporaries hold `stc`, and finishing the pass from `p` gives `R`. -/
structure PassInv {n : Nat} (le : temp_env) (m0 m : mem) (L : Loc) (ctx : Ctx n)
    (st0 : RefineSt n) (v0 : Nat) (R : RefineSt n) (p : Nat) (stc : RefineSt n) : Prop where
  mem : ∃ aw, Mem m L ctx stc aw
  unch : Unch m0 m L.writes
  tmp : Tmp le L stc
  gptr : PTree.get dense.id.gptr le =
    some (.Vptr L.bg (ptrTo (intOfZ (Ptrofs.unsigned L.gofs)) 8 (L.M * v0)))
  pn : p ≤ n
  fuel : ∃ F, n - p ≤ F ∧
    R = Hex.GraphIso.Nauty.refineTrivialFast.go L.level ctx.g[v0]! st0.ptn F p stc
  agree : ∀ j, p ≤ j → j < n → stc.ptn[j]! = st0.ptn[j]!
  ok : Hex.GraphIso.Nauty.StOk n L.level stc
  small : ∀ i < n, stc.ptn[i]! < 2147483648
  nc : stc.numcells ≤ st0.numcells + p
  hint : stc.hint < n
  maxpos : stc.maxpos < n
  code : stc.longcode < 2 ^ 62


theorem wp_cellLoopT {f : function} {Q : Post} {le : temp_env} {m0 m : mem} {n : Nat} {L : Loc}
    {ctx : Ctx n} {st0 : RefineSt n} {v0 : Nat} {R stc : RefineSt n}
    (hok : Ok n L) (hv0 : v0 < n) (hok0 : Hex.GraphIso.Nauty.StOk n L.level st0)
    (hI : PassInv le m0 m L ctx st0 v0 R 0 stc)
    (hc : PTree.get dense.id.cell1 le = some (.Vint (ir (0 : Nat))))
    (hQ : ∀ le' m', PassInv le' m0 m' L ctx st0 v0 R n R → Q.normal E0 empty_env le' m') :
    Wp xi ge f cellLoopT Q empty_env le m := by
  have hn := hok.nlt
  have hsz0 : st0.ptn.size = n := hok0.ptnSize
  have hend0 : st0.ptn[n - 1]! ≤ L.level := by have := hok0.ptnEnd; rwa [hsz0] at this
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ c stc, v = n - c ∧ PTree.get dense.id.cell1 le' = some (.Vint (ir c)) ∧
      PassInv le' m0 m' L ctx st0 v0 R c stc
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ c en stc, c ≤ en ∧ en < n ∧ v = n - c ∧
      PTree.get dense.id.cell2 le' = some (.Vint (ir en)) ∧
      PassInv le' m0 m' L ctx st0 v0 R (en + 1) stc
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0) ⟨rfl, rfl, 0, stc, rfl, hc, hI⟩
  · rintro v t e' le' m' ⟨rfl, rfl, c, stc, rfl, hc, hP⟩
    have ht := hP.tmp
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hc, ht.n, typeof, cop]
    have := hP.pn
    rw [ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hcn : c < n
    · rw [ite_eq_left (by simpa using hcn)]
      apply wp_skip
      obtain ⟨aw, hm⟩ := hP.mem
      have hspec := Spec.cellEnd_spec hsz0 hcn hend0
      obtain ⟨F, hF, hR⟩ := hP.fuel
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [goT_succ _ _ _ _ _ _ hcn] at hR
      generalize hen : cellEnd st0.ptn L.level c = en at hspec hR
      obtain ⟨hce, hen', hstop, hgo⟩ := hspec
      wp_step
      refine wp_scanEnd (x := dense.id.cell2) (y := dense.id.cell1) (by decide) (by decide) hm.ptn
        (by omega) ht.ptn ht.level hok.levlt hP.small hc hce hen'
        (by rw [hP.agree en hce hen']; exact hstop)
        (fun i h1 h2 => by rw [hP.agree i h1 (by omega)]; exact hgo i h1 h2) ?_
      intro le1 hcell2 ho1
      have hc1 : PTree.get dense.id.cell1 le1 = some (.Vint (ir c)) := by
        rw [ho1 _ (by decide)]; exact hc
      wp_step; wp_step; wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, hc1, hcell2, typeof, cop]
      rw [ir_eq (a := (c : Int)) (b := (en : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hce' : c = en
      · rw [ite_eq_left (by simp; omega)]
        apply wp_continue
        subst hce'
        rw [trivialCell_self] at hR
        refine ⟨rfl, rfl, c, c, stc, Nat.le_refl _, hen', rfl, hcell2,
          { hP with
            mem := ⟨aw, hm⟩
            tmp := ht.temps fun x hx => ho1 x (by
              rcases hx with hx | rfl | rfl | rfl
              · intro h; subst h; revert hx; decide
              all_goals decide)
            gptr := by rw [ho1 _ (by decide)]; exact hP.gptr
            pn := hen'
            fuel := ⟨F', by omega, hR⟩
            agree := fun j h1 h2 => hP.agree j (by omega) h2
            nc := by have := hP.nc; omega }⟩
      · rw [ite_eq_right (by simp; omega)]
        apply wp_skip
        have hlt : c < en := by omega
        wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, hc1]
        wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gso _ _ (show dense.id.cell2 ≠ dense.id.c1 by decide), hcell2]
        generalize hle2 : PTree.set dense.id.c2 _ (PTree.set dense.id.c1 _ le1) = le2
        have ho2 : ∀ x, x ≠ dense.id.c1 → x ≠ dense.id.c2 → PTree.get x le2 = PTree.get x le1 :=
          fun x h1 h2 => by rw [← hle2, temps_gso _ _ h2, temps_gso _ _ h1]
        have hok' := hP.ok
        have hlsz : stc.lab.size = n := hok'.labSize
        wp_step
        refine wp_swap (v := v0) hm.graph hv0 hok.Mlt hok.nM hm.bit (hok.ne 0 1 (by omega))
          (hok.ne 1 16 (by omega)).symm rfl hm.lab hlsz (fun j hj => hok'.labOk j (by omega))
          (Nat.le_of_lt hlt) hen'
          (by rw [ho2 _ (by decide) (by decide), ho1 _ (by decide)]; exact hP.gptr)
          (by rw [ho2 _ (by decide) (by decide), ho1 _ (by decide)]; exact ht.lab)
          (by rw [← hle2, temps_gso _ _ (by decide), temps_gss])
          (by rw [← hle2, temps_gss]) ?_
        intro le3 m3 lab' c1 c2 hRs harr3 hu3 hs hcc hc13 hc23 ho3
        have ho13 : ∀ x, x ≠ dense.id.c1 → x ≠ dense.id.c2 → x ≠ dense.id.labc1 → x ≠ dense.id.cell2 →
            PTree.get x le3 = PTree.get x le' := fun x h1 h2 h3 h4 => by
          rw [ho3 x h1 h2 h3, ho2 x h1 h2, ho1 x h4]
        let stL : RefineSt n := { stc with lab := lab' }
        have hw3 : Unch m' m3 L.writes := hu3.mono fun _ h => .inl h
        have nl : ∀ k : Nat, (hk : 1 < k) → (hk' : k < L.blocks.length) → L.blocks[k] ≠ L.bl :=
          fun k hk hk' => (hok.ne 1 k hk hk').symm
        obtain ⟨cv, hcv⟩ := hm.cnt
        have hmL : Mem m3 L ctx stL aw :=
          Mem.frame hok hm hw3 (Keep.unch hu3 (nl 7 (by omega) (by simp [Loc.blocks])))
            (Keep.unch hu3 (nl 8 (by omega) (by simp [Loc.blocks])))
            (Keep.unch hu3 (nl 9 (by omega) (by simp [Loc.blocks]))) harr3
            (hm.ptn.unch hu3 (nl 2 (by omega) (by simp [Loc.blocks])))
            (hm.nc.unch hu3 (nl 3 (by omega) (by simp [Loc.blocks])))
            (hm.act.unch hu3 (nl 5 (by omega) (by simp [Loc.blocks]))) hm.actRep
            ⟨cv, hcv.unch hu3 (nl 4 (by omega) (by simp [Loc.blocks]))⟩
        have htL : Tmp le3 L stL := (ht.temps fun x hx => ho13 x
          (by rintro rfl; rcases hx with hx | h | h | h <;> first | (revert hx; decide) | (revert h; decide))
          (by rintro rfl; rcases hx with hx | h | h | h <;> first | (revert hx; decide) | (revert h; decide))
          (by rintro rfl; rcases hx with hx | h | h | h <;> first | (revert hx; decide) | (revert h; decide))
          (by rintro rfl; rcases hx with hx | h | h | h <;> first | (revert hx; decide) | (revert h; decide))).congr
            rfl rfl rfl
        refine wp_trivSplit hok hmL htL hP.code hok'.ptnSize hs.lo hcc hs.hi hen'
          (by rw [ho13 _ (by decide) (by decide) (by decide) (by decide)]; exact hc)
          (by rw [ho3 _ (by decide) (by decide) (by decide), ho2 _ (by decide) (by decide)]; exact hcell2)
          hc13 hc23 ?_
        intro le4 m4 aw4 hm4 ht4 hu4 ho4
        have hTC : trivialCell L.level ctx.g[v0]! c en stc =
            trivialSplit L.level c en (c1 : Int) c2 stL := by
          rw [trivialCell_ne _ _ _ hce', hRs]
        rw [← hTC] at hm4 ht4
        have hpsz := hok'.ptnSize
        have hF : (∀ j, en < j → (trivialCell L.level ctx.g[v0]! c en stc).ptn[j]! = stc.ptn[j]!) ∧
            (∀ i < n, (trivialCell L.level ctx.g[v0]! c en stc).ptn[i]! < 2147483648) ∧
            (trivialCell L.level ctx.g[v0]! c en stc).numcells ≤ stc.numcells + 1 ∧
            (trivialCell L.level ctx.g[v0]! c en stc).hint < n ∧
            (trivialCell L.level ctx.g[v0]! c en stc).maxpos = stc.maxpos ∧
            (trivialCell L.level ctx.g[v0]! c en stc).longcode < 2 ^ 62 := by
          rw [hTC]
          rcases trivialSplit_fields L.level c en (c1 : Int) c2 stL with
            heq | ⟨hA, hB, -, hmax, hnum, hptn, hhint, hcd⟩
          · rw [heq]
            exact ⟨fun _ _ => rfl, hP.small, Nat.le_succ _, hP.hint, rfl, hP.code⟩
          · have hlev := hok.levlt
            refine ⟨fun j hj => ?_, fun i hi => ?_, by rw [hnum]; exact Nat.le_refl _, ?_, hmax, by omega⟩
            · rw [hptn, Array.getElem!_set!_ne _ _ _ _ (by omega)]
            · rw [hptn]
              by_cases hi' : i = c2.toNat
              · subst hi'; rw [Array.getElem!_set!_self _ _ _ (by simp [stL]; omega)]; exact hlev
              · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hi')]; exact hP.small i hi
            · rcases hhint with h | h | h <;> rw [h]
              · exact hP.hint
              · simp; omega
              · omega
        obtain ⟨hagr, hsm, hnum, hhint, hmax, hcd⟩ := hF
        refine ⟨rfl, rfl, c, en, _, Nat.le_of_lt hlt, hen', rfl, ?_,
          { mem := ⟨aw4, hm4⟩
            unch := hP.unch.trans (hw3.trans (hu4.mono fun _ h => by
              rcases h with h | h | h
              · exact .inr (.inl h)
              · exact .inr (.inr (.inl h))
              · exact .inr (.inr (.inr (.inr (.inl h))))))
            tmp := ht4
            gptr := by
              rw [ho4 _ (by decide) (by decide) (by decide) (by decide),
                ho13 _ (by decide) (by decide) (by decide) (by decide)]
              exact hP.gptr
            pn := hen'
            fuel := ⟨F', by omega, hR⟩
            agree := fun j h1 h2 => by rw [hagr j (by omega)]; exact hP.agree j (by omega) h2
            ok := Hex.GraphIso.Nauty.trivialCell_stOk hok' hen'
            small := hsm
            nc := by have := hP.nc; omega
            hint := hhint
            maxpos := by rw [hmax]; exact hP.maxpos
            code := hcd }⟩
        rw [ho4 _ (by decide) (by decide) (by decide) (by decide),
          ho3 _ (by decide) (by decide) (by decide), ho2 _ (by decide) (by decide)]
        exact hcell2
    · rw [ite_eq_right (by simpa using hcn)]
      apply wp_break
      have hcn' : c = n := by omega
      subst hcn'
      obtain ⟨F, -, hR⟩ := hP.fuel
      rw [goT_ge _ _ _ _ _ _ hcn] at hR
      subst hR
      exact hQ le' m' hP
  · rintro v t e' le' m' ⟨rfl, rfl, c, en, stc, hce, hen, rfl, hc2, hP⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hc2, typeof, cop, ir_add]
    refine ⟨n - (en + 1), by omega, by simp, rfl, en + 1, stc, rfl, ?_, ?_⟩
    · rw [temps_gss]; push_cast; rfl
    · exact { hP with
        tmp := hP.tmp.set _ (by decide)
        gptr := by rw [temps_gso _ _ (by decide)]; exact hP.gptr }


/-- `refine`'s pass for a trivial splitting cell is HexGraphIso's `refineTrivial`. -/
theorem wp_trivial : TrivialPass xi := by
  intro n Q le m L ctx st aw split1 hok hm ht hi hnc hs1 hsp hQ
  have hn := hok.nlt
  have hok0 := hi.ok
  have hlsz : st.lab.size = n := hok0.labSize
  have hv0 : st.lab[split1]! < n := hok0.labOk split1 (by omega)
  have hle := eval_at (ge := ge) (e := empty_env) hm.lab (by omega) dense.id.lab ht.lab
    (tv dense.id.split1) split1 hsp hs1 rfl
  wp_step; wp_step; wp_step
  apply wp_set_eval
  have e1 : Exec.evalExpr ge empty_env le m (.Ecast (Set.pv dense.id.g) (tptr tulong)) =
      some (.Vptr L.bg L.gofs) := by simp only [Exec.evalExpr, ht.g, typeof, cop]
  have e3 : Exec.evalExpr ge empty_env le m (.Ecast (ix dense.id.lab (tv dense.id.split1)) tulong) =
      some (.Vlong (lr (st.lab[split1]! : Int))) := by
    rw [Exec.evalExpr, hle]
    simp only [ints, typeof, cop, cast_int_long_ir (a := (st.lab[split1]! : Int)) ⟨by omega, by omega⟩]
  rw [Exec.evalExpr, e1, Exec.evalExpr, show Exec.evalExpr ge empty_env le m (tv dense.id.m) = _ from ht.m,
    e3]
  have hMlt := hok.Mlt
  simp only [typeof, cop, Graph.mul_lr (show L.M < 2147483648 by omega)]
  rw [show ((L.M : Int) * (st.lab[split1]! : Int)) = ((L.M * st.lab[split1]! : Nat) : Int) by
    push_cast; rfl, Graph.add_ptrTo_long]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  have hR : Hex.GraphIso.Nauty.refineTrivial ctx L.level split1 st =
      Hex.GraphIso.Nauty.refineTrivialFast.go L.level ctx.g[st.lab[split1]!]! st.ptn n 0 st := by
    rw [Hex.GraphIso.Nauty.refineTrivial_eq_fast]; rfl
  refine wp_cellLoopT (st0 := st) (v0 := st.lab[split1]!) hok hv0 hok0
    { mem := ⟨aw, hm⟩
      unch := Unch.refl _ _
      tmp := (ht.set _ (by decide)).set _ (by decide)
      gptr := by rw [temps_gso _ _ (by decide), temps_gss]
      pn := Nat.zero_le _
      fuel := ⟨n, by omega, hR⟩
      agree := fun _ _ _ => rfl
      ok := hok0
      small := hi.ptnSmall
      nc := Nat.le_add_right _ _
      hint := hi.hint
      maxpos := hi.maxpos
      code := hi.code } (by rw [temps_gss]; rfl) ?_
  intro le' m' hP
  obtain ⟨aw', hm'⟩ := hP.mem
  exact hQ le' m' ⟨aw', hm', hP.tmp,
    { ok := hP.ok, ptnSmall := hP.small, ncSmall := by have := hP.nc; omega, hint := hP.hint,
      maxpos := hP.maxpos, code := hP.code }⟩ hP.unch

end NautyVerified.Proofs.Refine

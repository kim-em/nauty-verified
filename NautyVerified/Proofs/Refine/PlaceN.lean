import NautyVerified.Proofs.Refine.ScanN
import NautyVerified.Spec.NtcPlace

/-!
# The counting-sort placement of the nontrivial pass

`wp_placeLoop`: `for (i = cell1; i <= cell2; ++i) workperm[bucket[count[i]]++] = lab[i];`
writes member `o` of the cell at its destination `dest o` (the start of its
count group plus the number of earlier members of the group).
`wp_copyLoop`: `for (i = cell1; i <= cell2; ++i) lab[i] = workperm[i];`.
Together they leave in `lab` HexGraphIso's `writeSegment … (segmentOf …)`
(`fold_getElem!`).
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Spec.Ntc
open NautyVerified.Source NautyVerified.Proofs NautyVerified.Proofs.Alloc
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

theorem toArray_get! (cs : List Nat) (q : Nat) : cs.toArray[q]! = cs[q]! := by
  by_cases h : q < cs.length
  · rw [getElem!_pos cs.toArray q (by simpa using h), getElem!_pos cs q h]; simp
  · rw [getElem!_neg cs.toArray q (by simpa using h), getElem!_neg cs q h]

/-- A cell's members, in cell order. -/
def members (lab : Array Nat) (cell1 len : Nat) : Array Nat :=
  ((List.range len).map fun o => lab[cell1 + o]!).toArray

theorem members_get (lab : Array Nat) (cell1 len o : Nat) (ho : o < len) :
    (members lab cell1 len)[o]! = lab[cell1 + o]! := by
  rw [getElem!_pos _ o (by simp [members]; exact ho)]
  simp [members]

/-- The destination of member `o`. -/
abbrev dst (cs : List Nat) (A cell1 o : Nat) : Nat :=
  dest cs.toArray A (fun w => cell1 + baseOff cs.toArray A w) o

/-- `workperm`, modelled after the first `o` placements from a sentinel array. -/
def placed' (cs : List Nat) (A cell1 : Nat) (mem : Array Nat) (n o : Nat) : Array Nat :=
  (List.range o).foldl (fun a k => a.set! (dst cs A cell1 k) mem[k]!) (Array.replicate n n)

theorem placed'_succ (cs : List Nat) (A cell1 : Nat) (mem : Array Nat) (n o : Nat) :
    placed' cs A cell1 mem n (o + 1) = (placed' cs A cell1 mem n o).set! (dst cs A cell1 o) mem[o]! := by
  simp [placed', List.range_succ]

theorem placed'_size (cs : List Nat) (A cell1 : Nat) (mem : Array Nat) (n : Nat) :
    ∀ o, (placed' cs A cell1 mem n o).size = n
  | 0 => by simp [placed']
  | o + 1 => by rw [placed'_succ, Array.size_set!, placed'_size]

/-- The `workperm` values after `o` placements. -/
def wpVals (cs : List Nat) (A cell1 : Nat) (mem : Array Nat) (n o : Nat) (wv0 : Nat → val)
    (p : Nat) : val :=
  if p < n ∧ (placed' cs A cell1 mem n o)[p]! < n then .Vint (ir ((placed' cs A cell1 mem n o)[p]! : Nat))
  else wv0 p

/-- The `bucket` cursors after `o` placements. -/
def curVals (cs : List Nat) (A B cell1 o : Nat) (bv0 : Nat → val) (v : Nat) : val :=
  if A ≤ v ∧ v ≤ B then
    (if multOf cs v = 0 then .Vint (ir 0) else
      .Vint (ir (cell1 + baseOff cs.toArray A (v - A) + placed cs.toArray A o (v - A) : Nat)))
  else bv0 v

/-- `baseOff` counts the counts below a value. -/
theorem baseOff_below {cs : List Nat} {A v : Nat} (hA : ∀ c ∈ cs, A ≤ c) (hv : A ≤ v) :
    baseOff cs.toArray A (v - A) = below cs v := by
  rw [baseOff_eq_countP, List.toList_toArray]
  apply List.countP_congr
  intro c hc
  have := hA c hc
  simp only [decide_eq_true_eq]
  omega

theorem wpVals_zero (cs : List Nat) (A cell1 : Nat) (mem : Array Nat) (n : Nat) (wv0 : Nat → val)
    (p : Nat) : wpVals cs A cell1 mem n 0 wv0 p = wv0 p := by
  unfold wpVals
  rw [ite_eq_right]
  intro ⟨hp, h⟩
  simp only [placed', List.range_zero, List.foldl_nil] at h
  rw [getElem!_pos _ p (by simpa using hp)] at h
  simp at h

theorem wpVals_succ (cs : List Nat) (A cell1 : Nat) (mem : Array Nat) (n o : Nat) (wv0 : Nat → val)
    (hd : dst cs A cell1 o < n) (hm : mem[o]! < n) (p : Nat) :
    upd (wpVals cs A cell1 mem n o wv0) (dst cs A cell1 o) (.Vint (ir (mem[o]! : Nat))) p =
      wpVals cs A cell1 mem n (o + 1) wv0 p := by
  unfold wpVals upd
  rw [placed'_succ]
  have hsz := placed'_size cs A cell1 mem n o
  by_cases hp : p = dst cs A cell1 o
  · subst hp
    rw [ite_eq_left rfl, Array.getElem!_set!_self _ _ _ (by omega), ite_eq_left ⟨hd, hm⟩]
  · rw [ite_eq_right hp, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hp)]

theorem curVals_succ {cs : List Nat} {A B cell1 o : Nat} (bv0 : Nat → val)
    (hAo : A ≤ cs[o]!) (hoB : cs[o]! ≤ B) (hmul : multOf cs cs[o]! ≠ 0) (v : Nat) :
    upd (curVals cs A B cell1 o bv0) cs[o]! (.Vint (ir ((dst cs A cell1 o : Nat) + 1))) v =
      curVals cs A B cell1 (o + 1) bv0 v := by
  have hco : cs.toArray[o]! = cs[o]! := toArray_get! cs o
  unfold curVals upd
  by_cases hv : v = cs[o]!
  · subst hv
    rw [ite_eq_left rfl, ite_eq_left ⟨hAo, hoB⟩, ite_eq_right hmul, placed_succ, hco,
      ite_eq_left (by simp)]
    simp only [dst, dest, hco]
    push_cast; rfl
  · rw [ite_eq_right hv]
    dsimp only
    by_cases hw : A ≤ v ∧ v ≤ B
    · rw [ite_eq_left hw, ite_eq_left hw]
      by_cases hm : multOf cs v = 0
      · rw [ite_eq_left hm, ite_eq_left hm]
      · have hw1 := hw.1
        have hne : cs[o]! - A ≠ v - A := fun h => hv (by omega)
        rw [ite_eq_right hm, ite_eq_right hm, placed_succ, hco, ite_eq_right (by simpa using hne),
          Nat.add_zero]
    · rw [ite_eq_right hw, ite_eq_right hw]

/-- The counting-sort placement, with SimplExpr's temporary `t`. -/
abbrev placeLoopG (t : Common.AST.ident) : statement :=
  (.Sloop
    (.Ssequence
      (Set.sk (.Sifthenelse (.Ebinop .Ole (tv dense.id.«i») (tv dense.id.«cell2») tint) .Sskip .Sbreak))
      (.Ssequence
        (.Ssequence
          (Set.sk (.Sset t (gix dense.id.«naugraph:bucket» (ix dense.id.«count» (tv dense.id.«i»)))))
          (.Sassign
            (gix dense.id.«naugraph:bucket» (ix dense.id.«count» (tv dense.id.«i»)))
            (.Ebinop .Oadd (tv t) (ci 1 tint) tint)))
        (.Sassign (gix dense.id.«naugraph:workperm» (tv t)) (ix dense.id.«lab» (tv dense.id.«i»)))))
    (Set.sk (.Sset dense.id.«i» (.Ebinop .Oadd (tv dense.id.«i») (ci 1 tint) tint))))

theorem placeLoop_D0 : placeLoop = placeLoopG (idOf 731) := rfl

theorem placeLoop_D1 : Refine1.placeLoop = placeLoopG (idOf 722) := rfl

theorem wp_placeLoop {t : Common.AST.ident} (hT : NTemps [t]) {f : function} {Q : Post} {le : temp_env} {m : mem} {n : Nat} {L : Loc} {cs : List Nat}
    {lab : Array Nat} {cell1 cell2 A B : Nat} {cv0 bv0 wv0 : Nat → val}
    (hok : Ok n L) (hcapW : L.capW < 2147483648) (hcapB : L.capB < 2147483648)
    (hlen : cs.length = cell2 + 1 - cell1) (h12 : cell1 < cell2) (h2n : cell2 < n)
    (hAc : ∀ c ∈ cs, A ≤ c ∧ c ≤ B) (hBn : B ≤ n)
    (hi : PTree.get dense.id.i le = some (.Vint (ir cell1)))
    (hcl2 : PTree.get dense.id.cell2 le = some (.Vint (ir cell2)))
    (hcount : PTree.get dense.id.count le = some (.Vptr L.bc L.cofs))
    (hlabp : PTree.get dense.id.lab le = some (.Vptr L.bl L.lofs))
    (hlarr : ArrayAt m .Mint32 L.bl L.lb (ints lab) n) (hlabs : ∀ i < n, lab[i]! < n)
    (hcnt : ArrayAt m .Mint32 L.bc L.cb (cntVals cs cell1 (cell2 - cell1) cv0) n)
    (hbkt : ArrayAt m .Mint32 L.bB 0 (curVals cs A B cell1 0 bv0) L.capB)
    (hbkp : Mem.load .Mint64 m Block.naugraphBucket (zOfInt 0) = some (.Vptr L.bB Ptrofs.zero))
    (hwp : ArrayAt m .Mint32 L.bW 0 wv0 L.capW)
    (hwpp : Mem.load .Mint64 m Block.naugraphWorkperm (zOfInt 0) = some (.Vptr L.bW Ptrofs.zero))
    (hQ : ∀ le' m',
      ArrayAt m' .Mint32 L.bW 0
        (wpVals cs A cell1 (members lab cell1 cs.length) n cs.length wv0) L.capW →
      (∃ v, ArrayAt m' .Mint32 L.bB 0 v L.capB) →
      Unch m m' (fun z => z = L.bB ∨ z = L.bW) → Keep m m' L.bB → Keep m m' L.bW →
      (∀ z, z ≠ dense.id.i → z ≠ t → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f (placeLoopG t) Q empty_env le m := by
  have d := hok.wd
  have hnl := hok.nlt
  have hcW := hok.capW
  have hcB := hok.capB
  generalize hlen' : cs.length = len at *
  have hco : ∀ q, cs.toArray[q]! = cs[q]! := toArray_get! cs
  have hsz : cs.toArray.size = len := by simp [hlen']
  have hmem : ∀ q, q < len → cs[q]! ∈ cs := fun q hq => by
    rw [getElem!_pos cs q (by omega)]; exact List.getElem_mem _
  have hbd : ∀ q, q < cs.toArray.size → cs.toArray[q]! - A < B + 1 - A := fun q hq => by
    rw [hco]
    have := hAc _ (hmem q (by omega))
    omega
  let mb := members lab cell1 len
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ o, o ≤ len ∧ v = len - o ∧
      PTree.get dense.id.i le' = some (.Vint (ir (cell1 + o : Nat))) ∧
      ArrayAt m' .Mint32 L.bB 0 (curVals cs A B cell1 o bv0) L.capB ∧
      ArrayAt m' .Mint32 L.bW 0 (wpVals cs A cell1 mb n o wv0) L.capW ∧
      Unch m m' (fun z => z = L.bB ∨ z = L.bW) ∧ Keep m m' L.bB ∧ Keep m m' L.bW ∧
      (∀ z, z ≠ dense.id.i → z ≠ t → PTree.get z le' = PTree.get z le)
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ o, o < len ∧ v = len - o ∧
      PTree.get dense.id.i le' = some (.Vint (ir (cell1 + o : Nat))) ∧
      ArrayAt m' .Mint32 L.bB 0 (curVals cs A B cell1 (o + 1) bv0) L.capB ∧
      ArrayAt m' .Mint32 L.bW 0 (wpVals cs A cell1 mb n (o + 1) wv0) L.capW ∧
      Unch m m' (fun z => z = L.bB ∨ z = L.bW) ∧ Keep m m' L.bB ∧ Keep m m' L.bW ∧
      (∀ z, z ≠ dense.id.i → z ≠ t → PTree.get z le' = PTree.get z le)
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := len) ⟨rfl, rfl, 0, Nat.zero_le _, rfl,
    by simpa using hi, hbkt, hwp.congr fun p _ => (wpVals_zero _ _ _ _ _ _ p).symm, Unch.refl _ _,
    Keep.refl _ _, Keep.refl _ _, fun _ _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, o, ho, rfl, hio, hbk, hwk, hu, hkB, hkW, hoth⟩
    have nB : ∀ {z}, L.bB ≠ z → L.bW ≠ z → ¬ (z = L.bB ∨ z = L.bW) := fun h1 h2 h => by
      rcases h with h | h
      · exact h1 h.symm
      · exact h2 h.symm
    have hcl2' : PTree.get dense.id.cell2 le' = some (.Vint (ir cell2)) := by
      rw [hoth _ (by nscr) (by nscr)]; exact hcl2
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hio, hcl2', typeof, cop]
    rw [ir_lt (a := (cell2 : Int)) (b := ((cell1 + o : Nat) : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hoL : o = len
    · rw [ite_eq_right (by simp; omega)]
      apply wp_break
      subst hoL
      exact hQ le' m' hwk ⟨_, hbk⟩ hu hkB hkW hoth
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      have hol : o < len := by omega
      have hcm := hAc _ (hmem o hol)
      have hcount' : PTree.get dense.id.count le' = some (.Vptr L.bc L.cofs) := by
        rw [hoth _ (by nscr) (by nscr)]; exact hcount
      have hlabp' : PTree.get dense.id.lab le' = some (.Vptr L.bl L.lofs) := by
        rw [hoth _ (by nscr) (by nscr)]; exact hlabp
      have hcnt' := hcnt.unch hu (nB (Ne.symm d.bc_bB) (Ne.symm d.bc_bW))
      have hlarr' := hlarr.unch hu (nB (Ne.symm d.bl_bB) (Ne.symm d.bl_bW))
      have hbkp' : Mem.load .Mint64 m' Block.naugraphBucket (zOfInt 0) =
          some (.Vptr L.bB Ptrofs.zero) := by rw [hu.load _ _ _ (nB d.bB_g4 d.bW_g4)]; exact hbkp
      have hwpp' : Mem.load .Mint64 m' Block.naugraphWorkperm (zOfInt 0) =
          some (.Vptr L.bW Ptrofs.zero) := by rw [hu.load _ _ _ (nB d.bB_g0 d.bW_g0)]; exact hwpp
      have hcread : Exec.evalExpr ge empty_env le' m' (ix dense.id.count (tv dense.id.i)) =
          some (.Vint (ir (cs[o]! : Nat))) := by
        rw [eval_atV hcnt' (by omega) dense.id.count hcount' (tv dense.id.i) (cell1 + o) (by omega)
          hio rfl]
        simp only [cntVals]
        rw [ite_eq_left (by omega), show cell1 + o - cell1 = o by omega]
      have hmul : multOf cs cs[o]! ≠ 0 := by
        rw [multOf]; apply Nat.pos_iff_ne_zero.1; apply List.countP_pos_iff.2
        exact ⟨_, hmem o hol, by simp⟩
      have hdr := dest_range cs.toArray A (B + 1 - A) cell1 hbd o (by omega)
      rw [hsz] at hdr
      have hdr1 : cell1 ≤ dst cs A cell1 o := hdr.1
      have hdr2 : dst cs A cell1 o < cell1 + len := hdr.2
      have hdst : dst cs A cell1 o = cell1 + baseOff cs.toArray A (cs[o]! - A) +
          placed cs.toArray A o (cs[o]! - A) := by simp only [dst, dest, hco]
      have hbread := eval_gat (e := empty_env) (le := le') rfl find_naugraphBucket hbkp' hbk hcapB
        (ix dense.id.count (tv dense.id.i)) cs[o]! (by omega) hcread rfl
      simp only [curVals] at hbread
      rw [ite_eq_left ⟨hcm.1, hcm.2⟩, ite_eq_right hmul, ← hdst] at hbread
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [hbread]
      refine wp_gstore rfl find_naugraphBucket hbkp' hbk hcapB (ix dense.id.count (tv dense.id.i))
        cs[o]! (by omega)
        (eval_atV hcnt' (by omega) dense.id.count (by rw [temps_gso _ _ (by nscr)]; exact hcount')
          (tv dense.id.i) (cell1 + o) (by omega)
          (by show PTree.get _ _ = _; rw [temps_gso _ _ (by nscr)]; exact hio) rfl |>.trans (by
            simp only [cntVals]
            rw [ite_eq_left (by omega), show cell1 + o - cell1 = o by omega])) rfl _
        ((dst cs A cell1 o : Nat) + 1)
        (eval_add_ii (y := 1) (by show PTree.get _ _ = _; rw [temps_gss]) rfl rfl rfl) rfl ?_
      intro m1 hbk1 hu1 hk1
      have hwk1 := hwk.unch hu1 d.bW_bB
      have hwpp1 : Mem.load .Mint64 m1 Block.naugraphWorkperm (zOfInt 0) =
          some (.Vptr L.bW Ptrofs.zero) := by rw [hu1.load _ _ _ (Ne.symm d.bB_g0)]; exact hwpp'
      have hlarr1 := hlarr'.unch hu1 d.bl_bB
      have hlab_o := hlabs (cell1 + o) (by omega)
      refine wp_gstore rfl find_naugraphWorkperm hwpp1 hwk1 hcapW (tv t) (dst cs A cell1 o)
        (by omega) (by show PTree.get _ _ = _; rw [temps_gss]) rfl (ix dense.id.lab (tv dense.id.i))
        (lab[cell1 + o]! : Nat) ?_ rfl ?_
      · rw [eval_at hlarr1 (by omega) dense.id.lab (by rw [temps_gso _ _ (by nscr)]; exact hlabp')
          (tv dense.id.i) (cell1 + o) (by omega)
          (by show PTree.get _ _ = _; rw [temps_gso _ _ (by nscr)]; exact hio) rfl]
        rfl
      intro m2 hwk2 hu2 hk2
      have hmbo : mb[o]! = lab[cell1 + o]! := members_get lab cell1 len o hol
      refine ⟨by simp, rfl, o, hol, rfl,
        by rw [temps_gso _ _ (by nscr)]; exact hio,
        (hbk1.unch hu2 (Ne.symm d.bW_bB)).congr fun v _ => curVals_succ bv0 hcm.1 hcm.2 hmul v,
        hwk2.congr fun p _ => ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hmbo]
        exact wpVals_succ cs A cell1 mb n o wv0 (by omega) (by rw [hmbo]; exact hlab_o) p
      · exact (hu.trans (hu1.mono fun z hz => .inl hz)).trans (hu2.mono fun z hz => .inr hz)
      · exact (hkB.trans hk1).trans (Keep.unch hu2 d.bW_bB.symm)
      · exact (hkW.trans (Keep.unch hu1 d.bW_bB)).trans hk2
      · intro z h1 h2; rw [temps_gso _ _ h2, hoth z h1 h2]
  · rintro v tr e' le' m' ⟨rfl, rfl, o, ho, rfl, hio, hbk, hwk, hu, hkB, hkW, hoth⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hio, typeof, cop, ir_add]
    refine ⟨len - (o + 1), by omega, by simp, rfl, o + 1, by omega, rfl, ?_, hbk, hwk, hu, hkB, hkW,
      fun z h1 h2 => by rw [temps_gso _ _ h1, hoth z h1 h2]⟩
    rw [temps_gss]; push_cast; rw [Int.add_assoc]

theorem wp_copyLoop {f : function} {Q : Post} {le : temp_env} {m : mem} {n : Nat} {L : Loc}
    {lab0 T : Array Nat} {cell1 cell2 : Nat} {wv : Nat → val}
    (hok : Ok n L) (hcapW : L.capW < 2147483648) (h12 : cell1 < cell2) (h2n : cell2 < n)
    (hi : PTree.get dense.id.i le = some (.Vint (ir cell1)))
    (hcl2 : PTree.get dense.id.cell2 le = some (.Vint (ir cell2)))
    (hlabp : PTree.get dense.id.lab le = some (.Vptr L.bl L.lofs))
    (hlarr : ArrayAt m .Mint32 L.bl L.lb (ints lab0) n)
    (hwp : ArrayAt m .Mint32 L.bW 0 wv L.capW)
    (hwpp : Mem.load .Mint64 m Block.naugraphWorkperm (zOfInt 0) = some (.Vptr L.bW Ptrofs.zero))
    (hT : ∀ q, cell1 ≤ q → q ≤ cell2 → wv q = .Vint (ir (T[q]! : Nat)))
    (hT0 : ∀ q, q < n → ¬ (cell1 ≤ q ∧ q ≤ cell2) → T[q]! = lab0[q]!)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 L.bl L.lb (ints T) n → Unch m m' (· = L.bl) →
      (∀ z, z ≠ dense.id.i → PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f copyLoop Q empty_env le m := by
  have d := hok.wd
  have hnl := hok.nlt
  have hcW := hok.capW
  let len := cell2 + 1 - cell1
  let lv := fun (o : Nat) (q : Nat) => if cell1 ≤ q ∧ q < cell1 + o then ints T q else ints lab0 q
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ o, o ≤ len ∧ v = len - o ∧
      PTree.get dense.id.i le' = some (.Vint (ir (cell1 + o : Nat))) ∧
      ArrayAt m' .Mint32 L.bl L.lb (lv o) n ∧ Unch m m' (· = L.bl) ∧
      (∀ z, z ≠ dense.id.i → PTree.get z le' = PTree.get z le)
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ o, o < len ∧ v = len - o ∧
      PTree.get dense.id.i le' = some (.Vint (ir (cell1 + o : Nat))) ∧
      ArrayAt m' .Mint32 L.bl L.lb (lv (o + 1)) n ∧ Unch m m' (· = L.bl) ∧
      (∀ z, z ≠ dense.id.i → PTree.get z le' = PTree.get z le)
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := len) ⟨rfl, rfl, 0, Nat.zero_le _, rfl,
    by simpa using hi, hlarr.congr fun q _ => by simp only [lv]; rw [ite_eq_right (by omega)],
    Unch.refl _ _, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, o, ho, rfl, hio, hla, hu, hoth⟩
    have hcl2' : PTree.get dense.id.cell2 le' = some (.Vint (ir cell2)) := by
      rw [hoth _ (by decide)]; exact hcl2
    have hlabp' : PTree.get dense.id.lab le' = some (.Vptr L.bl L.lofs) := by
      rw [hoth _ (by decide)]; exact hlabp
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hio, hcl2', typeof, cop]
    rw [ir_lt (a := (cell2 : Int)) (b := ((cell1 + o : Nat) : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hoL : o = len
    · rw [ite_eq_right (by simp; omega)]
      apply wp_break
      subst hoL
      refine hQ le' m' (hla.congr fun q hq => ?_) hu hoth
      simp only [lv]
      by_cases hq2 : cell1 ≤ q ∧ q < cell1 + len
      · rw [ite_eq_left hq2]
      · rw [ite_eq_right hq2]; simp only [ints]; rw [hT0 q hq (by omega)]
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      have hwp' := hwp.unch hu (Ne.symm d.bl_bW)
      have hwpp' : Mem.load .Mint64 m' Block.naugraphWorkperm (zOfInt 0) =
          some (.Vptr L.bW Ptrofs.zero) := by rw [hu.load _ _ _ (Ne.symm d.bl_g0)]; exact hwpp
      have hrd := eval_gat (e := empty_env) (le := le') rfl find_naugraphWorkperm hwpp' hwp' hcapW
        (tv dense.id.i) (cell1 + o) (by omega) hio rfl
      rw [hT (cell1 + o) (by omega) (by omega)] at hrd
      wp_step; wp_step
      refine wp_storeV hla (by omega) dense.id.lab hlabp' (tv dense.id.i) (cell1 + o) (by omega) hio
        rfl _ _ hrd rfl ?_
      intro m1 hla1 hu1
      refine ⟨by simp, rfl, o, by omega, rfl, hio, hla1.congr fun q _ => ?_, hu.trans hu1, hoth⟩
      simp only [lv, upd]
      by_cases hq : q = cell1 + o
      · subst hq; rw [ite_eq_left rfl, ite_eq_left (by omega)]; rfl
      · rw [ite_eq_right hq]
        by_cases hq2 : cell1 ≤ q ∧ q < cell1 + o
        · rw [ite_eq_left hq2, ite_eq_left (by omega)]
        · rw [ite_eq_right hq2, ite_eq_right (by omega)]
  · rintro v tr e' le' m' ⟨rfl, rfl, o, ho, rfl, hio, hla, hu, hoth⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hio, typeof, cop, ir_add]
    refine ⟨len - (o + 1), by omega, by simp, rfl, o + 1, by omega, rfl, ?_, hla, hu,
      fun z h1 => by rw [temps_gso _ _ h1, hoth z h1]⟩
    rw [temps_gss]; push_cast; rw [Int.add_assoc]

end NautyVerified.Proofs.Refine

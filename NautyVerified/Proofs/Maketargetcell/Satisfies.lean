import NautyVerified.Proofs.Maketargetcell.Loops
import NautyVerified.Proofs.Targetcell.Satisfies

/-!
# `maketargetcell` meets its specification

`maketargetcellSpec`: with `targetcell` passed as the function pointer and a
nontrivial cell present, nautil.c's `maketargetcell` stores HexGraphIso's
`maketargetcell ⟨g⟩ lab ptn level tcLevel hint` into `tcell`, `*tcellsize` and
`*cellpos`.
-/

namespace NautyVerified.Proofs.Maketargetcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Spec.Bestcell
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Alloc (DynAt Keep dyn3Set ne_new)
open NautyVerified.Proofs.Bestcell (Pre Post WP WPS WS WSS BK BKS not_dyn3)
open NautyVerified.Proofs.Targetcell (targetcellSpec targetcell_satisfies)
open NautyVerified.Proofs.Updatecan (tv)
open Hex.GraphIso.Nauty (VSet cellEnd worksetOf)

/-- The caller's output blocks `tcell`, `tcellsize`, `cellpos` and nautil.c's
`bit`: valid, apart from what `targetcell` may change and from each other. -/
structure Out (m : mem) (capP : Nat) (bP : block) (capS : Nat) (bS : block) (capB : Nat)
    (bB : block) (bg bl bp bt bz bc : block) : Prop where
  out : ∀ z, z = bt ∨ z = bz ∨ z = bc ∨ z = Block.nautilBit → Mem.valid_block m z ∧ z ≠ WP ∧
    z ≠ WPS ∧ z ≠ WS ∧ z ≠ WSS ∧ z ≠ BK ∧ z ≠ BKS ∧ (0 < capP → z ≠ bP) ∧ (0 < capS → z ≠ bS) ∧
    (0 < capB → z ≠ bB)
  sep : ∀ z, z = bt ∨ z = bz ∨ z = bc → z ≠ bg ∧ z ≠ bl ∧ z ≠ bp ∧ z ≠ Block.nautilBit
  tz : bt ≠ bz
  tc : bt ≠ bc
  zc : bz ≠ bc

def maketargetcellSpec {n : Nat} (bg : block) (gofs : ptrofs) (gw : Nat → Lib.Integers.int64)
    (grows : Array (VSet n)) (bl : block) (lofs : ptrofs) (lab : Array Nat) (bp : block)
    (pofs : ptrofs) (ptn : Array Nat) (level : Nat) (bt : block) (tofs : ptrofs)
    (tvals : Nat → val) (bz : block) (zofs : ptrofs) (zvals : Nat → val) (bc : block)
    (cofs : ptrofs) (cvals : Nat → val) (tcLevel : Nat) (dg : Lib.Integers.int) (hint : Int)
    (M capP : Nat) (bP : block) (capS : Nat) (bS : block) (capB : Nat) (bB : block) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bl lofs, .Vptr bp pofs, .Vint (ir level),
      .Vptr bt tofs, .Vptr bz zofs, .Vptr bc cofs, .Vint (ir tcLevel), .Vint dg, .Vint (ir hint),
      .Vptr Block.targetcell Ptrofs.zero, .Vint (ir M), .Vint (ir n)] ∧
    Pre m bg gofs gw grows bl lofs lab bp pofs ptn level M capP bP capS bS capB bB ∧
    hint < n ∧ -2147483648 ≤ hint ∧ tcLevel < 2147483648 ∧ (∃ x < n, level < ptn[x]!) ∧
    ArrayAt m .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) tvals M ∧
    ArrayAt m .Mint32 bz (intOfZ (Ptrofs.unsigned zofs)) zvals 1 ∧
    ArrayAt m .Mint32 bc (intOfZ (Ptrofs.unsigned cofs)) cvals 1 ∧ BitTable m Block.nautilBit ∧
    Out m capP bP capS bS capB bB bg bl bp bt bz bc
  post _ m t _ m' := t = E0 ∧
    (∃ ws, ArrayAt m' .Mint64 bt (intOfZ (Ptrofs.unsigned tofs)) (longs ws) M ∧
      SetRep (fun w => bv64 (ws w)) M
        (Hex.GraphIso.Nauty.maketargetcell ⟨grows⟩ lab ptn level tcLevel hint).2.1) ∧
    ArrayAt m' .Mint32 bz (intOfZ (Ptrofs.unsigned zofs)) (fun _ => .Vint (ir
      ((Hex.GraphIso.Nauty.maketargetcell ⟨grows⟩ lab ptn level tcLevel hint).2.2 : Int))) 1 ∧
    ArrayAt m' .Mint32 bc (intOfZ (Ptrofs.unsigned cofs)) (fun _ => .Vint (ir
      ((Hex.GraphIso.Nauty.maketargetcell ⟨grows⟩ lab ptn level tcLevel hint).1 : Int))) 1 ∧
    ∃ capP' bP' capS' bS' capB' bB', DynAt m' WP WPS 4 capP' bP' ∧ DynAt m' WS WSS 8 capS' bS' ∧
      DynAt m' BK BKS 4 capB' bB' ∧
      ((capP' = capP ∧ bP' = bP) ∨ ¬ Mem.valid_block m bP') ∧
      ((capS' = capS ∧ bS' = bS) ∨ ¬ Mem.valid_block m bS') ∧
      ((capB' = capB ∧ bB' = bB) ∨ ¬ Mem.valid_block m bB') ∧
      Unch m m' (fun z => dyn3Set m capP bP capS bS capB bB z ∨ z = bt ∨ z = bz ∨ z = bc) ∧
      (0 < capP' → 0 < capS' → bP' ≠ bS') ∧ (0 < capP' → 0 < capB' → bP' ≠ bB') ∧
      (0 < capS' → 0 < capB' → bS' ≠ bB')

def entryTemps (bg : block) (gofs : ptrofs) (bl : block) (lofs : ptrofs) (bp : block)
    (pofs : ptrofs) (level : Nat) (bt : block) (tofs : ptrofs) (bz : block) (zofs : ptrofs)
    (bc : block) (cofs : ptrofs) (tcLevel : Nat) (dg : Lib.Integers.int) (hint : Int) (M n : Nat) :
    temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.targetcell (.Vptr Block.targetcell Ptrofs.zero)
      (PTree.set id.hint (.Vint (ir hint)) (PTree.set id.digraph (.Vint dg)
        (PTree.set id.tc_level (.Vint (ir tcLevel)) (PTree.set id.cellpos (.Vptr bc cofs)
          (PTree.set id.tcellsize (.Vptr bz zofs) (PTree.set id.tcell (.Vptr bt tofs)
            (PTree.set id.level (.Vint (ir level)) (PTree.set id.ptn (.Vptr bp pofs)
              (PTree.set id.lab (.Vptr bl lofs) (PTree.set id.g (.Vptr bg gofs)
                (create_undef_temps Source.dense.fn.maketargetcell.fn_temps)))))))))))))

theorem maketargetcell_satisfies {xi : ExternalCalls} {n : Nat} (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (grows : Array (VSet n)) (bl : block) (lofs : ptrofs)
    (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat) (level : Nat) (bt : block)
    (tofs : ptrofs) (tvals : Nat → val) (bz : block) (zofs : ptrofs) (zvals : Nat → val)
    (bc : block) (cofs : ptrofs) (cvals : Nat → val) (tcLevel : Nat) (dg : Lib.Integers.int)
    (hint : Int) (M capP : Nat) (bP : block) (capS : Nat) (bS : block) (capB : Nat) (bB : block) :
    Satisfies xi ge (.Internal Source.dense.fn.maketargetcell)
      (maketargetcellSpec bg gofs gw grows bl lofs lab bp pofs ptn level bt tofs tvals bz zofs zvals
        bc cofs cvals tcLevel dg hint M capP bP capS bS capB bB) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧
    le = entryTemps bg gofs bl lofs bp pofs level bt tofs bz zofs bc cofs tcLevel dg hint M n ∧
    m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bg gofs bl lofs bp pofs level bt tofs bz zofs bc cofs tcLevel dg
      hint M n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hpre, hhn, hh0, htc, ⟨x, hx, hxg⟩, htarr, hzarr, hcarr, hnbit, hout⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.maketargetcell.fn_body_eq, body_eq]
    simp only [body]
    have hnlt := hpre.nlt
    have hMlt := hpre.Mlt
    have hM1 := hpre.M1
    have hnM := hpre.nM
    generalize hE : entryTemps bg gofs bl lofs bp pofs level bt tofs bz zofs bc cofs tcLevel dg hint M n = E
    have eg : PTree.get id.g E = some (.Vptr bg gofs) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have elb : PTree.get id.lab E = some (.Vptr bl lofs) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have eptn : PTree.get id.ptn E = some (.Vptr bp pofs) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have elev : PTree.get id.level E = some (.Vint (ir level)) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have etcell : PTree.get id.tcell E = some (.Vptr bt tofs) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have etsz : PTree.get id.tcellsize E = some (.Vptr bz zofs) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have ecp : PTree.get id.cellpos E = some (.Vptr bc cofs) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have etcl : PTree.get id.tc_level E = some (.Vint (ir tcLevel)) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have edg : PTree.get id.digraph E = some (.Vint dg) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have ehint : PTree.get id.hint E = some (.Vint (ir hint)) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have etc : PTree.get id.targetcell E = some (.Vptr Block.targetcell Ptrofs.zero) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have em : PTree.get id.m E = some (.Vint (ir M)) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have en : PTree.get id.n E = some (.Vint (ir n)) := by
      subst hE; simp (config := {decide := true}) only [entryTemps, temps_gss]
    -- `i = (*targetcell)(…);`
    wp_step; wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr Block.targetcell Ptrofs.zero)
      (targs := [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tint, tint, tint]) (tres := tint)
      (cc := Common.AST.cc_default) _
      (targetcellSpec bg gofs gw grows bl lofs lab bp pofs ptn level tcLevel dg hint M capP bP capS bS
        capB bB)
      (targetcell_satisfies _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) rfl
      (by simp only [Exec.evalExpr, etc, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
      (by simp only [Exec.evalExprlist, Exec.evalExpr, eg, elb, eptn, elev, etcl, edg, ehint, em, en,
        typeof, cop])
      (by simp [Common.Globalenvs.Genv.find_funct, funct_targetcell]) rfl
      ⟨rfl, hpre, hhn, hh0, htc⟩ ?_
    rintro t v m1 ⟨rfl, rfl, capP', bP', capS', bS', capB', bB', hDP, hDS, hDB, hfP, hfS, hfB, hU,
      hPS', hPB', hSB'⟩
    simp only [set_opttemp, E0_append]
    have hr := targetcell_mem ⟨grows⟩ lab ptn level tcLevel hint hpre.psize hpre.plast hhn hx hxg
    generalize hR : Hex.GraphIso.Nauty.targetcell ⟨grows⟩ lab ptn level tcLevel hint = r at hr
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    -- what the call left alone
    have oND : ∀ z, z = bt ∨ z = bz ∨ z = bc ∨ z = Block.nautilBit →
        ¬ dyn3Set m capP bP capS bS capB bB z := fun z hz =>
      have c := hout.out z hz
      not_dyn3 c.1 c.2.2.1 c.2.1 c.2.2.2.2.1 c.2.2.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.1
        c.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2
    have cND : ∀ z, z = bg ∨ z = bl ∨ z = bp → ¬ dyn3Set m capP bP capS bS capB bB z := fun z hz =>
      have c := hpre.caller z hz
      not_dyn3 c.1 c.2.2.1 c.2.1 c.2.2.2.2.1 c.2.2.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.1
        c.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.2
    have hparr1 := hpre.parr.unch hU (cND bp (.inr (.inr rfl)))
    have hlarr1 := hpre.larr.unch hU (cND bl (.inr (.inl rfl)))
    have htarr1 := htarr.unch hU (oND bt (.inl rfl))
    have hzarr1 := hzarr.unch hU (oND bz (.inr (.inl rfl)))
    have hcarr1 := hcarr.unch hU (oND bc (.inr (.inr (.inl rfl))))
    have hbit1 := hnbit.unch hU (oND _ (.inr (.inr (.inr rfl))))
    let le2 := PTree.set id.i (.Vint (ir (r : Int))) (PTree.set id.t3 (.Vint (ir (r : Int))) E)
    have g2 : ∀ x, x ≠ id.i → x ≠ id.t3 → PTree.get x le2 = PTree.get x E := fun x h1 h2 => by
      simp only [le2]; rw [temps_gso _ _ h1, temps_gso _ _ h2]
    -- `for (j = i + 1; ptn[j] > level; ++j) {}`
    wp_step
    refine wp_jloop (by rw [g2 _ (by decide) (by decide)]; exact eptn) hparr1 (by omega)
      (by rw [g2 _ (by decide) (by decide)]; exact elev) hpre.levlt hpre.psmall hpre.psize hpre.plast
      hr.1 hr.2 (temps_gss _ _ _) ?_
    intro le3 hj3 ho3
    have sp := cellEnd_spec hpre.psize (show r + 1 < n by
      rcases Nat.lt_or_ge (r + 1) n with h1 | h1
      · exact h1
      · have : r = n - 1 := by omega
        have := hpre.plast; rw [← ‹r = n - 1›] at this; omega) hpre.plast
    generalize hE3 : cellEnd ptn level (r + 1) = e at hj3 sp
    have g3 : ∀ x, x ≠ id.j → x ≠ id.i → x ≠ id.t3 → PTree.get x le3 = PTree.get x E :=
      fun x h1 h2 h3 => by rw [ho3 x h1, g2 x h2 h3]
    have hi3 : PTree.get id.i le3 = some (.Vint (ir (r : Int))) := by
      rw [ho3 _ (by decide)]; exact temps_gss _ _ _
    -- `*tcellsize = j - i + 1;`
    have hre : r + 1 ≤ e := sp.1
    obtain ⟨m2, hst2, hzarr2, -⟩ := store_array hzarr1 (show 0 < 1 by decide)
      (.Vint (ir (((e - r + 1 : Nat) : Int)))) rfl
    have hu2 : Unch m1 m2 (· = bz) := Unch.store hst2 rfl
    simp only [E0_append]
    wp_step; wp_step; wp_step
    apply wp_assign_eval
    simp only [Exec.evalLvalue, Exec.evalExpr, g3 id.tcellsize (by decide) (by decide) (by decide), etsz, hj3,
      hi3, typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev, ir_sub, ir_add]
    rw [show Ptrofs.unsigned zofs = elemOfs .Mint32 (intOfZ (Ptrofs.unsigned zofs)) 0 by
      unfold elemOfs
      rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ],
      show (e : Int) - r + 1 = ((e - r + 1 : Nat) : Int) by omega, hst2]
    have hzarr2' : ArrayAt m2 .Mint32 bz (intOfZ (Ptrofs.unsigned zofs))
        (fun _ => .Vint (ir (((e - r + 1 : Nat) : Int)))) 1 :=
      hzarr2.congr fun i hi => by simp [upd, show i = 0 by omega]
    have tz := hout.tz
    have tc := hout.tc
    have zc := hout.zc
    have st := hout.sep bt (.inl rfl)
    -- `EMPTYSET(tcell, m);`
    wp_step
    refine Set.wp_emptySet' (by decide) (by decide) (by decide) (htarr1.unch hu2 tz) hM1 (by omega)
      (by rw [g3 _ (by decide) (by decide) (by decide)]; exact etcell)
      (by rw [g3 _ (by decide) (by decide) (by decide)]; exact em) ?_
    intro le4 m3 htarr3 hu3 hout3 ho4
    have g4 : ∀ x, x ≠ id.es → x ≠ id.t4 → x ≠ id.j → x ≠ id.i → x ≠ id.t3 →
        PTree.get x le4 = PTree.get x E := fun x h1 h2 h3 h4 h5 => by rw [ho4 x h1 h2, g3 x h3 h4 h5]
    -- `for (k = i; k <= j; ++k) ADDELEMENT(tcell, lab[k]);`
    wp_step
    refine wp_kloop (by rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact elb)
      ((hlarr1.unch hu2 (hout.sep bz (.inr (.inl rfl))).2.1.symm).unch hu3 st.2.1.symm)
      hpre.lsmall (by omega) hnM (by omega) st.2.1.symm
      (by rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact etcell) htarr3
      (Set.setRep_zero hnM)
      ((hbit1.unch hu2 (hout.sep bz (.inr (.inl rfl))).2.2.2.symm).unch hu3 st.2.2.2.symm)
      st.2.2.2.symm (show r ≤ e by omega) sp.2.1 (by rw [ho4 _ (by decide) (by decide)]; exact hi3)
      (by rw [ho4 _ (by decide) (by decide)]; exact hj3) ?_
    intro le5 m4 ws4 htarr4 hW4 hu4 hout4 ho5
    -- `*cellpos = i;`
    have hcarr4 := ((hcarr1.unch hu2 zc.symm).unch hu3 tc.symm).unch hu4 tc.symm
    obtain ⟨m5, hst5, hcarr5, -⟩ := store_array hcarr4 (show 0 < 1 by decide)
      (.Vint (ir (r : Int))) rfl
    have hu5 : Unch m4 m5 (· = bc) := Unch.store hst5 rfl
    have hi5 : PTree.get id.i le5 = some (.Vint (ir (r : Int))) := by
      rw [ho5 _ (by decide), ho4 _ (by decide) (by decide)]; exact hi3
    have hcp5 : PTree.get id.cellpos le5 = some (.Vptr bc cofs) := by
      rw [ho5 _ (by decide), g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact ecp
    wp_step; wp_step
    apply wp_assign_eval
    simp only [Exec.evalLvalue, Exec.evalExpr, hcp5, hi5, typeof, cop, Exec.assignLoc,
      Cfrontend.Ctypes.access_mode, Mem.storev]
    rw [show Ptrofs.unsigned cofs = elemOfs .Mint32 (intOfZ (Ptrofs.unsigned cofs)) 0 by
      unfold elemOfs
      rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ], hst5]
    refine ⟨m5, Nextelement.free_empty _, rfl, ?_⟩
    -- the postcondition
    have hMk : Hex.GraphIso.Nauty.maketargetcell ⟨grows⟩ lab ptn level tcLevel hint =
        (r, worksetOf n lab r e, e - r + 1) := by
      simp only [Hex.GraphIso.Nauty.maketargetcell, hR, hE3]
    rw [hMk]
    have hU15 : Unch m1 m5 (fun z => z = bt ∨ z = bz ∨ z = bc) :=
      (((hu2.mono fun _ h => .inr (.inl h)).trans (hu3.mono fun _ h => .inl h)).trans
        (hu4.mono fun _ h => .inl h)).trans (hu5.mono fun _ h => .inr (.inr h))
    have nO : ∀ z, z ≠ bt → z ≠ bz → z ≠ bc → ¬ (z = bt ∨ z = bz ∨ z = bc) :=
      fun z h1 h2 h3 h => by rcases h with h | h | h <;> contradiction
    have oT := hout.out bt (.inl rfl)
    have oZ := hout.out bz (.inr (.inl rfl))
    have oC := hout.out bc (.inr (.inr (.inl rfl)))
    have nb : ∀ (b' b : block) cap cap', ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') →
        (∀ z, z = bt ∨ z = bz ∨ z = bc → 0 < cap → z ≠ b) → 0 < cap' →
        ¬ (b' = bt ∨ b' = bz ∨ b' = bc) := fun b' b cap cap' hf hz hc => by
      refine nO b' (ne_new hf oT.1 (hz bt (.inl rfl)) hc).symm
        (ne_new hf oZ.1 (hz bz (.inr (.inl rfl))) hc).symm (ne_new hf oC.1 (hz bc (.inr (.inr rfl))) hc).symm
    refine ⟨⟨ws4, (htarr4.unch hu5 tc), hW4⟩, ((hzarr2'.unch hu3 tz.symm).unch hu4 tz.symm).unch hu5 zc,
      hcarr5.congr fun i hi => by simp [upd, show i = 0 by omega], capP', bP', capS', bS', capB', bB',
      hDP.keep hU15 (nO _ (Ne.symm oT.2.1) (Ne.symm oZ.2.1) (Ne.symm oC.2.1))
        (nO _ (Ne.symm oT.2.2.1) (Ne.symm oZ.2.2.1) (Ne.symm oC.2.2.1))
        fun hc => Keep.unch hU15 (nb bP' bP capP capP' hfP (fun z hz => (hout.out z (by
          rcases hz with h | h | h <;> simp [h])).2.2.2.2.2.2.2.1) hc),
      hDS.keep hU15 (nO _ (Ne.symm oT.2.2.2.1) (Ne.symm oZ.2.2.2.1) (Ne.symm oC.2.2.2.1))
        (nO _ (Ne.symm oT.2.2.2.2.1) (Ne.symm oZ.2.2.2.2.1) (Ne.symm oC.2.2.2.2.1))
        fun hc => Keep.unch hU15 (nb bS' bS capS capS' hfS (fun z hz => (hout.out z (by
          rcases hz with h | h | h <;> simp [h])).2.2.2.2.2.2.2.2.1) hc),
      hDB.keep hU15 (nO _ (Ne.symm oT.2.2.2.2.2.1) (Ne.symm oZ.2.2.2.2.2.1) (Ne.symm oC.2.2.2.2.2.1))
        (nO _ (Ne.symm oT.2.2.2.2.2.2.1) (Ne.symm oZ.2.2.2.2.2.2.1) (Ne.symm oC.2.2.2.2.2.2.1))
        fun hc => Keep.unch hU15 (nb bB' bB capB capB' hfB (fun z hz => (hout.out z (by
          rcases hz with h | h | h <;> simp [h])).2.2.2.2.2.2.2.2.2) hc),
      hfP, hfS, hfB, (hU.mono fun _ h => .inl h).trans (hU15.mono fun _ h => .inr h), hPS', hPB',
      hSB'⟩

end NautyVerified.Proofs.Maketargetcell

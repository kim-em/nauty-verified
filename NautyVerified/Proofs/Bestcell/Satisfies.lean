import NautyVerified.Proofs.Bestcell.Spec
import NautyVerified.Proofs.Bestcell.Rows
import NautyVerified.Proofs.Bestcell.Clear
import NautyVerified.Proofs.Bestcell.Argmax

/-!
# `bestcell` meets its specification
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Spec.Bestcell
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Alloc (DynAt Keep dyn3Set ne_new)
open NautyVerified.Proofs.Updatecan (tv)
open Hex.GraphIso.Nauty (VSet cells)

def entryTemps (bg : block) (gofs : ptrofs) (bl : block) (lofs : ptrofs) (bp : block)
    (pofs : ptrofs) (level tcLevel M n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.tc_level (.Vint (ir tcLevel)) (PTree.set id.level (.Vint (ir level))
      (PTree.set id.ptn (.Vptr bp pofs) (PTree.set id.lab (.Vptr bl lofs)
        (PTree.set id.g (.Vptr bg gofs)
          (create_undef_temps Source.dense.fn.«naugraph:bestcell».fn_temps)))))))

theorem valid_of_load {m : mem} {chunk : memory_chunk} {b : block} {ofs : Z} {v : val}
    (h : Mem.load chunk m b ofs = some v) : Mem.valid_block m b :=
  Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h)

/-- A block of the old memory outside everything the prologue touches. -/
theorem not_dyn3 {m : mem} {capP capS capB : Nat} {bP bS bB z : block} (hv : Mem.valid_block m z)
    (h1 : z ≠ WPS) (h2 : z ≠ WP) (h3 : z ≠ WSS) (h4 : z ≠ WS) (h5 : z ≠ BKS) (h6 : z ≠ BK)
    (h7 : 0 < capP → z ≠ bP) (h8 : 0 < capS → z ≠ bS) (h9 : 0 < capB → z ≠ bB) :
    ¬ dyn3Set m capP bP capS bS capB bB z := by
  rintro (h | h | h | h | h | h | ⟨hc, h⟩ | ⟨hc, h⟩ | ⟨hc, h⟩ | h)
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h
  · exact h5 h
  · exact h6 h
  · exact h7 hc h
  · exact h8 hc h
  · exact h9 hc h
  · exact h hv

theorem bestcell_satisfies {xi : ExternalCalls} {n : Nat} (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (grows : Array (VSet n)) (bl : block) (lofs : ptrofs)
    (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat) (level tcLevel M capP : Nat)
    (bP : block) (capS : Nat) (bS : block) (capB : Nat) (bB : block) :
    Satisfies xi ge (.Internal Source.dense.fn.«naugraph:bestcell»)
      (bestcellSpec bg gofs gw grows bl lofs lab bp pofs ptn level tcLevel M capP bP capS bS capB bB) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bg gofs bl lofs bp pofs level tcLevel M n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bg gofs bl lofs bp pofs level tcLevel M n, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hpre⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.«naugraph:bestcell».fn_body_eq, body_eq]
    simp only [body]
    have hn0 := hpre.n0
    have hnlt := hpre.nlt
    have hMlt := hpre.Mlt
    have hM1 := hpre.M1
    have hnM := hpre.nM
    have cG := hpre.caller bg (.inl rfl)
    have cL := hpre.caller bl (.inr (.inl rfl))
    have cP := hpre.caller bp (.inr (.inr rfl))
    have hvWP := Alloc.valid_of_access hpre.dP.bpW
    have hvWPS := Alloc.valid_of_access hpre.dP.bsW
    have hvWS := Alloc.valid_of_access hpre.dS.bpW
    have hvWSS := Alloc.valid_of_access hpre.dS.bsW
    have hvBK := Alloc.valid_of_access hpre.dB.bpW
    have hvBKS := Alloc.valid_of_access hpre.dB.bsW
    have hvBIT : Mem.valid_block m BIT := valid_of_load (hpre.bit 0 (by decide))
    refine Alloc.wp_dyn3 (xn := id.n) (xm := id.m) (n := n) (M := M) hpre.dP hpre.dS hpre.dB
      (by simp (config := {decide := true}) only [entryTemps, temps_gss])
      (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (by omega) (by omega) (by decide) (by decide)
      (fun hc => have h := hpre.sP hc; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩)
      (fun hc => have h := hpre.sS hc; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩)
      (fun hc => have h := hpre.sB hc; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) ?_
    intro le1 m1 capP' bP' capS' bS' capB' bB' hDP hDS hDB hcP hcS hcB hfP hfS hfB hgrow ho1 hU
      hPS hPB hSB
    have hcP0 : 0 < capP' := by omega
    have hcS0 : 0 < capS' := by omega
    have hcB0 : 0 < capB' := by omega
    have nP : ∀ z, Mem.valid_block m z → (0 < capP → z ≠ bP) → z ≠ bP' :=
      fun z hv hz => ne_new hfP hv hz hcP0
    have nS : ∀ z, Mem.valid_block m z → (0 < capS → z ≠ bS) → z ≠ bS' :=
      fun z hv hz => ne_new hfS hv hz hcS0
    have nB : ∀ z, Mem.valid_block m z → (0 < capB → z ≠ bB) → z ≠ bB' :=
      fun z hv hz => ne_new hfB hv hz hcB0
    have cND : ∀ z, z = bg ∨ z = bl ∨ z = bp → ¬ dyn3Set m capP bP capS bS capB bB z := fun z hz =>
      have c := hpre.caller z hz
      not_dyn3 c.1 c.2.2.1 c.2.1 c.2.2.2.2.1 c.2.2.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.1
        c.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2.2
    have bND : ¬ dyn3Set m capP bP capS bS capB bB BIT :=
      not_dyn3 hvBIT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun hc h => (hpre.sP hc).2.2.2.2.1 h.symm) (fun hc h => (hpre.sS hc).2.2.2.2.1 h.symm)
        (fun hc h => (hpre.sB hc).2.2.2.2 h.symm)
    have cNe : ∀ z, z = bg ∨ z = bl ∨ z = bp → z ≠ bP' ∧ z ≠ bS' ∧ z ≠ bB' := fun z hz =>
      have c := hpre.caller z hz
      ⟨nP z c.1 c.2.2.2.2.2.2.2.2.1, nS z c.1 c.2.2.2.2.2.2.2.2.2.1, nB z c.1 c.2.2.2.2.2.2.2.2.2.2⟩
    -- the globals and the new blocks
    have gP : bP' ≠ WP ∧ bP' ≠ WPS ∧ bP' ≠ WS ∧ bP' ≠ WSS ∧ bP' ≠ BK ∧ bP' ≠ BKS ∧ bP' ≠ BIT :=
      ⟨(hDP.bne hcP0).2, (hDP.bne hcP0).1,
        (nP WS hvWS fun hc h => (hpre.sP hc).1 h.symm).symm,
        (nP WSS hvWSS fun hc h => (hpre.sP hc).2.1 h.symm).symm,
        (nP BK hvBK fun hc h => (hpre.sP hc).2.2.1 h.symm).symm,
        (nP BKS hvBKS fun hc h => (hpre.sP hc).2.2.2.1 h.symm).symm,
        (nP BIT hvBIT fun hc h => (hpre.sP hc).2.2.2.2.1 h.symm).symm⟩
    have gS : bS' ≠ WP ∧ bS' ≠ WPS ∧ bS' ≠ WS ∧ bS' ≠ WSS ∧ bS' ≠ BK ∧ bS' ≠ BKS ∧ bS' ≠ BIT :=
      ⟨(nS WP hvWP fun hc h => (hpre.sS hc).1 h.symm).symm,
        (nS WPS hvWPS fun hc h => (hpre.sS hc).2.1 h.symm).symm,
        (hDS.bne hcS0).2, (hDS.bne hcS0).1,
        (nS BK hvBK fun hc h => (hpre.sS hc).2.2.1 h.symm).symm,
        (nS BKS hvBKS fun hc h => (hpre.sS hc).2.2.2.1 h.symm).symm,
        (nS BIT hvBIT fun hc h => (hpre.sS hc).2.2.2.2.1 h.symm).symm⟩
    have gB : bB' ≠ WP ∧ bB' ≠ WPS ∧ bB' ≠ WS ∧ bB' ≠ WSS ∧ bB' ≠ BK ∧ bB' ≠ BKS ∧ bB' ≠ BIT :=
      ⟨(nB WP hvWP fun hc h => (hpre.sB hc).1 h.symm).symm,
        (nB WPS hvWPS fun hc h => (hpre.sB hc).2.1 h.symm).symm,
        (nB WS hvWS fun hc h => (hpre.sB hc).2.2.1 h.symm).symm,
        (nB WSS hvWSS fun hc h => (hpre.sB hc).2.2.2.1 h.symm).symm,
        (hDB.bne hcB0).2, (hDB.bne hcB0).1,
        (nB BIT hvBIT fun hc h => (hpre.sB hc).2.2.2.2 h.symm).symm⟩
    have hT1 : ∀ k, Args k ∨ k = id.nnt ∨ k = id.i →
        PTree.get k le1 = PTree.get k (entryTemps bg gofs bl lofs bp pofs level tcLevel M n) :=
      fun k hk => ho1 k (by rcases hk with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide)
        (by rcases hk with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide)
        (by rcases hk with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide)
        (by rcases hk with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide)
        (by rcases hk with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide)
        (by rcases hk with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide)
    have hf : Frame m1 le1 bg gofs gw grows bl lofs lab bp pofs ptn level M bP' bS' bB' :=
      { hg := by rw [hT1 _ (.inl (.inl rfl))]
                 simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hlab := by rw [hT1 _ (.inl (.inr (.inl rfl)))]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hptn := by rw [hT1 _ (.inl (.inr (.inr (.inl rfl))))]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hlev := by rw [hT1 _ (.inl (.inr (.inr (.inr (.inl rfl)))))]
                   simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hm := by rw [hT1 _ (.inl (.inr (.inr (.inr (.inr (.inl rfl))))))]
                 simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
        hn := by rw [hT1 _ (.inl (.inr (.inr (.inr (.inr (.inr rfl))))))]
                 simp (config := {decide := true}) only [entryTemps, temps_gss]
        graph := ⟨hpre.graph.arr.unch hU (cND bg (.inl rfl)), hpre.graph.rep⟩
        larr := hpre.larr.unch hU (cND bl (.inr (.inl rfl)))
        lsmall := hpre.lsmall
        parr := hpre.parr.unch hU (cND bp (.inr (.inr rfl)))
        psize := hpre.psize, psmall := hpre.psmall, plast := hpre.plast, levlt := hpre.levlt
        wpP := hDP.ptr hcP0, wsP := hDS.ptr hcS0, bkP := hDB.ptr hcB0
        bit := hpre.bit.unch hU bND
        dPS := hPS hcP0 hcS0, dPB := hPB hcP0 hcB0, dSB := hSB hcS0 hcB0
        owned := by
          rintro z (rfl | rfl | rfl)
          · exact ⟨(cNe bg (.inl rfl)).1.symm, (cNe bl (.inr (.inl rfl))).1.symm,
              (cNe bp (.inr (.inr rfl))).1.symm, gP.1, gP.2.2.1, gP.2.2.2.2.1, gP.2.2.2.2.2.2⟩
          · exact ⟨(cNe bg (.inl rfl)).2.1.symm, (cNe bl (.inr (.inl rfl))).2.1.symm,
              (cNe bp (.inr (.inr rfl))).2.1.symm, gS.1, gS.2.2.1, gS.2.2.2.2.1, gS.2.2.2.2.2.2⟩
          · exact ⟨(cNe bg (.inl rfl)).2.2.symm, (cNe bl (.inr (.inl rfl))).2.2.symm,
              (cNe bp (.inr (.inr rfl))).2.2.symm, gB.1, gB.2.2.1, gB.2.2.2.2.1, gB.2.2.2.2.2.2⟩
        n0 := hn0, nlt := hnlt, M1 := hM1, Mlt := hMlt, nM := hnM }
    obtain ⟨wv, hw⟩ := Alloc.malloced_array (hDP.mal hcP0) .Mint32 4 rfl rfl n
      (Nat.mul_le_mul_left 4 hcP)
    obtain ⟨wsv, hws⟩ := Alloc.malloced_array (hDS.mal hcS0) .Mint64 8 rfl rfl M
      (Nat.mul_le_mul_left 8 hcS)
    obtain ⟨bv, hb⟩ := Alloc.malloced_array (hDB.mal hcB0) .Mint32 4 rfl rfl (n + 2)
      (Nat.mul_le_mul_left 4 hcB)
    -- the blocks the body changes lie in what the specification allows
    have memD : ∀ z, z = bP' ∨ z = bS' ∨ z = bB' → dyn3Set m capP bP capS bS capB bB z := by
      rintro z (rfl | rfl | rfl)
      · rcases hfP with ⟨hc, rfl⟩ | hnv
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, rfl⟩))))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hnv))))))))
      · rcases hfS with ⟨hc, rfl⟩ | hnv
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, rfl⟩)))))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hnv))))))))
      · rcases hfB with ⟨hc, rfl⟩ | hnv
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, rfl⟩))))))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hnv))))))))
    have post : ∀ mF, Mod m1 mF bP' bS' bB' →
        Post m mF capP bP capS bS capB bB := fun mF hmod => by
      have nd : ∀ z, z ≠ bP' → z ≠ bS' → z ≠ bB' → ¬ (z = bP' ∨ z = bS' ∨ z = bB') :=
        fun z h1 h2 h3 h => by rcases h with h | h | h <;> contradiction
      exact ⟨capP', bP', capS', bS', capB', bB',
        hDP.keep hmod.1 (nd _ gP.1.symm gS.1.symm gB.1.symm) (nd _ gP.2.1.symm gS.2.1.symm gB.2.1.symm)
          fun _ => hmod.2.1,
        hDS.keep hmod.1 (nd _ gP.2.2.1.symm gS.2.2.1.symm gB.2.2.1.symm)
          (nd _ gP.2.2.2.1.symm gS.2.2.2.1.symm gB.2.2.2.1.symm) fun _ => hmod.2.2.1,
        hDB.keep hmod.1 (nd _ gP.2.2.2.2.1.symm gS.2.2.2.2.1.symm gB.2.2.2.2.1.symm)
          (nd _ gP.2.2.2.2.2.1.symm gS.2.2.2.2.2.1.symm gB.2.2.2.2.2.1.symm) fun _ => hmod.2.2.2,
        hfP, hfS, hfB, hU.trans (hmod.1.mono memD), hPS, hPB, hSB⟩
    -- `i = nnt = 0;`
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gso _ _ (show id.t9 ≠ id.nnt by decide), temps_gss, E0_append]
    let le2 := PTree.set id.i (.Vint (ir 0)) (PTree.set id.nnt (.Vint (ir 0))
      (PTree.set id.t9 (.Vint (ir 0)) le1))
    show Wp xi ge _ _ _ empty_env le2 m1
    have hf2 := hf.temps (le' := le2) fun x hx => by
      simp only [le2]
      rw [temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    -- the starts of the nontrivial cells
    wp_step
    refine wp_starts hf2 hw (temps_gss _ _ _) (by simp only [le2]; rw [temps_gso _ _ (by decide),
      temps_gss]) ?_
    intro le3 m3 wv3 hw3 hwS hnnt3 hu3 hk3 ho3 hSlen
    generalize hSd : starts' ptn level n = S at hwS hnnt3 hSlen
    have hSn : ∀ k < S.length, S[k]! < n := fun k hk => by
      subst hSd
      rw [getElem!_pos _ k hk]
      exact (mem_starts hpre.psize hpre.plast _ _ _ (List.getElem_mem hk)).2.1
    have hf3 := (hf2.unch (m' := m3) (hu3.mono fun _ hz => .inl hz)).temps ho3
    have hmod3 : Mod m1 m3 bP' bS' bB' := hf.modP hu3 hk3
    -- `if (nnt == 0) return n;`
    simp only [E0_append]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hnnt3, typeof, cop]
    rw [ir_eq (a := (S.length : Int)) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    by_cases hS0 : S.length = 0
    · rw [ite_eq_left (by simp [hS0])]
      wp_step; wp_step
      apply wp_return_some_eval
      simp only [Exec.evalExpr, hf3.hn, typeof, cop, Source.dense.fn.«naugraph:bestcell».fn_return_eq,
        Nextelement.free_empty]
      exact ⟨rfl, by rw [bestcell_nil _ _ _ _ (by rw [← hSd] at hS0; exact hS0)], post m3 hmod3⟩
    · rw [ite_eq_right (by simp only [decide_eq_true_eq]; omega)]
      apply wp_skip
      have hS1 : 1 ≤ S.length := by omega
      -- clear `bucket`
      have hb3 := hb.unch hu3 hf.dPB.symm
      wp_step
      refine wp_clear hf3.bkP hb3 (by omega) (K := S.length) (by omega) gB.2.2.2.2.1.symm hnnt3 ?_
      intro le4 m4 bv4 hb4 hbv4 hu4 hk4 ho4
      have hf4 := (hf3.unch (m' := m4) (hu4.mono fun _ hz => .inr (.inr hz))).temps (le' := le4)
        fun x hx => ho4 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      have hmod4 : Mod m1 m4 bP' bS' bB' := hmod3.trans (hf3.modB hu4 hk4)
      have hnnt4 : PTree.get id.nnt le4 = some (.Vint (ir (S.length : Int))) := by
        rw [ho4 _ (by decide) (by decide)]; exact hnnt3
      -- the joined-cell counts
      wp_step
      refine wp_rows hf4 ((hw3.unch hu4 hf.dPB)) hwS hSn ((hws.unch hu3 hf.dPS.symm).unch hu4 hf.dSB)
        hb4 hbv4 hSlen hS1 hnnt4 ?_
      intro le5 m5 bv5 hb5 hbv5 hu5 hk5S hk5B ho5
      have hf5 := (hf4.unch (m' := m5) (hu5.mono fun _ hz => .inr hz)).temps (le' := le5)
        fun x hx => ho5 x (by
          unfold RowT PairT; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
          (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      have hmod5 : Mod m1 m5 bP' bS' bB' := hmod4.trans
        ⟨hu5.mono fun _ hz => .inr hz,
          Keep.unch hu5 (by rintro (h | h); exact hf.dPS h; exact hf.dPB h), hk5S, hk5B⟩
      have hnnt5 : PTree.get id.nnt le5 = some (.Vint (ir (S.length : Int))) := by
        rw [ho5 _ (by unfold RowT PairT; decide) (by decide)]; exact hnnt4
      -- the argmax
      simp only [E0_append]
      have hbnd := rows_bound (n := n) ⟨grows⟩ lab ptn level S.toArray S.length S.length hS1
      refine wp_argmax hf5 ((hw3.unch hu4 hf.dPB).unch hu5 (by
          rintro (h | h); exact hf.dPS h; exact hf.dPB h)) hwS hSlen hS1 hb5 hbv5
        (fun x => by have := hbnd x; split at this <;> omega) hnnt5 ?_
      refine ⟨rfl, ?_, post m5 hmod5⟩
      have hS0' : (startsOf (cells.go ptn level n (n - 0) 0)).length ≠ 0 := by
        rw [← hSd] at hS0; exact hS0
      rw [bestcell_eq _ _ _ _ hS0']
      rw [show startsOf (cells.go ptn level n (n - 0) 0) = S from hSd]

end NautyVerified.Proofs.Bestcell

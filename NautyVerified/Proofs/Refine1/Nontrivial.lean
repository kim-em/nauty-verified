import NautyVerified.Proofs.Refine.NontrivialN
import NautyVerified.Proofs.Refine1.Satisfies

/-!
# `refine1`'s pass for a nontrivial splitting cell

`refine1` keeps the splitter set in the one-word temporary `workset0`
(`SpOne`). `cnt1_ok`: its per-member count is a `CountHead`. With those and
dialect `D1`, `refine`'s generic lemmas give the pass: `wp_nontrivial1`, which
is `NontrivialPass1`, and with it `refineFn_refine1'`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs NautyVerified.Proofs.Alloc
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

/-- `refine1`'s splitter set: the word in `workset0`. -/
def SpOne {n : Nat} (ws : VSet n) (le : temp_env) (_m : mem) : Prop :=
  ∃ w, PTree.get dense.id.workset0 le = some (.Vlong w) ∧ SetRep (fun _ => bv64 w) 1 ws

theorem SpOne.ok {n : Nat} {ws : VSet n} {L : Loc} {T : List Common.AST.ident}
    (hT : dense.id.workset0 ∉ T) : SpOk (SpOne ws) L T where
  unch := fun hs _ _ => hs
  temps := fun ⟨w, hw, hr⟩ ho => ⟨w, by rw [ho _ hT]; exact hw, hr⟩

/-- `refine1`'s per-member count. -/
theorem cnt1_ok {f : function} {t : Common.AST.ident} (htx : t ≠ dense.id.x) {n : Nat} {L : Loc}
    (hL : L.M = 1) {ctx : Ctx n} {ws : VSet n} :
    CountHead xi f (fun rest => .Ssequence (Refine1.cnt1 t) rest) [t] L ctx ws (SpOne ws) := by
  intro Q le m rest st i ⟨w, hw, hrep⟩ hf ht hi hin hQ
  have hg := hf.graph
  rw [hL] at hg
  have hn := hf.ok.nlt
  wp_step
  refine Refine1.wp_cnt1 htx hw hrep hg ht.g hf.larr ht.lab hin (hf.labs i hin) hi (by omega)
    hf.bytes ?_
  intro le' hc ho
  simp only [E0_append]
  refine hQ le' hc fun z hz => ho z (fun h => hz (h ▸ by simp)) (fun h => hz (h ▸ by simp))
    (fun h => hz (h ▸ by simp))

/-- `refine1`'s pass for a nontrivial splitting cell is HexGraphIso's `refineNontrivial`. -/
theorem wp_nontrivial1 : NontrivialPass1 xi := by
  intro n L ctx hok hL Q le m st aw split1 split2 hm ht hi hnc hs1 hs2 h12 hse h2n hQ
  have d := hok.wd
  have hn := hok.nlt
  have hnM := hok.nM
  have hso := hi.ok
  have hlabs : ∀ i < n, st.lab[i]! < n := fun i hi' => hso.labOk i (by rw [hso.labSize]; exact hi')
  rw [Refine1.nontrivial_fill]
  refine Refine1.wp_fill1 hm.lab ht.lab hlabs (by rw [hL] at hnM; omega) (by omega) h2n hs1 hs2
    hm.bit ?_
  intro le2 w hw hr g2
  have ht2 : Tmp le2 L st := ht.of (g2 _ (by decide) (by decide)) (g2 _ (by decide) (by decide))
    (g2 _ (by decide) (by decide)) (g2 _ (by decide) (by decide)) (g2 _ (by decide) (by decide))
    (g2 _ (by decide) (by decide)) (g2 _ (by decide) (by decide)) (g2 _ (by decide) (by decide))
    (g2 _ (by decide) (by decide)) (g2 _ (by decide) (by decide)) (g2 _ (by decide) (by decide))
    (g2 _ (by decide) (by decide)) (g2 _ (by decide) (by decide))
  -- MASH(longcode, split2 - split1 + 1)
  wp_step; wp_step; wp_step
  refine wp_mash ht2.longcode hi.code (i := split2 - split1 + 1) ?_ rfl (by omega) ?_
  · simp only [Exec.evalExpr, typeof, cop]
    rw [g2 _ (by decide) (by decide), g2 _ (by decide) (by decide), hs1, hs2]
    simp only [cop, ir_sub, ir_add]
    congr 3; omega
  let st1 : RefineSt n := { st with longcode := Hex.GraphIso.Nauty.mash st.longcode (split2 - split1 + 1) }
  have ht3 := ht2.setCode (Hex.GraphIso.Nauty.mash st.longcode (split2 - split1 + 1))
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  have hR : refineNontrivial ctx L.level split1 split2 st =
      refineNontrivialFast.go ctx L.level (worksetOf n st.lab split1 split2) st1.ptn n 0 st1 := by
    rw [refineNontrivial_eq_fast]; rfl
  have hCP : CellPass xi Source.dense.fn.refine1 Refine1.cellN
      (cellTempsG (idOf 718) (idOf 720) (idOf 721) [idOf 719] [idOf 715] (idOf 716) (idOf 717)
        (idOf 722)) L ctx (worksetOf n st.lab split1 split2) (SpOne (worksetOf n st.lab split1 split2)) :=
    fun hSp hf hm ht hso hb0 h12 h2n hcl1 hcl2 hbkt hwp hQ =>
      wp_cellN (by decide) D1_sem (cnt1_ok (by decide) hL) (cnt1_ok (by decide) hL) hSp
        (SpOne.ok (by decide)) hL hf hm ht hso hb0 h12 h2n hcl1 hcl2 hbkt hwp hQ
  refine wp_cellLoopN (by decide) hCP (SpOne.ok (by decide)) (st0 := st1) (stc := st1)
    (R := refineNontrivial ctx L.level split1 split2 st)
    hok ⟨hso.labSize, hso.labOk, hso.ptnSize, hso.ptnEnd⟩
    { mem := ⟨aw, hm.congr rfl rfl rfl rfl⟩
      unch := Unch.refl _ _
      tmp := ht3.set _ (by decide)
      sp := ⟨w, by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hw, hr⟩
      pn := Nat.zero_le _
      fuel := ⟨n, by omega, hR⟩
      agree := fun _ _ _ => rfl
      ok := ⟨hso.labSize, hso.labOk, hso.ptnSize, hso.ptnEnd⟩
      small := hi.ptnSmall
      nc := Nat.le_add_right _ _
      hint := hi.hint
      maxpos := hi.maxpos
      code := by have := mash_lt st.longcode (split2 - split1 + 1); exact Nat.lt_trans this (by decide) }
    (by rw [temps_gss]; rfl) ?_
  intro le' m' hP
  obtain ⟨aw', hm'⟩ := hP.mem
  refine hQ le' m' ⟨aw', hm', hP.tmp,
    { ok := hP.ok, ptnSmall := hP.small,
      ncSmall := by have := hP.nc; have h2 : st1.numcells = st.numcells := rfl; omega,
      hint := hP.hint, maxpos := hP.maxpos, code := hP.code }⟩ ?_
  refine hP.unch.mono fun z hz => ?_
  rcases hz with h | h | h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))

/-- `refine1` is a refinement procedure for one-word sets. -/
theorem refineFn_refine1' : RefineFn xi 1 (.Vptr Block.refine1 Ptrofs.zero) :=
  refineFn_refine1 wp_nontrivial1

/-- `refine` is a refinement procedure for any number of words per set. -/
theorem refineFn_refine' (M : Nat) : RefineFn xi M (.Vptr Block.refine Ptrofs.zero) :=
  refineFn_refine wp_trivial wp_nontrivial M

end NautyVerified.Proofs.Refine

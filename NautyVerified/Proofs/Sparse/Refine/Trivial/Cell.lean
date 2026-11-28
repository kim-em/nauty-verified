import NautyVerified.Proofs.Sparse.Refine.Trivial.Fix

/-!
# One touched cell of the singleton splitter

`wp_cell`: the body of `cellLoopT` (after its test `i < hitcells`) on the
touched cell `first = HITCELL[i]` computes `cellT`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {s : RefineSt n} {S : Scr}

theorem revAt_lab (v2 : Nat) (hit lab starts : Array Nat) (hn : 0 < n) (hl : ∀ i < n, lab[i]! < n)
    (hh : ∀ i < hit.size, hit[i]! < n) : ∀ q, ∀ i < n, (revAt v2 hit lab starts q).1[i]! < n
  | 0 => hl
  | q + 1 => by
    intro i hi
    rw [revAt_succ]
    simp only [revStep]
    by_cases he : i = (revAt v2 hit lab starts q).2.2
    · subst he
      by_cases hs : (revAt v2 hit lab starts q).2.2 < (revAt v2 hit lab starts q).1.size
      · rw [Array.getElem!_set!_self _ _ _ hs]
        by_cases hq : hit.size - 1 - q < hit.size
        · exact hh _ hq
        · rw [getElem!_neg hit _ hq]; exact hn
      · rw [show (revAt v2 hit lab starts q).1.set! _ _ = (revAt v2 hit lab starts q).1 by
          simp [Array.set!, Array.setIfInBounds, hs]]
        exact revAt_lab v2 hit lab starts hn hl hh q _ hi
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]; exact revAt_lab v2 hit lab starts hn hl hh q i hi

theorem partAt_ge (vm : Array Nat) (stamp first : Nat) (lab : Array Nat) :
    ∀ q, first ≤ (partAt vm stamp first lab q).2.1
  | 0 => Nat.le_refl _
  | q + 1 => by
    rw [partAt_succ]; unfold partStep; split
    · exact partAt_ge vm stamp first lab q
    · have := partAt_ge vm stamp first lab q; simp only; omega

/-- The body of `cellLoopT` after its test. -/
abbrev cellBody : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk (.Sset (idOf 738) (.Ecast (gix id.«nausparse:work4» (tv id.«i»)) tint)))
            (.Sset id.«v2» (tv (idOf 738))))
          (.Sset (idOf 739) (.Ecast (tv (idOf 738)) tint)))
        (.Sset id.«v1» (tv (idOf 739))))
      (.Sset id.«j» (tv (idOf 739))))
    (.Ssequence (sk (mash (tv id.«v2»)))
      (.Ssequence (sk (.Sset id.«k» (ci 0 tint)))
        (.Ssequence partLoopT
          (.Ssequence (sk (mash (tv id.«k»)))
            (.Ssequence (sk (.Sset id.«v3» (tv id.«v2»)))
              (.Ssequence revLoopT fixStmt))))))

/-- The temporaries a touched cell assigns besides `longcode` and `nactive`. -/
abbrev cellTempsT : List ident :=
  partTemps ++ revTemps ++ fixTemps ++ [id.«v1», idOf 738, idOf 739]

theorem wp_cell {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G s S)
    (hr : Rep L s S) (ht : Tmp le L s) {stamp first i : Nat}
    (hmk : ∀ v < n, (S.mk2 v = S.st2 ↔ s.vmarks[v]! = stamp))
    (hi : PTree.get id.«i» le = some (.Vint (ir i))) (hic : i < L.c4)
    (hw4 : S.w4 i = .Vint (ir first))
    (hc : IsCell s.ptn L.level first (s.cellend[first]! + 1 - first)) (hf : first < s.cellend[first]!)
    (hb : s.cellend[first]! < n) (hls : s.lab.size = n) (hlb : ∀ i < n, s.lab[i]! < n)
    (hss : s.cellstart.size = n) (hps : s.ptn.size = n) (hcode : s.longcode < 2 ^ 62)
    (hq : (cellT L.level stamp first s).queue.size ≤ n)
    (hnc : (cellT L.level stamp first s).numcells < 2147483648)
    (hQ : ∀ le' m' S', Mem m' L G (cellT L.level stamp first s) S' →
      Rep L (cellT L.level stamp first s) S' → Tmp le' L (cellT L.level stamp first s) →
      S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 → S'.st2 = S.st2 → S'.mk2 = S.mk2 →
      Frame L m m' →
      (∀ x, x ∉ cellTempsT → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F cellBody Q empty_env le m := by
  have hnl := hok.nlt
  have hn0 := hok.n0
  have hfn : first < n := by omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_skip
  simp only [E0_append]
  apply wp_set_eval
  rw [Exec.evalExpr, eval_gw4 hok hm (eval_tv hi) rfl hic, hw4]
  simp only [typeof, cop]
  apply wp_set_eval
  rw [eval_tv (temps_gss _ _ _)]
  dsimp only
  apply wp_set_eval
  rw [Exec.evalExpr, eval_tv (by rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _)]
  simp only [typeof, cop]
  apply wp_set_eval
  rw [eval_tv (temps_gss _ _ _)]
  dsimp only
  apply wp_set_eval
  rw [eval_tv (by rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _)]
  dsimp only
  simp only [E0_append]
  generalize hle0 : PTree.set id.«j» (.Vint (ir first)) (PTree.set id.«v1» (.Vint (ir first))
    (PTree.set (idOf 739) (.Vint (ir first)) (PTree.set id.«v2» (.Vint (ir first))
      (PTree.set (idOf 738) (.Vint (ir first)) le)))) = le0
  have ho0 : ∀ x, x ∉ [id.«j», id.«v1», idOf 739, id.«v2», idOf 738] → PTree.get x le0 = PTree.get x le := by
    intro x hx; rw [← hle0]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.1, temps_gso _ _ hx.2.2.1, temps_gso _ _ hx.2.2.2.1,
      temps_gso _ _ hx.2.2.2.2]
  have ht0 : Tmp le0 L s := ht.frame ho0 (by decide)
  have hv1 : PTree.get id.«v1» le0 = some (.Vint (ir first)) := by
    rw [← hle0, temps_gso _ _ (by decide), temps_gss]
  have hv2 : PTree.get id.«v2» le0 = some (.Vint (ir first)) := by
    rw [← hle0, temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]
  have hj : PTree.get id.«j» le0 = some (.Vint (ir first)) := by rw [← hle0, temps_gss]
  wp_step; wp_step; wp_step
  refine wp_mash ht0.longcode hcode (eval_tv hv2) rfl (by omega) ?_
  have ht1 := ht0.hash first
  simp only [E0_append]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  simp only [E0_append]
  wp_step
  let len := s.cellend[first]! + 1 - first
  have hlen : first + len ≤ n := by omega
  let le1 := PTree.set id.«k» (.Vint (ir 0))
    (PTree.set id.longcode (.Vlong (lr (Hex.GraphIso.Nauty.mash s.longcode first : Nat))) le0)
  have ht1' : Tmp le1 L (s.hash first) := ht1.set _ (by decide)
  refine wp_partLoop (t := s.hash first) (le := le1) (first := first) (len := len) hok
    (hm.congr rfl rfl rfl rfl) ⟨hr.starts, hr.queue, hr.w3size, hr.w3small, hr.ptnSmall⟩ ht1' hc hlen
    hls hlb hmk (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj)
    (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hv2) (temps_gss _ _ _) ?_
  intro le2 m2 w hm2 hr2 hw hf2 hj2 hv22 hk2 ho2
  have hpi := partAt_inv s.vmarks stamp first (s.hash first).lab hls hlb len hlen
  generalize hp : partAt s.vmarks stamp first (s.hash first).lab len = p at hm2 hr2 hw hv22 hk2 hpi
  obtain ⟨i1, i2, i3, i4, i5⟩ := hpi
  have ht2 : Tmp le2 L { s.hash first with lab := p.1 } :=
    ((ht1'.frame ho2 (by decide)).congr rfl rfl)
  simp only [E0_append]
  wp_step; wp_step; wp_step
  refine wp_mash ht2.longcode (show Hex.GraphIso.Nauty.mash s.longcode first < 2 ^ 62 by
    have := Refine.mash_lt s.longcode first; omega) (eval_tv hk2) rfl
    (by omega) ?_
  have ht3 := ht2.hash p.2.2.size
  simp only [E0_append]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tv (by rw [temps_gso _ _ (by decide)]; exact hv22)]
  dsimp only
  simp only [E0_append]
  wp_step
  let u : RefineSt n := ({ s.hash first with lab := p.1 } : RefineSt n).hash p.2.2.size
  let le3 := PTree.set id.«v3» (.Vint (ir p.2.1))
    (PTree.set id.longcode (.Vlong (lr (Hex.GraphIso.Nauty.mash
      (Hex.GraphIso.Nauty.mash s.longcode first) p.2.2.size : Nat))) le2)
  have ht4 : Tmp le3 L u := ht3.set _ (by decide)
  refine wp_revLoop (u := u) (le := le3) (v2 := p.2.1) (hit := p.2.2) hok (hm2.congr rfl rfl rfl rfl)
    ⟨hr2.starts, hr2.queue, hr2.w3size, hr2.w3small, hr2.ptnSmall⟩ ht4 hw i4 (by omega) i1 hss
    (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hk2)
    (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hv22) (temps_gss _ _ _) ?_
  intro le4 m4 w1 hm4 hr4 hf4 hv34 ho4
  have hge : first ≤ p.2.1 := by rw [← hp]; exact partAt_ge _ _ _ _ _
  have hp' : partAt s.vmarks stamp first s.lab (s.cellend[first]! + 1 - first) = p := hp
  have hmid : midSt stamp first s = revSt p.2.1 p.2.2 u p.2.2.size := by
    simp only [midSt, revSt, hp']; rfl
  have hfix := cellT_fix L.level stamp first s
  have hv3e : (revAt p.2.1 p.2.2 p.1 s.cellstart p.2.2.size).2.2 = p.2.1 + p.2.2.size :=
    (revAt_inv p.2.1 p.2.2 p.1 s.cellstart i1 hss p.2.2.size).2.2
  rw [hp', hv3e, hmid] at hfix
  rw [hfix] at hq hnc hQ
  have hri := revAt_inv p.2.1 p.2.2 p.1 s.cellstart i1 hss p.2.2.size
  have hv14 : PTree.get id.«v1» le4 = some (.Vint (ir first)) := by
    rw [ho4 _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide), ho2 _ (by decide),
      temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hv1
  have hv24 : PTree.get id.«v2» le4 = some (.Vint (ir p.2.1)) := by
    rw [ho4 _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hv22
  refine wp_fix hok hm4 hr4 ((ht4.frame ho4 (by decide)).congr rfl rfl) hv14 hv24 hv34 hge
    (by omega) (by omega) hfn hri.1
    (revAt_lab p.2.1 p.2.2 p.1 s.cellstart hn0 i2 i4 p.2.2.size) hri.2.1 hps
    (show Hex.GraphIso.Nauty.mash (Hex.GraphIso.Nauty.mash s.longcode first) p.2.2.size < 2 ^ 62 by
      have := Refine.mash_lt (Hex.GraphIso.Nauty.mash s.longcode first) p.2.2.size; omega) hq hnc ?_
  intro le5 m5 S5 hm5 hr5 ht5 e3 e4 e5 e6 e7 e8 hf5 ho5
  refine hQ le5 m5 S5 hm5 hr5 ht5 e4 e5 e6 e7 e8 (hf2.trans (hf4.trans hf5)) fun x hx hl hn => ?_
  have hP : x ∉ partTemps := fun h => hx (by simp only [cellTempsT, List.mem_append]; exact .inl (.inl (.inl h)))
  have hR : x ∉ revTemps := fun h => hx (by simp only [cellTempsT, List.mem_append]; exact .inl (.inl (.inr h)))
  have hF : x ∉ fixTemps := fun h => hx (by simp only [cellTempsT, List.mem_append]; exact .inl (.inr h))
  have hO : x ∉ [id.«v1», idOf 738, idOf 739] := fun h => hx (by simp only [cellTempsT, List.mem_append]; exact .inr h)
  simp only [partTemps, revTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hP hR hO
  rw [ho5 x hF hl hn, ho4 x (by simp [revTemps]; exact hR), temps_gso _ _ hR.2.2.1, temps_gso _ _ hl,
    ho2 x (by simp [partTemps]; exact hP), temps_gso _ _ hP.2.2.1, temps_gso _ _ hl, ← hle0,
    temps_gso _ _ hP.1, temps_gso _ _ hO.1, temps_gso _ _ hO.2.2, temps_gso _ _ hP.2.1,
    temps_gso _ _ hO.2.1]

end NautyVerified.Proofs.Sparse.Refine.Trivial

import NautyVerified.Proofs.Sparse.Refine.Count.Tail

/-!
# The installation after the first run

`wp_rest`: when the first two fragments are not the whole cell, the rest is
sorted, the second fragment pushed, `big` computed, the later fragments
split off (`wp_frag`) and `replace` applied. `wp_inner`: `innerG` computes
HexGraphIso's `finish` after its two hashes (`finish_split`).
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk isElement addElementB delElementB)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem replace_fields (first : Nat) (d : Bool) (s : RefineSt n) (bp : Option Nat) :
    (replace first d s bp).queue.size = s.queue.size ∧ (replace first d s bp).lab = s.lab := by
  cases bp with
  | none => exact ⟨rfl, rfl⟩
  | some pos =>
    rw [replace_some]
    split
    · cases d <;> simp [hashIf, RefineSt.hash]
    · exact ⟨rfl, rfl⟩

theorem FragOk.iter {level last : Nat} {d : Bool} {lab hits : Array Nat} (hlast : last ≤ n) :
    ∀ (F : Nat) (st : RefineSt n × Option Nat × Nat × Nat), FragOk n lab hits st → st.2.2.2 < last →
      FragOk n lab hits (iterF (fragStep level last d) F st)
  | 0, _, h, _ => h
  | F + 1, ⟨s, bp, bs, k⟩, h, hk => by
    by_cases hd : (s, bp, bs, k).2.2.2 ≥ last - 1
    · rw [iterF_frag_done hd]; exact h
    · rw [iterF_frag_next hd]
      simp only at hd hk
      have := fragNext_k level last d s bp bs k (by omega)
      exact FragOk.iter hlast F _ (h.next (by omega) hlast) (by omega)

/-- The case of more than two fragments. -/
abbrev restS (d : Bool) (t4 t5 tv0 tv1 : ident) : statement :=
  optSeq (!d) (sk (mash (tv id.«v3»)))
    (.Ssequence (sk sortS)
      (.Ssequence (enq t4 id.«v2»)
        (.Ssequence (addElementB id.«active» id.«nausparse:bit» (tv id.«v2»))
          (.Ssequence (sk (bigS d))
            (.Ssequence
              (.Ssequence (sk (.Sset id.«k» (.Ebinop .Osub (tv id.«v3») (ci 1 tint) tint)))
                (fragG d tv0 (runLoopG tv1)))
              (replaceS d t5))))))

/-- The tail after the sort, as `wp_rest` computes it. -/
def restRes (level first last : Nat) (d : Bool) (s : RefineSt n) (v2 v3 : Nat) : RefineSt n :=
  let s1 := hashIf (!d) s v3
  let s2 := ({ s1 with lab := Hex.GraphIso.Nauty.Sparse.Sort.indirect s1.lab s1.hits v3 (last - v3) }).push v2
  let b := big first d s2 v2 v3
  let R := iterF (fragStep level last d) (last - v3) (b.1, b.2.1, b.2.2, v3 - 1)
  replace first d R.1 R.2.1

theorem tail_rest (level first last : Nat) (d : Bool) (s : RefineSt n) (v2 v3 : Nat) (h : last ≠ v3) :
    tail level first last d s v2 v3 = restRes level first last d s v2 v3 := by
  unfold tail restRes
  rw [if_neg (by simpa using h)]
  simp only [fragLit_eq]

theorem big_fields (first : Nat) (d : Bool) (s : RefineSt n) (v2 v3 : Nat) :
    (big first d s v2 v3).1.queue = s.queue ∧ (big first d s v2 v3).1.lab = s.lab ∧
      (big first d s v2 v3).1.hits = s.hits ∧ (big first d s v2 v3).1.cellstart = s.cellstart ∧
      (big first d s v2 v3).1.ptn = s.ptn ∧ (big first d s v2 v3).1.numcells = s.numcells ∧
      (big first d s v2 v3).1.active = s.active ∧
      (s.longcode < 2 ^ 62 → (big first d s v2 v3).1.longcode < 2 ^ 62) := by
  unfold big
  split
  · cases d
    · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ?_⟩
      exact Nat.lt_of_lt_of_le (NautyVerified.Proofs.Refine.mash_lt _ _) (by decide)
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, id⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, id⟩

theorem wp_rest {Q : Post} {le : temp_env} {m : mem} {d : Bool} {t4 t5 tv0 tv1 : ident}
    (h4 : TT t4) (h5 : TT t5) (htv : FragT tv0 tv1) (hok : Ok n L) (hm : Mem m L G t S)
    (hv1t : id.«v1» ∉ fragTemps tv0 tv1)
    (hr : Rep L t S) (ht : Tmp le L t) {first v2 v3 last : Nat} (h12 : first + 1 ≤ v2) (h23 : v2 ≤ v3)
    (h3l : v3 < last) (hl : last ≤ n) (hlab : ∀ q < n, t.lab[q]! < n) (hsz : t.lab.size = n)
    (hcs : t.cellstart.size = n) (hps : t.ptn.size = n) (hc : t.longcode < 2 ^ 62)
    (hhits : ∀ v < n, S.w3[v]! = t.hits[v]!) (hqe : ∀ i < t.queue.size, t.queue[i]! < n)
    (hfin : (restRes L.level first last d t v2 v3).queue.size ≤ n)
    (hfl : ∀ q < n, (restRes L.level first last d t v2 v3).lab[q]! < n)
    (hv1 : PTree.get id.«v1» le = some (.Vint (ir first)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir v2)))
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir v3)))
    (hj : PTree.get id.«j» le = some (.Vint (ir last)))
    (hQ : ∀ le' m' S', After2 L G S m le ([t4, t5, id.«bigpos», id.«bigsize»] ++ fragTemps tv0 tv1)
      (restRes L.level first last d t v2 v3) le' m' S' →
      (restRes L.level first last d t v2 v3).longcode < 2 ^ 62 → Q.normal E0 empty_env le' m') :
    Wp xi sge F (restS d t4 t5 tv0 tv1) Q empty_env le m := by
  have hnl := hok.nlt
  let s1 := hashIf (!d) t v3
  let s1' : RefineSt n := { s1 with lab := Hex.GraphIso.Nauty.Sparse.Sort.indirect s1.lab s1.hits v3 (last - v3) }
  let s2 := s1'.push v2
  let b := big first d s2 v2 v3
  let st : RefineSt n × Option Nat × Nat × Nat := (b.1, b.2.1, b.2.2, v3 - 1)
  have hRR : restRes L.level first last d t v2 v3 =
      replace first d (iterF (fragStep L.level last d) (last - v3) st).1
        (iterF (fragStep L.level last d) (last - v3) st).2.1 := rfl
  have hs1 : s1.lab = t.lab ∧ s1.hits = t.hits ∧ s1.queue = t.queue ∧ s1.cellstart = t.cellstart ∧
      s1.ptn = t.ptn ∧ s1.active = t.active ∧ s1.longcode < 2 ^ 62 := by
    cases d
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
        Nat.lt_of_lt_of_le (NautyVerified.Proofs.Refine.mash_lt _ _) (by decide)⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hc⟩
  obtain ⟨hs1l, hs1h, hs1q, hs1c, hs1p, hs1a, hs1k⟩ := hs1
  obtain ⟨hbq, hbl, hbh, hbc, hbp, hbn, hba, hbk⟩ := big_fields first d s2 v2 v3
  have hst : FragOk n b.1.lab b.1.hits st := by
    refine ⟨rfl, rfl, by rw [hbc]; show s1.cellstart.size = n; rw [hs1c]; exact hcs,
      by rw [hbp]; show s1.ptn.size = n; rw [hs1p]; exact hps, hbk hs1k, fun p hp => ?_, ?_, ?_⟩
    · show p < b.1.queue.size
      rw [hbq]
      have hb2 : b.2.1 = if v2 - first < v3 - v2 then some (s2.queue.size - 1) else none := by
        simp only [b, big]; split <;> rfl
      simp only [st] at hp
      rw [hb2] at hp
      split at hp
      · cases hp; simp [s2, RefineSt.push]
      · cases hp
    · show b.2.2 ≤ n
      simp only [b, big]; split <;> (dsimp only; omega)
    · intro i hi
      show b.1.queue[i]! < n
      rw [hbq] at hi ⊢
      simp only [s2, RefineSt.push, Array.size_push] at hi ⊢
      by_cases he : i = s1'.queue.size
      · subst he; rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]; omega
      · rw [getElem!_pos _ _ (by simp; omega), Array.getElem_push_lt (by omega), ← getElem!_pos _ _ (by omega)]
        show s1.queue[i]! < n
        rw [hs1q]
        exact hqe i (by simp only [s1', hs1q] at hi he ⊢; omega)
  have hiter := FragOk.iter (level := L.level) (d := d) hl (last - v3) st hst (by simp only [st]; omega)
  have hmono := (frag_mono L.level last d (last - v3) st).1
  obtain ⟨hrq, hrl⟩ := replace_fields first d (iterF (fragStep L.level last d) (last - v3) st).1
    (iterF (fragStep L.level last d) (last - v3) st).2.1
  rw [hRR] at hfin hfl hQ
  rw [hrq] at hfin
  rw [hrl, hiter.lab] at hfl
  have hq2 : s2.queue.size ≤ n := by
    have : st.1.queue.size = s2.queue.size := by simp only [st]; rw [hbq]
    omega
  have hq1 : s1'.queue.size < n := by simp only [s2, RefineSt.push, Array.size_push] at hq2; omega
  -- MASH(v3) in the nontrivial pass
  refine wp_optMash (t := t) (!d) ht hc (show Exec.evalExpr sge empty_env le m (tv id.«v3») = _ from hv3)
    rfl (by omega) ?_
  intro le1 ht1 ho1
  have g1 : ∀ x, x ≠ id.longcode → PTree.get x le1 = PTree.get x le := ho1
  have hm1 : Mem m L G s1 S := Mem.hashIf hm (!d) v3
  have hr1 : Rep L s1 S := Rep.hashIf hr (!d) v3
  apply wp_seq
  wp_step; wp_step
  refine wp_sort (t := s1) (v3 := v3) (last := last) hok hm1 hr1 ht1 (by omega) (by omega) hl (by rw [hs1l]; exact hlab)
    (by rw [hs1l]; exact hsz) (by rw [hs1h]; exact hhits) (by rw [g1 _ (by decide)]; exact hv3)
    (by rw [g1 _ (by decide)]; exact hj) ?_
  intro m1 hm1' hf1
  simp only [seqPost, after_E0, E0_append]
  have hr1' : Rep L s1' S := { hr1 with }
  have ht1' : Tmp le1 L s1' := ht1.congr rfl rfl
  refine wp_pushBR h4.ne (h4.ne' (by simp)) (by decide) hok hm1' hr1' ht1' (c := v2)
    (by rw [g1 _ (by decide)]; exact hv2) (by omega) hq1 ?_
  rintro le2 m2 S2 ⟨hm2, hr2, ht2, hf2, hk2, -, ho2⟩
  have g2 : ∀ x, x ≠ t4 → x ≠ id.nactive → x ≠ id.longcode → PTree.get x le2 = PTree.get x le :=
    fun x a b c => by rw [ho2 x a b, g1 x c]
  apply wp_seq
  wp_step; wp_step
  have hq2' : 1 ≤ s2.queue.size := by simp [s2, RefineSt.push]
  refine wp_big (t := s2) (d := d) hok ht2 h12 h23 (by omega) hq2' hq2 (by
      show s1.longcode < _; exact hs1k)
    (by rw [g2 _ (h4.ne' (by simp)) (by decide) (by decide)]; exact hv1)
    (by rw [g2 _ (h4.ne' (by simp)) (by decide) (by decide)]; exact hv2)
    (by rw [g2 _ (h4.ne' (by simp)) (by decide) (by decide)]; exact hv3) ?_
  intro le3 ht3 hk3c hbp3 hbs3 ho3
  simp only [seqPost, after_E0, E0_append]
  have g3 : ∀ x, x ≠ t4 → x ≠ id.nactive → x ≠ id.longcode → x ≠ id.«bigpos» → x ≠ id.«bigsize» →
      PTree.get x le3 = PTree.get x le := fun x a b c e f => by rw [ho3 x e f c, g2 x a b c]
  have hm3 : Mem m2 L G b.1 S2 := hm2.congr hbl hbp hbn hba
  have hr3 : Rep L b.1 S2 :=
    { starts := by rw [hbc]; exact hr2.starts
      queue := by rw [hbq]; exact hr2.queue
      w3size := hr2.w3size
      w3small := hr2.w3small
      ptnSmall := by rw [hbp]; exact hr2.ptnSmall }
  apply wp_seq
  apply wp_seq
  wp_step; wp_step
  apply wp_set_eval
  have hv33 : PTree.get id.«v3» le3 = some (.Vint (ir v3)) := by
    rw [g3 _ (h4.ne' (by simp)) (by decide) (by decide) (by decide) (by decide)]; exact hv3
  rw [eval_dec (by omega) hv33]
  have hS2 : ∀ v < n, S2.w3[v]! = b.1.hits[v]! := fun v hv => by
    rw [hk2.w3, hbh]; show S.w3[v]! = s1.hits[v]!; rw [hs1h]; exact hhits v hv
  have hjn : id.«j» ∉ fragTemps tv0 tv1 := by
    simp only [fragTemps, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      fun h => htv.b0 (by rw [← h]; simp), fun h => htv.b1 (by rw [← h]; simp)⟩
  refine wp_frag (st := st) (fu := last - v3) htv hok hm3 hr3 (ht3.set (x := id.«k») _ (by decide)) hst
    (fun q hq => hfl q hq) hS2 (by simp only [st]; omega) hl (by simp only [st]; omega) hfin
    (by rw [temps_gss]) (by rw [temps_gso _ _ (by decide), g3 _ (fun h => h4.2.2.2 (by rw [← h]; simp))
      (by decide) (by decide) (by decide) (by decide)]; exact hj)
    (by rw [temps_gso _ _ (by decide)]; exact hbs3) (by rw [temps_gso _ _ (by decide)]; exact hbp3) ?_
  intro le4 m4 S4 hm4 hr4 ht4 hf4 hk4 hok4 hbp4 ho4
  simp only [seqPost, after_E0, E0_append]
  have hv14 : PTree.get id.«v1» le4 = some (.Vint (ir first)) := by
    rw [ho4 _ hv1t (by decide) (by decide), temps_gso _ _ (by decide),
      g3 _ (h4.ne' (by simp)) (by decide) (by decide) (by decide) (by decide)]; exact hv1
  refine wp_replace h5 hok hm4 hr4 ht4 (by omega) (by omega) hok4.bp hok4.qe hok4.code hv14 hbp4 ?_
  rintro le5 m5 S5 ⟨hm5, hr5, ht5, hf5, hk5, ho5⟩ hc5
  refine hQ le5 m5 S5 ⟨hm5, hr5, ht5, hf1.trans (hf2.trans (hf4.trans hf5)), hk2.trans (hk4.trans hk5),
    fun x hx h1 h2 => ?_⟩ hc5
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
  rw [ho5 x (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; exact hx.1.2.1) h1 h2,
    ho4 x hx.2 h1 h2]
  have hxk : x ≠ id.«k» := fun h => hx.2 (by rw [h]; simp [fragTemps])
  rw [temps_gso _ _ hxk, g3 x hx.1.1 h2 h1 hx.1.2.2.1 hx.1.2.2.2]

end NautyVerified.Proofs.Sparse.Refine.Count

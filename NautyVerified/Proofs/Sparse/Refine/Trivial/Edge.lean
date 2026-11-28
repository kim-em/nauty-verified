import NautyVerified.Proofs.Sparse.Refine.Trivial.CellLoop

/-!
# The singleton splitter's neighbour scan

`edgeLoopT`: for each neighbour `j` of the splitting vertex, `MARK2(j)`, and
the first time a nontrivial cell `k = CELLSTART[j]` is hit, `MARK1(k)` and
`HITCELL[hitcells++] = k`; this is `markStep` over the row.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {s : RefineSt n} {S : Scr}

/-- What the scan keeps: a cell start is marked exactly when it was recorded,
the records are distinct cell starts below `n`. -/
def MarkInv (n stamp : Nat) (r : Array Nat × Array Nat × Array Nat) : Prop :=
  (∀ k < n, r.1[k]! = stamp ↔ k ∈ r.2.1.toList) ∧ r.2.1.toList.Nodup ∧ (∀ k ∈ r.2.1.toList, k < n) ∧
    r.1.size = n ∧ r.2.2.size = n

theorem MarkInv.size_le {stamp : Nat} {r : Array Nat × Array Nat × Array Nat} (h : MarkInv n stamp r) :
    r.2.1.size ≤ n := by
  have hs := List.Nodup.length_le_of_subset h.2.1 (l₂ := List.range n)
    fun x hx => List.mem_range.2 (h.2.2.1 x hx)
  simpa using hs

theorem markStep_inv (g : Graph n) (starts : Array Nat) (stamp : Nat)
    {r : Array Nat × Array Nat × Array Nat} (e : Nat) (h : MarkInv n stamp r)
    (hk : starts[g.neighbor e]! ≤ n) :
    MarkInv n stamp (markStep g starts stamp r e) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold markStep
  split
  · rename_i hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    have hkn : starts[g.neighbor e]! < n := by omega
    have hnot : starts[g.neighbor e]! ∉ r.2.1.toList := fun hm => hc.2 ((h1 _ hkn).2 hm)
    refine ⟨fun k hk' => ?_, ?_, ?_, by simp [h4], by simp [h5]⟩
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton]
      by_cases he : k = starts[g.neighbor e]!
      · subst he
        rw [Array.getElem!_set!_self _ _ _ (show starts[g.neighbor e]! < r.1.size by omega)]; simp
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he), h1 k hk']; simp [he]
    · rw [Array.toList_push, List.nodup_append]
      exact ⟨h2, List.pairwise_singleton _ _, fun a ha b hb => by
        simp only [List.mem_singleton] at hb; subst hb; exact fun e => hnot (e ▸ ha)⟩
    · intro k hk'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk'
      rcases hk' with hk' | rfl
      · exact h3 k hk'
      · exact hkn
  · exact ⟨h1, h2, h3, h4, by simp [h5]⟩

/-- The scan after `q` edges from `vi`. -/
abbrev scanAt (g : Graph n) (starts marks vmarks : Array Nat) (stamp vi q : Nat) :
    Array Nat × Array Nat × Array Nat :=
  (List.range' vi q).foldl (markStep g starts stamp) (marks, #[], vmarks)

theorem scanAt_succ (g : Graph n) (starts marks vmarks : Array Nat) (stamp vi q : Nat) :
    scanAt g starts marks vmarks stamp vi (q + 1) =
      markStep g starts stamp (scanAt g starts marks vmarks stamp vi q) (vi + q) := by
  simp only [scanAt, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul]

/-- The temporaries the scan assigns. -/
abbrev edgeTemps : List ident := [id.«ii», id.«j», id.«k», id.«hitcells», idOf 736, idOf 737]

/-- `edgeLoopT` over the `D` edges from `vi`, from `ii = 0` and `hitcells = 0`. -/
theorem wp_edgeLoop {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G s S)
    (hr : Rep L s S) (ht : Tmp le L s) {stamp VI D : Nat} {marks vmarks : Array Nat}
    (hinv : MarkInv n stamp (marks, #[], vmarks))
    (h1 : ∀ k < n, (S.mk1 k = S.st1 ↔ marks[k]! = stamp))
    (h2 : ∀ v < n, (S.mk2 v = S.st2 ↔ vmarks[v]! = stamp))
    (hstarts : ∀ v < n, s.cellstart[v]! ≤ n)
    (hVD : VI + D ≤ G.neighbors.size) (hD : D < 2147483648)
    (hvi : PTree.get id.«vi» le = some (.Vlong (lr VI)))
    (hdi : PTree.get id.«di» le = some (.Vint (ir D)))
    (hii : PTree.get id.«ii» le = some (.Vlong (lr 0)))
    (hhc : PTree.get id.«hitcells» le = some (.Vint (ir 0)))
    (hQ : ∀ le' m' S', Mem m' L G s S' → Rep L s S' →
      S'.w1 = S.w1 → S'.w2 = S.w2 → S'.w3 = S.w3 → S'.st1 = S.st1 → S'.st2 = S.st2 →
      (∀ k < n, (S'.mk1 k = S'.st1 ↔
        (scanAt (Graph.ofGraph G) s.cellstart marks vmarks stamp VI D).1[k]! = stamp)) →
      (∀ v < n, (S'.mk2 v = S'.st2 ↔
        (scanAt (Graph.ofGraph G) s.cellstart marks vmarks stamp VI D).2.2[v]! = stamp)) →
      (∀ i < (scanAt (Graph.ofGraph G) s.cellstart marks vmarks stamp VI D).2.1.size,
        S'.w4 i = .Vint (ir (scanAt (Graph.ofGraph G) s.cellstart marks vmarks stamp VI D).2.1[i]!)) →
      MarkInv n stamp (scanAt (Graph.ofGraph G) s.cellstart marks vmarks stamp VI D) →
      PTree.get id.«hitcells» le' =
        some (.Vint (ir (scanAt (Graph.ofGraph G) s.cellstart marks vmarks stamp VI D).2.1.size)) →
      Frame L m m' → (∀ x, x ∉ edgeTemps → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F edgeLoopT Q empty_env le m := by
  have hnl := hok.nlt
  have hn0 := hok.n0
  have hnd := Isautom.nde_lt hm.graph.earr
  let g := Graph.ofGraph G
  let R := scanAt g s.cellstart marks vmarks stamp VI
  let Inv := fun (q : Nat) (le' : temp_env) (m' : mem) (S' : Scr) =>
    Mem m' L G s S' ∧ Rep L s S' ∧ S'.w1 = S.w1 ∧ S'.w2 = S.w2 ∧ S'.w3 = S.w3 ∧ S'.st1 = S.st1 ∧
      S'.st2 = S.st2 ∧ (∀ k < n, (S'.mk1 k = S'.st1 ↔ (R q).1[k]! = stamp)) ∧
      (∀ v < n, (S'.mk2 v = S'.st2 ↔ (R q).2.2[v]! = stamp)) ∧
      (∀ i < (R q).2.1.size, S'.w4 i = .Vint (ir (R q).2.1[i]!)) ∧ MarkInv n stamp (R q) ∧
      PTree.get id.«hitcells» le' = some (.Vint (ir (R q).2.1.size)) ∧ Frame L m m' ∧
      ∀ x, x ∉ edgeTemps → PTree.get x le' = PTree.get x le
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q S', v = D - q ∧ q ≤ D ∧ Inv q le' m' S' ∧
      PTree.get id.«ii» le' = some (.Vlong (lr q))
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q S', v = D - q ∧ q < D ∧ Inv (q + 1) le' m' S' ∧
      PTree.get id.«ii» le' = some (.Vlong (lr q))
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := D - 0)
    ⟨rfl, rfl, 0, S, rfl, Nat.zero_le _, ⟨hm, hr, rfl, rfl, rfl, rfl, rfl, h1, h2,
      fun i hi => by simp [R, scanAt] at hi, hinv, by simpa [R, scanAt] using hhc, Frame.refl _ _,
      fun _ _ => rfl⟩, hii⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, q, S', rfl, hqD, ⟨hm', hr', e1, e2, e3, e5, e6, r1, r2, r4, hmi,
      hhc', hf, ho⟩, hiq⟩
    have ht' : Tmp le' L s := ht.frame ho (by decide)
    have hvi' : PTree.get id.«vi» le' = some (.Vlong (lr VI)) := by rw [ho _ (by decide)]; exact hvi
    have hdi' : PTree.get id.«di» le' = some (.Vint (ir D)) := by rw [ho _ (by decide)]; exact hdi
    wp_step; wp_step; wp_step
    refine wp_if_ob (b := decide (q < D)) ?_ rfl ?_
    · rw [eval_binop (show Exec.evalExpr sge empty_env le' m' (.Etempvar id.«ii» tulong) = _ from hiq)
        (eval_tv hdi')]
      simp only [typeof, cop, Isautom.cast_l_i D hD, Alloc.ltu_lr (a := q) (b := D) (by omega) (by omega)]
    by_cases hq : q < D
    · simp only [hq, decide_true, ite_true]
      apply wp_skip
      simp only [E0_append]
      have hidx : VI + q < G.neighbors.size := by omega
      have hJ : g.neighbor (VI + q) < n := neighbor_lt G hidx
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_idx_l (pe := .Etempvar id.«e» (tptr tint)) hm'.graph.earr (by omega) ht'.e rfl rfl rfl _
        (VI + q) hidx (by
          rw [eval_binop (show Exec.evalExpr sge empty_env le' m' (.Etempvar id.«vi» tulong) = _ from hvi')
            (show Exec.evalExpr sge empty_env le' m' (.Etempvar id.«ii» tulong) = _ from hiq)]
          simp only [typeof, cop, lr_add]) rfl]
      dsimp only [eVals]
      let J0 := g.neighbor (VI + q)
      let le1 := PTree.set id.«j» (.Vint (ir (J0 : Int))) le'
      have hj1 : PTree.get id.«j» le1 = some (.Vint (ir (J0 : Int))) := temps_gss _ _ _
      simp only [E0_append]
      wp_step; wp_step; wp_step
      refine wp_mark2 hok hm' (eval_tv hj1) rfl (by have := hok.mc2; omega) fun m1 hm1 hf1 => ?_
      simp only [E0_append]
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_gw1 hok hm1 (eval_tv hj1) rfl (by have := hok.c1; omega)]
      dsimp only
      rw [hr'.starts J0 hJ]
      let K0 := s.cellstart[J0]!
      have hK0 : K0 ≤ n := hstarts J0 hJ
      let le2 := PTree.set id.«k» (.Vint (ir (K0 : Int))) le1
      have hk2 : PTree.get id.«k» le2 = some (.Vint (ir (K0 : Int))) := temps_gss _ _ _
      have ht2 : Tmp le2 L s := (ht'.set _ (by decide)).set _ (by decide)
      simp only [E0_append]
      wp_step; wp_step; wp_step
      refine wp_if_ob (b := !decide ((K0 : Int) = n)) (eval_nei (eval_tv hk2) rfl (eval_tv ht2.n) rfl
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
      have hRs := scanAt_succ g s.cellstart marks vmarks stamp VI q
      have hmi' := markStep_inv g s.cellstart stamp (VI + q) hmi hK0
      rw [← hRs] at hmi'
      obtain ⟨m1a, m1b, m1c, m1d, m1e⟩ := hmi
      -- the vertex marks after `MARK2(j)`
      have r2' : ∀ v < n, (setMark S'.mk2 J0 S'.st2 v = S'.st2 ↔ (R (q + 1)).2.2[v]! = stamp) := by
        intro v hv
        have hR2 : (R (q + 1)).2.2 = (R q).2.2.set! J0 stamp := by
          simp only [R, hRs, markStep]; split <;> rfl
        rw [hR2]
        simp only [setMark]
        by_cases he : v = J0
        · subst he; rw [Array.getElem!_set!_self _ _ _ (by omega)]; simp
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]; simp only [he, ite_false]; exact r2 v hv
      have fin : ∀ (b : Bool), b = (K0 != n && (R q).1[K0]! != stamp) →
          Wp xi sge F
            (.Sifthenelse (tv (idOf 737))
              (.Ssequence (sk (.Sassign (mk id.«nausparse:vmark1» (tv id.«k»))
                  (.Evar id.«nausparse:vmark1_val» tshort)))
                (.Ssequence (.Ssequence (sk (.Sset (idOf 736) (tv id.«hitcells»)))
                  (.Sset id.«hitcells» (.Ebinop .Oadd (tv (idOf 736)) (ci 1 tint) tint)))
                  (.Sassign (gix id.«nausparse:work4» (tv (idOf 736))) (tv id.«k»))))
              .Sskip)
            { normal := fun t => J (D - q) (E0 ++ t), brk := fun t => Q.normal (E0 ++ t),
              cont := fun t => J (D - q) (E0 ++ t), ret := fun t => Q.ret (E0 ++ t) }
            empty_env (PTree.set (idOf 737) (Val.of_bool b) le2) m1 := by
        intro b hb
        refine wp_if_ob (b := b) (eval_tv (temps_gss _ _ _)) rfl ?_
        let le3 := PTree.set (idOf 737) (Val.of_bool b) le2
        have hk3 : PTree.get id.«k» le3 = some (.Vint (ir (K0 : Int))) := by
          rw [temps_gso _ _ (by decide)]; exact hk2
        have hhc3 : PTree.get id.«hitcells» le3 = some (.Vint (ir (R q).2.1.size)) := by
          rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hhc'
        have hii3 : PTree.get id.«ii» le3 = some (.Vlong (lr q)) := by
          rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hiq
        have ho3 : ∀ x, x ∉ edgeTemps → PTree.get x le3 = PTree.get x le := by
          intro x hx
          simp only [edgeTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          rw [temps_gso _ _ hx.2.2.2.2.2, temps_gso _ _ hx.2.2.1, temps_gso _ _ hx.2.1]
          exact ho x (by simp [edgeTemps]; exact hx)
        by_cases hbt : b = true
        · subst hbt
          have hc : K0 ≠ n ∧ (R q).1[K0]! ≠ stamp := by simpa using hb.symm
          have hKlt : K0 < n := by omega
          have hnot : K0 ∉ (R q).2.1.toList := fun h => hc.2 ((m1a K0 hKlt).2 h)
          have hsz : (R q).2.1.size < n := by
            have := MarkInv.size_le hmi'
            have hR1 : (R (q + 1)).2.1 = (R q).2.1.push K0 := by
              simp only [R, hRs, markStep]; rw [ite_eq_left (by simpa using hc)]
            rw [hR1] at this; simp at this
            have hle := List.Nodup.length_le_of_subset (l₁ := K0 :: (R q).2.1.toList)
              (List.nodup_cons.2 ⟨hnot, m1b⟩) (l₂ := List.range n)
              (fun x hx => List.mem_range.2 (by
                simp only [List.mem_cons] at hx; rcases hx with rfl | hx
                · exact hKlt
                · exact m1c x hx))
            simp at hle; omega
          have hR : R (q + 1) = ((R q).1.set! K0 stamp, (R q).2.1.push K0, (R q).2.2.set! J0 stamp) := by
            simp only [R, hRs, markStep]; rw [ite_eq_left (by simpa using hc)]
          simp only [ite_true]
          wp_step; wp_step; wp_step
          refine wp_mark1 hok hm1 (eval_tv hk3) rfl (by have := hok.mc1; omega) fun m2 hm2 hf2 => ?_
          simp only [E0_append]
          wp_step; wp_step; wp_step
          apply wp_skip
          apply wp_set_eval
          rw [eval_tv hhc3]
          dsimp only
          apply wp_set_eval
          rw [eval_inc (temps_gss _ _ _)]
          dsimp only
          let le4 := PTree.set id.«hitcells» (.Vint (ir (((R q).2.1.size : Int) + 1)))
            (PTree.set (idOf 736) (.Vint (ir ((R q).2.1.size : Int))) le3)
          refine wp_w4 hok hm2 (eval_tv (show PTree.get (idOf 736) le4 = some (.Vint (ir (R q).2.1.size)) by
            rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _)) rfl (by have := hok.c4; omega)
            (eval_tv (show PTree.get id.«k» le4 = _ by
              rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hk3)) rfl ?_
          intro m3 hm3 hf3
          refine ⟨by simp, rfl, q, _, rfl, hq, ⟨hm3, ⟨hr'.starts, hr'.queue, hr'.w3size, hr'.w3small,
            hr'.ptnSmall⟩, e1, e2, e3, e5, e6, ?_, ?_, ?_, hmi', ?_, hf.trans (hf1.trans (hf2.trans hf3)),
            ?_⟩, ?_⟩
          · intro k hk
            rw [hR]
            simp only [setMark]
            by_cases he : k = K0
            · subst he; rw [Array.getElem!_set!_self _ _ _ (by omega)]; simp
            · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]; simp only [he, ite_false]; exact r1 k hk
          · intro v hv; exact r2' v hv
          · intro i hi
            rw [hR] at hi ⊢
            simp only [Array.size_push] at hi
            by_cases he : i = (R q).2.1.size
            · subst he; simp only [upd_same, push_size]
            · dsimp only
              rw [upd_ne _ _ he, push_lt _ _ _ (by omega)]; exact r4 i (by omega)
          · rw [temps_gss, hR]; simp
          · intro x hx
            simp only [edgeTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
            rw [temps_gso _ _ hx.2.2.2.1, temps_gso _ _ hx.2.2.2.2.1]
            exact ho3 x (by simp [edgeTemps]; exact hx)
          · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hii3
        · have hbf : b = false := by simpa using hbt
          subst hbf
          have hc : ¬ (K0 ≠ n ∧ (R q).1[K0]! ≠ stamp) := by
            intro h; have := hb; simp [h.1, h.2] at this
          have hR : R (q + 1) = ((R q).1, (R q).2.1, (R q).2.2.set! J0 stamp) := by
            simp only [R, hRs, markStep]; rw [ite_eq_right (by simpa using hc)]
          simp only [Bool.false_eq_true, ite_false]
          apply wp_skip
          refine ⟨by simp, rfl, q, _, rfl, hq, ⟨hm1, ⟨hr'.starts, hr'.queue, hr'.w3size, hr'.w3small,
            hr'.ptnSmall⟩, e1, e2, e3, e5, e6, ?_, r2', ?_, hmi', ?_, hf.trans hf1, ho3⟩, hii3⟩
          · rw [hR]; exact r1
          · rw [hR]; exact r4
          · rw [hR]; exact hhc3
      by_cases hKn : K0 = n
      · simp only [show decide ((K0 : Int) = n) = true by simp; omega, Bool.not_true,
          Bool.false_eq_true, ite_false]
        apply wp_set_eval
        simp only [Exec.evalExpr]
        exact fin false (by simp [hKn])
      · simp only [show decide ((K0 : Int) = n) = false by simp; omega, Bool.not_false, ite_true]
        wp_step; wp_step
        apply wp_set_eval
        have hM1 : MarksAt m1 L.mc1 L.mb1 S'.st1 S'.mk1 := hm1.k1
        have hb1 := hM1.bounds K0 (by have := hok.mc1; omega)
        rw [Exec.evalExpr, eval_binop (eval_mk1 hok hm1 (eval_tv hk2) rfl (by have := hok.mc1; omega))
          (eval_val1 hm1)]
        simp only [typeof, cop]
        rw [eq_marks hb1.1 (by have := hM1.val32; omega) (by omega) (by have := hM1.val32; omega)]
        simp only [cast_b]
        exact fin _ (by
          have := r1 K0 (by omega)
          by_cases hm : S'.mk1 K0 = S'.st1
          · simp [hm, this.1 hm]
          · have : (R q).1[K0]! ≠ stamp := fun h => hm (this.2 h)
            simp [hm, this, hKn])
    · simp only [hq, decide_false, Bool.false_eq_true, ite_false]
      apply wp_break
      have hqe : q = D := by omega
      subst hqe
      exact hQ le' m' S' hm' hr' e1 e2 e3 e5 e6 r1 r2 r4 hmi hhc' hf
        fun x hx => ho x hx
  · rintro v tr e' le' m' ⟨rfl, rfl, q, S', rfl, hqD, hinv', hiq⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_binop (show Exec.evalExpr sge empty_env le' m' (.Etempvar id.«ii» tulong) = _ from hiq) rfl]
    simp only [typeof, cop, Alloc.add_lr_one]
    refine ⟨D - (q + 1), by omega, by simp, rfl, q + 1, S', rfl, hqD, ?_, temps_gss _ _ _⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hinv'
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      by rw [temps_gso _ _ (by decide)]; exact a12, a13,
      fun x hx => by rw [temps_gso _ _ (fun h => hx (by rw [h]; simp [edgeTemps])), a14 x hx]⟩

end NautyVerified.Proofs.Sparse.Refine.Trivial

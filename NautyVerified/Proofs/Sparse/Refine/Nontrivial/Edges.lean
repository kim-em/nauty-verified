import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Mark
import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Scan
import NautyVerified.Proofs.Sparse.Isautom.Loops

/-!
# The neighbour loop of `refine_sg`'s nontrivial pass

`CRep L s S c`: memory holds the count state `c` of the splitter state `s`
(`HITS` its hit counts, `HITCELL` its touched starts, the first mark array
equal to its stamp exactly at the cells `c` marks). `wp_edge`: one neighbour
(`edgeBody`) computes `countEdge`; `wp_edgeLoopN`: the loop over the
neighbours of the vertex at position `q` computes `countVertex`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph CountScan)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {S : Scr}

/-- Memory holds the count state `c` of `s`. -/
structure CRep (s : RefineSt n) (S : Scr) (c : CS) : Prop where
  hits : S.w3 = c.2.1
  touched : ∀ i < c.2.2.size, S.w4 i = .Vint (ir c.2.2[i]!)
  marks : ∀ k < n, (S.mk1 k = S.st1 ↔ c.1[k]! = s.stamp + 1)

/-- One neighbour: `j = e[vi + ii]; k = CELLSTART[j]; if (k != n) ...`. -/
abbrev edgeBody : statement :=
  .Ssequence
    (sk (.Sset id.«j» (ix id.«e» (.Ebinop .Oadd (.Etempvar id.«vi» tulong) (.Etempvar id.«ii» tulong) tulong))))
    (.Ssequence
      (sk (.Sset id.«k» (gix id.«nausparse:work1» (tv id.«j»))))
      (sk
        (.Sifthenelse
          (.Ebinop .One (tv id.«k») (tv id.«n») tint)
          (.Ssequence
            (sk
              (.Sifthenelse
                (.Ebinop .One
                  (mk id.«nausparse:vmark1» (tv id.«k»))
                  (.Evar id.«nausparse:vmark1_val» tshort)
                  tint)
                (.Ssequence
                  (sk
                    (.Sassign
                      (mk id.«nausparse:vmark1» (tv id.«k»))
                      (.Evar id.«nausparse:vmark1_val» tshort)))
                  (.Ssequence
                    (.Ssequence
                      (.Ssequence
                        (sk (.Sset (idOf 751) (tv id.«hitcells»)))
                        (.Sset id.«hitcells» (.Ebinop .Oadd (tv (idOf 751)) (ci 1 tint) tint)))
                      (.Sassign (gix id.«nausparse:work4» (tv (idOf 751))) (tv id.«k»)))
                    clearLoop))
                .Sskip))
            (sk
              (.Sassign
                (gix id.«nausparse:work3» (tv id.«j»))
                (.Ebinop .Oadd (gix id.«nausparse:work3» (tv id.«j»)) (ci 1 tint) tint))))
          .Sskip)))

theorem edgeLoopN_eq : edgeLoopN =
    .Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (.Etempvar id.«ii» tulong) (tv id.«di») tint) .Sskip .Sbreak))
        edgeBody)
      (sk (.Sset id.«ii» (.Ebinop .Oadd (.Etempvar id.«ii» tulong) (ci 1 tint) tulong))) := rfl

/-- The temporaries the neighbour loop assigns. -/
abbrev edgeTemps : List ident := [id.«ii», id.«j», id.«k», id.«hitcells», idOf 751, idOf 752]

/-- A count state's touched starts number at most `n`. -/
theorem touched_le {s : RefineSt n} {c : CS} {seen : List Nat}
    (h : CountScan n s.stamp s.marks c.1 c.2.2 s.cellstart c.2.1 seen) : c.2.2.size ≤ n := by
  have hs := List.Nodup.length_le_of_subset h.touch.nodup (l₂ := List.range n)
    fun x hx => List.mem_range.2 ((h.touch.members x).mp hx).1
  simpa using hs

/-- The `int` value of a vertex row offset sum `off + r` read as `e[vi + ii]`. -/
theorem eval_e {le : temp_env} {m : mem} {t : RefineSt n} (hm : Mem m L G t S) (ht : Tmp le L t)
    {off r : Nat} (hvi : PTree.get id.«vi» le = some (.Vlong (lr off)))
    (hii : PTree.get id.«ii» le = some (.Vlong (lr r))) (hb : off + r < G.neighbors.size) :
    Exec.evalExpr sge empty_env le m
      (ix id.«e» (.Ebinop .Oadd (.Etempvar id.«vi» tulong) (.Etempvar id.«ii» tulong) tulong)) =
      some (.Vint (ir ((Graph.ofGraph G).neighbor (off + r)))) := by
  have hnd := Isautom.nde_lt hm.graph.earr
  refine eval_idx_l hm.graph.earr (by omega) (by simp only [Exec.evalExpr]; exact ht.e) rfl rfl rfl _ _
    hb ?_ rfl
  simp only [Exec.evalExpr, hvi, hii, typeof, cop, Sparse.lr_add]

/-- One neighbour of the vertex at position `q`, the `r`-th. -/
theorem wp_edge {Q : Post} {le : temp_env} {m : mem} {s : RefineSt n} {c : CS} {split q r : Nat}
    (hok : Ok n L) (hm : Mem m L G s S) (hr : Rep L s S) (ht : Tmp le L s) (hv : s.Valid L.level)
    (hcr : CRep s S c)
    (hscan : CountScan n s.stamp s.marks c.1 c.2.2 s.cellstart c.2.1 (seenTo (.ofGraph G) s split q r))
    (hq : q < n) (hsq : split ≤ q) (hrd : r < deg (.ofGraph G) s q)
    (hvi : PTree.get id.«vi» le = some (.Vlong (lr (Graph.ofGraph G).offsets[s.lab[q]!]!)))
    (hii : PTree.get id.«ii» le = some (.Vlong (lr r)))
    (hhc : PTree.get id.«hitcells» le = some (.Vint (ir c.2.2.size)))
    (hQ : ∀ le' m' S', Mem m' L G s S' → Rep L s S' →
      CRep s S' (countEdge s c ((Graph.ofGraph G).neighbor ((Graph.ofGraph G).offsets[s.lab[q]!]! + r))) →
      Frame L m m' →
      PTree.get id.«hitcells» le' = some (.Vint (ir (countEdge s c
        ((Graph.ofGraph G).neighbor ((Graph.ofGraph G).offsets[s.lab[q]!]! + r))).2.2.size)) →
      (∀ x, x ∉ edgeTemps → PTree.get x le' = PTree.get x le) → PTree.get id.«ii» le' = PTree.get id.«ii» le →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F edgeBody Q empty_env le m := by
  have hnl := hok.nlt
  have hl := Hex.GraphIso.Nauty.Sparse.perm_bound hv.lab hq
  let off := (Graph.ofGraph G).offsets[s.lab[q]!]!
  have hlo := G.offset_mono (i := s.lab[q]!) (j := s.lab[q]! + 1) (by omega) (by omega)
  have hhi := G.offset_le (i := s.lab[q]! + 1) (by omega)
  have hb : off + r < G.neighbors.size := by
    simp only [deg, Graph.ofGraph] at hrd; simp only [off, Graph.ofGraph]; omega
  let j := (Graph.ofGraph G).neighbor (off + r)
  have hj : j < n := neighbor_lt G hb
  have hscan' := edge_scan hv hj hscan
  rw [← seenTo_succ _ _ _ _ _ hrd] at hscan'
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_e hm ht hvi hii hb]
  let le1 := PTree.set id.«j» (.Vint (ir j)) le
  have ht1 : Tmp le1 L s := ht.set _ (by decide)
  have hj1 : Exec.evalExpr sge empty_env le1 m (tv id.«j») = some (.Vint (ir j)) := by
    simp only [Exec.evalExpr, le1, temps_gss]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_gw1 hok hm hj1 rfl (by have := hok.c1; omega), hr.starts j hj]
  let k := s.cellstart[j]!
  have hkk : k = s.cellstart[j]! := rfl
  have hkle : k ≤ n := hv.index.vertex_le hv.size hv.closed hv.lab hj
  let le2 := PTree.set id.«k» (.Vint (ir k)) le1
  have ht2 : Tmp le2 L s := ht1.set _ (by decide)
  have hk2 : Exec.evalExpr sge empty_env le2 m (tv id.«k») = some (.Vint (ir k)) := by
    simp only [Exec.evalExpr, le2, temps_gss]
  have hfr2 : ∀ x, x ∉ edgeTemps → PTree.get x le2 = PTree.get x le := fun x hx => by
    simp only [le2, le1]
    rw [temps_gso _ _ (fun h => hx (by simp [h])), temps_gso _ _ (fun h => hx (by simp [h]))]
  have hii2 : PTree.get id.«ii» le2 = PTree.get id.«ii» le := by
    simp only [le2, le1]; rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]
  have hhc2 : PTree.get id.«hitcells» le2 = some (.Vint (ir c.2.2.size)) := by
    simp only [le2, le1]; rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hhc
  wp_step; wp_step
  apply wp_if_eval
  rw [eval_binop hk2 (show Exec.evalExpr sge empty_env le2 m (tv id.«n») = _ from ht2.n)]
  simp only [typeof, cop]
  rw [ir_eq (a := (k : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hkn : k = n
  · rw [show decide ((k : Int) = n) = true from decide_eq_true (by omega)]
    simp (config := {decide := true}) only [cop, ite_false]
    apply wp_skip
    have hce : countEdge s c j = c := by
      unfold countEdge; simp only [show s.cellstart[j]! = n from hkn, bne_self_eq_false,
        Bool.false_eq_true, ite_false]
    exact hQ le2 m S hm hr (by rw [show (Graph.ofGraph G).neighbor (off + r) = j from rfl, hce]; exact hcr)
      (Frame.refl _ _) (by rw [show (Graph.ofGraph G).neighbor (off + r) = j from rfl, hce]; exact hhc2)
      hfr2 hii2
  · have hkn' : k < n := by omega
    rw [show decide ((k : Int) = n) = false from decide_eq_false (by omega)]
    simp (config := {decide := true}) only [cop, ite_true]
    let c' := countEdge s c j
    have hsc' : c'.2.2.size ≤ n := touched_le hscan'
    have tail : ∀ (m1 : mem) (S1 : Scr) (le' : temp_env), Mem m1 L G s S1 → Rep L s S1 →
        Frame L m m1 → Tmp le' L s → PTree.get id.«j» le' = some (.Vint (ir j)) →
        CRep s { S1 with w3 := S1.w3.set! j (S1.w3[j]! + 1) } c' →
        PTree.get id.«hitcells» le' = some (.Vint (ir c'.2.2.size)) →
        (∀ x, x ∉ edgeTemps → PTree.get x le' = PTree.get x le) →
        PTree.get id.«ii» le' = PTree.get id.«ii» le →
        S1.w3[j]! + 1 < 2147483648 →
        Wp xi sge F (sk (.Sassign (gix id.«nausparse:work3» (tv id.«j»))
          (.Ebinop .Oadd (gix id.«nausparse:work3» (tv id.«j»)) (ci 1 tint) tint))) Q empty_env le' m1 := by
      intro m1 S1 le' hm1 hr1 hf1 ht' hj' hcr' hhc' hfr' hii' hsm
      wp_step; wp_step
      have hj1' : Exec.evalExpr sge empty_env le' m1 (tv id.«j») = some (.Vint (ir j)) := hj'
      refine wp_storeHits hok hm1 hr1.w3size hj1' rfl hj (x := S1.w3[j]! + 1)
        (rhs := .Ebinop .Oadd (gix id.«nausparse:work3» (tv id.«j»)) (ci 1 tint) tint) ?_ rfl ?_
      · rw [eval_binop (eval_gw3 hok hm1 hj1' rfl hj) (by rfl)]
        simp only [typeof, cop, ir_add]; push_cast; rfl
      intro m2 hm2 hf2
      refine hQ le' m2 _ hm2 ⟨hr1.starts, hr1.queue, by simpa using hr1.w3size, fun i hi => ?_,
        hr1.ptnSmall⟩ hcr' (hf1.trans hf2) hhc' hfr' hii'
      by_cases hij : i = j
      · subst hij; rw [Array.getElem!_set!_self _ _ _ (by rw [hr1.w3size]; exact hi)]; exact hsm
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hij)]; exact hr1.w3small i hi
    have hjseen : j ∈ seenTo (.ofGraph G) s split q (r + 1) := by
      rw [seenTo_succ _ _ _ _ _ hrd]; simp [j, off]
    have hcnt : c'.2.1[j]! ≤ q - split + 1 :=
      count_le G hv hq hscan' hj hkn' (List.mem_map.mpr ⟨j, hjseen, rfl⟩)
    have hj2 : PTree.get id.«j» le2 = some (.Vint (ir j)) := by
      simp only [le2, le1]; rw [temps_gso _ _ (by decide), temps_gss]
    have hm1n := hok.mc1
    apply wp_seq; simp only [seqPost, Post.after]
    wp_step; wp_step
    apply wp_if_eval
    rw [eval_binop (eval_mark1 hok hm hk2 rfl hkn') (eval_stamp1 hm)]
    simp only [typeof, cop]
    have hbd := hm.k1.bounds k (by omega)
    have hst := hm.k1.val32
    rw [ir_eq (a := S.mk1 k) (b := (S.st1 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have hmk := hcr.marks k hkn'
    by_cases hmark : S.mk1 k = S.st1
    · rw [show decide (S.mk1 k = (S.st1 : Int)) = true from decide_eq_true hmark]
      simp (config := {decide := true}) only [cop, ite_false]
      apply wp_skip
      have hm' : c.1[k]! = s.stamp + 1 := hmk.mp hmark
      have hce : c' = (c.1, c.2.1.set! j (c.2.1[j]! + 1), c.2.2) := by
        simp only [c', countEdge, show (s.cellstart[j]! != n) = true by simpa using hkn,
          ite_true, show c.1[s.cellstart[j]!]! = s.stamp + 1 from hm', bne_self_eq_false,
          Bool.false_eq_true, ite_false]
      refine tail m S le2 hm hr (Frame.refl _ _) ht2 hj2 ?_ (by rw [hce]; exact hhc2) hfr2 hii2 ?_
      · rw [hce]
        exact ⟨by simp only [hcr.hits], hcr.touched, hcr.marks⟩
      · have := hcnt
        rw [hce] at this
        simp only at this
        rw [Array.getElem!_set!_self _ _ _ (by rw [← hcr.hits, hr.w3size]; exact hj)] at this
        rw [hcr.hits]; omega
    · rw [show decide (S.mk1 k = (S.st1 : Int)) = false from decide_eq_false hmark]
      simp (config := {decide := true}) only [cop, ite_true]
      have hm' : ¬ c.1[k]! = s.stamp + 1 := fun h => hmark (hmk.mpr h)
      have hc := hv.index.vertex_cell hv.size hv.closed hv.lab hj (show s.cellstart[j]! ≠ n from hkn)
      dsimp only at hc
      let e := s.cellend[k]!
      have hek : e = s.cellend[k]! := rfl
      have hke : k < e ∧ e < n := hc.2
      let cl := clearCell s.lab k (e + 1 - k) c.2.1
      have hce : c' = (c.1.set! k (s.stamp + 1), cl.set! j (cl[j]! + 1), c.2.2.push k) := by
        simp only [c', countEdge, show (s.cellstart[j]! != n) = true by simpa using hkn, ite_true,
          show (c.1[s.cellstart[j]!]! != s.stamp + 1) = true by simpa using hm']
        rfl
      wp_step; wp_step; wp_step
      refine wp_storeMark1 hok hm hk2 rfl hkn' ?_
      intro m1 hm1 hf1
      dsimp only
      wp_step; wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr]
      rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hhc]
      wp_step
      simp only [temps_gss, typeof, cop, ir_add]
      have hsz1 : c.2.2.size + 1 = c'.2.2.size := by rw [hce]; simp
      let le3 := PTree.set id.«hitcells» (.Vint (ir ((c.2.2.size : Int) + 1)))
        (PTree.set (idOf 751) (.Vint (ir c.2.2.size)) le2)
      have ht3 : Tmp le3 L s := (ht2.set _ (by decide)).set _ (by decide)
      have h751 : Exec.evalExpr sge empty_env le3 m1 (tv (idOf 751)) = some (.Vint (ir c.2.2.size)) := by
        simp only [Exec.evalExpr, le3]; rw [temps_gso _ _ (by decide), temps_gss]
      have hk3 : Exec.evalExpr sge empty_env le3 m1 (tv id.«k») = some (.Vint (ir k)) := by
        simp only [Exec.evalExpr, le3]; rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]
        exact hk2
      refine wp_storeHitcell (le := le3) hok hm1 h751 rfl (by have := hok.c4; omega) hk3 rfl ?_
      intro m2 hm2 hf2
      have hr2 : Rep L s { S with mk1 := (fun x => if x = k then (S.st1 : Int) else S.mk1 x), w4 := upd S.w4 c.2.2.size (.Vint (ir k)) } :=
        ⟨hr.starts, hr.queue, hr.w3size, hr.w3small, hr.ptnSmall⟩
      have hk3' : PTree.get id.«k» le3 = some (.Vint (ir k)) := hk3
      refine wp_clearLoop (a := k) (e := e) hok hm2 hr2 ht3 (fun i hi => Hex.GraphIso.Nauty.Sparse.perm_bound hv.lab hi)
        (Nat.le_of_lt hc.2.1) hc.2.2 (fun p h1 h2 => hc.1.2.2.1 p h1 (by
          have h3 := hc.2.1; dsimp only [e, k] at h1 h2 h3 ⊢; omega))
        (by have h4 := hc.1.2.2.2; have h3 := hc.2.1; dsimp only [e, k] at h4 h3 ⊢
            rwa [show s.cellstart[j]! + (s.cellend[s.cellstart[j]!]! + 1 - s.cellstart[j]!) - 1 =
              s.cellend[s.cellstart[j]!]! by omega] at h4) hk3' ?_
      intro le4 m3 hm3 hf3 hk4 hfr4
      have ht4 := ht3.frame hfr4 (by decide)
      have hcl : clearCell s.lab k (e + 1 - k) S.w3 = cl := by simp only [cl, hcr.hits]
      have hw := clear_writes (lab := s.lab) (hcr.hits ▸ hr.w3size) k (e + 1 - k)
        (fun q' _ h2 => Hex.GraphIso.Nauty.Sparse.perm_bound hv.lab (by
          have h5 : q' < k + (e + 1 - k) := h2
          omega))
      have hclsz : cl.size = n := hw.size
      have hfr3 : ∀ x, x ∉ edgeTemps → PTree.get x le4 = PTree.get x le := fun x hx => by
        rw [hfr4 x (fun h => hx (by simp at h; rcases h with h | h <;> simp [h])),
          temps_gso _ _ (fun h => hx (by simp [h])),
          temps_gso _ _ (fun h => hx (by simp [h]))]
        exact hfr2 x hx
      refine tail m3 _ le4 hm3 ⟨hr.starts, hr.queue, ?_, ?_, hr.ptnSmall⟩ ((hf1.trans hf2).trans hf3) ht4
        ?_ ?_ ?_ hfr3 ?_ ?_
      · simp only [hcl, hclsz]
      · intro i hi
        simp only [hcl]
        rw [show cl[i]! = _ from hw.get i hi]
        split
        · omega
        · rw [← hcr.hits]; exact hr.w3small i hi
      · rw [hfr4 _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj2
      · rw [hce]
        refine ⟨by simp only [hcl], fun i hi => ?_, fun x hx => ?_⟩
        · simp only [Array.size_push] at hi
          simp only [upd]
          by_cases hie : i = c.2.2.size
          · subst hie; simp
          · rw [ite_eq_right_iff.mpr (fun h => absurd h hie), hcr.touched i (by omega),
              getElem!_pos (c.2.2.push k) i (by simp; omega), getElem!_pos c.2.2 i (by omega),
              Array.getElem_push_lt (by omega)]
        · by_cases hxk : x = k
          · subst hxk
            simp only [ite_true, true_iff]
            rw [Array.getElem!_set!_self _ _ _ (by rw [hscan.touch.writes.size]; exact hkn')]
          · simp only [hxk, ite_false]
            rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hxk)]
            exact hcr.marks x hx
      · rw [hfr4 _ (by decide)]; simp only [le3, temps_gss]; rw [← hsz1]; push_cast; rfl
      · rw [hfr4 _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hii2
      · have := hcnt
        rw [hce] at this
        simp only at this
        rw [Array.getElem!_set!_self _ _ _ (by rw [hclsz]; exact hj)] at this
        simp only [hcl]; omega

end NautyVerified.Proofs.Sparse.Refine.Nontrivial

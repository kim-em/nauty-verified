import NautyVerified.Proofs.Sparse.Refine.Trivial.CellModel

/-!
# The bookkeeping after a touched cell

`(t748 = v2 != v3 && v2 != v1); fixT` computes `fixRes`: when the cell
split into an untouched and a touched part, the new boundary, the cell count,
singleton cell starts, the code and the activation of the smaller part.
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

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {u : RefineSt n} {S : Scr}

/-- The state before the activation in `fixRes`'s split case. -/
abbrev fixMid (level first v2 v3 : Nat) (u : RefineSt n) : RefineSt n :=
  ({ u with
    numcells := u.numcells + 1, ptn := u.ptn.set! (v2 - 1) level
    cellend := (u.cellend.set! first (v2 - 1)).set! v2 (v3 - 1)
    cellstart :=
      if (v3 == v2 + 1) = true then
        (if (v2 == first + 1) = true then u.cellstart.set! u.lab[first]! n else u.cellstart).set!
          u.lab[v2]! n
      else if (v2 == first + 1) = true then u.cellstart.set! u.lab[first]! n else u.cellstart } :
    RefineSt n).hash v2

/-- The activation in `fixRes`'s split case. -/
abbrev fixPush (first v2 v3 : Nat) (u w : RefineSt n) : RefineSt n :=
  if (decide (v2 - first ≤ v3 - v2) && !u.active.mem first) = true then w.push first else w.push v2

theorem fixRes_true (level first v2 v3 : Nat) (u : RefineSt n) (h : (v2 != v3 && v2 != first) = true) :
    fixRes level first v2 v3 u = fixPush first v2 v3 u (fixMid level first v2 v3 u) := by
  unfold fixRes
  rw [ite_eq_left h]

/-- The temporaries the bookkeeping assigns besides `longcode` and `nactive`. -/
abbrev fixTemps : List ident := [idOf 745, idOf 746, idOf 747, idOf 748]

/-- The test and `fixT`. -/
abbrev fixStmt : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Ebinop .One (tv id.«v2») (tv id.«v3») tint)
      (sk (.Sset (idOf 748) (.Ecast (.Ebinop .One (tv id.«v2») (tv id.«v1») tint) tbool)))
      (.Sset (idOf 748) (ci 0 tint))))
    fixT

theorem wp_fix {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G u S)
    (hr : Rep L u S) (ht : Tmp le L u) {first v2 v3 : Nat}
    (hv1 : PTree.get id.«v1» le = some (.Vint (ir first)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir v2)))
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir v3)))
    (hfv : first ≤ v2) (h23 : v2 ≤ v3) (h3n : v3 ≤ n) (hfn : first < n)
    (hls : u.lab.size = n) (hlb : ∀ i < n, u.lab[i]! < n) (hss : u.cellstart.size = n)
    (hps : u.ptn.size = n) (hcode : u.longcode < 2 ^ 62)
    (hq : (fixRes L.level first v2 v3 u).queue.size ≤ n)
    (hnc : (fixRes L.level first v2 v3 u).numcells < 2147483648)
    (hQ : ∀ le' m' S', Mem m' L G (fixRes L.level first v2 v3 u) S' →
      Rep L (fixRes L.level first v2 v3 u) S' → Tmp le' L (fixRes L.level first v2 v3 u) →
      S'.w3 = S.w3 → S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 →
      S'.st2 = S.st2 → S'.mk2 = S.mk2 → Frame L m m' →
      (∀ x, x ∉ fixTemps → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F fixStmt Q empty_env le m := by
  have hnl := hok.nlt
  have hlv := hok.levlt
  wp_step; wp_step; wp_step
  refine wp_if_ob (b := !decide ((v2 : Int) = v3)) (eval_nei (eval_tv hv2) rfl (eval_tv hv3) rfl
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
  by_cases h23e : v2 = v3
  · have hfr : fixRes L.level first v2 v3 u = u := by
      unfold fixRes; simp [h23e]
    simp only [h23e, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    refine wp_if_ob (b := false) (by simp only [Exec.evalExpr, temps_gss]; rfl) rfl ?_
    simp only [Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [E0_append]
    rw [hfr] at hQ
    exact hQ _ m S hm hr (ht.set _ (by decide)) rfl rfl rfl rfl rfl rfl (Frame.refl _ _)
      fun x hx _ _ => temps_gso _ _ (fun h => hx (h ▸ by simp))
  · simp only [show decide ((v2 : Int) = v3) = false by simp; omega, Bool.not_false, ite_true]
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, eval_nei (eval_tv hv2) rfl (eval_tv hv1) rfl ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    simp only [typeof, cast_b]
    let le1 := PTree.set (idOf 748) (Val.of_bool (!decide ((v2 : Int) = first))) le
    refine wp_if_ob (b := !decide ((v2 : Int) = first)) (eval_tv (temps_gss _ _ _)) rfl ?_
    have ht1 : Tmp le1 L u := ht.set _ (by decide)
    by_cases hv2f : v2 = first
    · have hfr : fixRes L.level first v2 v3 u = u := by
        unfold fixRes; simp [hv2f]
      simp only [hv2f, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      apply wp_skip
      rw [hfr] at hQ
      exact hQ _ m S hm hr (ht.set _ (by decide)) rfl rfl rfl rfl rfl rfl (Frame.refl _ _)
        fun x hx _ _ => temps_gso _ _ (fun h => hx (h ▸ by simp))
    · simp only [show decide ((v2 : Int) = first) = false by simp; omega, Bool.not_false, ite_true]
      have hcond : (v2 != v3 && v2 != first) = true := by simp; omega
      have hfr := fixRes_true L.level first v2 v3 u hcond
      rw [hfr] at hq hnc hQ
      have hnc' : u.numcells + 1 < 2147483648 := by
        have h1 : u.numcells + 1 ≤ (fixMid L.level first v2 v3 u).numcells := by simp [fixMid, RefineSt.hash]
        have h2 : (fixMid L.level first v2 v3 u).numcells ≤ (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)).numcells := by
          unfold fixPush; split <;> simp [RefineSt.push]
        omega
      have ht1 : Tmp (PTree.set (idOf 748) (Val.of_bool true) le) L u := ht.set _ (by decide)
      wp_step; wp_step; wp_step
      refine wp_nc hok hm ht1 (x := u.numcells + 1)
        (rhs := .Ebinop .Oadd (.Ederef (pi id.numcells) tint) (ci 1 tint) tint) ?_ rfl ?_
      · rw [eval_binop (eval_nc hm ht1) rfl]; simp only [typeof, cop, ir_add]; push_cast; rfl
      intro m1 hm1 hf1
      let le1 := PTree.set (idOf 748) (Val.of_bool true) le
      have hv1' : PTree.get id.«v1» le1 = some (.Vint (ir first)) := by
        rw [temps_gso _ _ (by decide)]; exact hv1
      have hv2' : PTree.get id.«v2» le1 = some (.Vint (ir v2)) := by
        rw [temps_gso _ _ (by decide)]; exact hv2
      have hv3' : PTree.get id.«v3» le1 = some (.Vint (ir v3)) := by
        rw [temps_gso _ _ (by decide)]; exact hv3
      have ht1' : Tmp le1 L { u with numcells := u.numcells + 1 } := ht1.congr rfl rfl
      have hcs : ∀ (c : Nat), c < n → ∀ (w : Nat → val) (cs : Array Nat), cs.size = n →
          (∀ v < n, w v = .Vint (ir cs[v]!)) →
          ∀ v < n, upd w c (.Vint (ir n)) v = .Vint (ir (cs.set! c n)[v]!) := by
        intro c hc w cs hcs' hw v hv
        by_cases he : v = c
        · subst he; rw [upd_same, Array.getElem!_set!_self _ _ _ (by omega)]
        · rw [upd_ne _ _ he, Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]; exact hw v hv
      -- the tail, from the cell starts `st` on
      have tail : ∀ (Q' : Post), (∀ le' m' S', Mem m' L G (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) S' →
          Rep L (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) S' →
          Tmp le' L (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) →
          S'.w3 = S.w3 → S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 →
          S'.st2 = S.st2 → S'.mk2 = S.mk2 → Frame L m m' →
          (∀ x, x ∉ fixTemps → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le' = PTree.get x le) →
          Q'.normal E0 empty_env le' m') →
          ∀ (m3 : mem) (S3 : Scr),
          Mem m3 L G { u with numcells := u.numcells + 1, cellstart := (fixMid L.level first v2 v3 u).cellstart } S3 →
          Rep L { u with numcells := u.numcells + 1, cellstart := (fixMid L.level first v2 v3 u).cellstart } S3 →
          S3.w3 = S.w3 → S3.w4 = S.w4 → S3.st1 = S.st1 → S3.mk1 = S.mk1 → S3.st2 = S.st2 →
          S3.mk2 = S.mk2 → Frame L m m3 →
          Wp xi sge F
            (.Ssequence (sk (.Sassign (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint))
              (tv id.«level»)))
            (.Ssequence (sk (mash (tv id.«v2»)))
            (.Ssequence
              (sk (.Sifthenelse (.Ebinop .Ole (.Ebinop .Osub (tv id.«v2») (tv id.«v1») tint)
                  (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint) tint)
                (sk (.Sset (idOf 747) (.Ecast (.Eunop .Onotbool
                  (Set.isElement id.active id.«nausparse:bit» (tv id.«v1»)) tint) tbool)))
                (.Sset (idOf 747) (ci 0 tint))))
              (.Sifthenelse (tv (idOf 747))
                (.Ssequence (Set.addElementB id.active id.«nausparse:bit» (tv id.«v1»))
                  (.Ssequence (.Ssequence (sk (.Sset (idOf 745) (tv id.nactive)))
                    (.Sset id.nactive (.Ebinop .Oadd (tv (idOf 745)) (ci 1 tint) tint)))
                    (.Sassign (gix id.«nausparse:work2» (tv (idOf 745))) (tv id.«v1»))))
                (.Ssequence (Set.addElementB id.active id.«nausparse:bit» (tv id.«v2»))
                  (.Ssequence (.Ssequence (sk (.Sset (idOf 746) (tv id.nactive)))
                    (.Sset id.nactive (.Ebinop .Oadd (tv (idOf 746)) (ci 1 tint) tint)))
                    (.Sassign (gix id.«nausparse:work2» (tv (idOf 746))) (tv id.«v2»))))))))
            Q' empty_env le1 m3 := by
        intro Q' hQ' m3 S3 hm3 hr3 e3 e4 e5 e6 e7 e8 hf3
        have ht3 : Tmp le1 L
            { u with numcells := u.numcells + 1, cellstart := (fixMid L.level first v2 v3 u).cellstart } :=
          ht1.congr rfl rfl
        have hv21 : 1 ≤ v2 := by omega
        wp_step; wp_step; wp_step
        refine wp_ptn hok hm3 ht3 (c := v2 - 1) (x := L.level) ?_ rfl (by omega) (eval_tv ht3.level)
          rfl hps ?_
        · rw [eval_binop (eval_tv hv2') rfl]; simp only [typeof, cop, ir_sub]
          rw [show ((v2 - 1 : Nat) : Int) = (v2 : Int) - 1 by omega]
        intro m4 hm4 hf4
        simp only [E0_append]
        wp_step; wp_step; wp_step
        refine wp_mash ht3.longcode hcode (eval_tv hv2') rfl (by omega) ?_
        let le2 := PTree.set id.longcode (.Vlong (lr (Hex.GraphIso.Nauty.mash u.longcode v2 : Nat))) le1
        have ht4 : Tmp le2 L (fixMid L.level first v2 v3 u) := (ht3.hash v2).congr rfl rfl
        have hm5 : Mem m4 L G (fixMid L.level first v2 v3 u) S3 := hm4.congr rfl rfl rfl rfl
        have hr5 : Rep L (fixMid L.level first v2 v3 u) S3 := by
          refine ⟨hr3.starts, hr3.queue, hr3.w3size, hr3.w3small, fun i hi => ?_⟩
          show (u.ptn.set! (v2 - 1) L.level)[i]! < 2147483648
          by_cases he : i = v2 - 1
          · subst he; rw [Array.getElem!_set!_self _ _ _ (by omega)]; omega
          · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)]; exact hr.ptnSmall i hi
        have hv1'' : PTree.get id.«v1» le2 = some (.Vint (ir first)) := by
          rw [temps_gso _ _ (by decide)]; exact hv1'
        have hv2'' : PTree.get id.«v2» le2 = some (.Vint (ir v2)) := by
          rw [temps_gso _ _ (by decide)]; exact hv2'
        have hv3'' : PTree.get id.«v3» le2 = some (.Vint (ir v3)) := by
          rw [temps_gso _ _ (by decide)]; exact hv3'
        have hsub : ∀ {a b : ident} {x y : Nat}, PTree.get a le2 = some (.Vint (ir x)) →
            PTree.get b le2 = some (.Vint (ir y)) →
            Exec.evalExpr sge empty_env le2 m4 (.Ebinop .Osub (tv a) (tv b) tint) =
              some (.Vint (ir ((x : Int) - y))) := by
          intro a b x y ha hb
          rw [eval_binop (eval_tv ha) (eval_tv hb)]; simp only [typeof, cop, ir_sub]
        simp only [E0_append]
        wp_step; wp_step; wp_step
        refine wp_if_ob (b := decide ((v2 : Int) - first ≤ v3 - v2))
          (eval_lei (hsub hv2'' hv1'') rfl (hsub hv3'' hv2'') rfl ⟨by omega, by omega⟩
            ⟨by omega, by omega⟩) rfl ?_
        have hqm : (fixMid L.level first v2 v3 u).queue.size < n := by
          have : (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)).queue.size =
              (fixMid L.level first v2 v3 u).queue.size + 1 := by
            unfold fixPush; split <;> simp [RefineSt.push]
          omega
        have fin : ∀ (b : Bool), b = (decide (v2 - first ≤ v3 - v2) && !u.active.mem first) →
            Wp xi sge F
              (.Sifthenelse (tv (idOf 747))
                (.Ssequence (Set.addElementB id.active id.«nausparse:bit» (tv id.«v1»))
                  (.Ssequence (.Ssequence (sk (.Sset (idOf 745) (tv id.nactive)))
                    (.Sset id.nactive (.Ebinop .Oadd (tv (idOf 745)) (ci 1 tint) tint)))
                    (.Sassign (gix id.«nausparse:work2» (tv (idOf 745))) (tv id.«v1»))))
                (.Ssequence (Set.addElementB id.active id.«nausparse:bit» (tv id.«v2»))
                  (.Ssequence (.Ssequence (sk (.Sset (idOf 746) (tv id.nactive)))
                    (.Sset id.nactive (.Ebinop .Oadd (tv (idOf 746)) (ci 1 tint) tint)))
                    (.Sassign (gix id.«nausparse:work2» (tv (idOf 746))) (tv id.«v2»)))))
              Q' empty_env (PTree.set (idOf 747) (Val.of_bool b) le2) m4 := by
          intro b hb
          have ht5 : Tmp (PTree.set (idOf 747) (Val.of_bool b) le2) L (fixMid L.level first v2 v3 u) :=
            ht4.set _ (by decide)
          refine wp_if_ob (b := b) (eval_tv (temps_gss _ _ _)) rfl ?_
          have hfin : ∀ le' m' S', Mem m' L G (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) S' →
              Rep L (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) S' →
              Tmp le' L (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) →
              S'.w3 = S3.w3 → S'.w4 = S3.w4 → S'.st1 = S3.st1 → S'.mk1 = S3.mk1 →
              S'.st2 = S3.st2 → S'.mk2 = S3.mk2 → Frame L m4 m' →
              (∀ y, y ∉ [idOf 745, idOf 746] → y ≠ id.nactive →
                PTree.get y le' = PTree.get y (PTree.set (idOf 747) (Val.of_bool b) le2)) →
              Q'.normal E0 empty_env le' m' := by
            intro le' m' S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
            refine hQ' le' m' S' a1 a2 a3 (a4.trans e3) (a5.trans e4) (a6.trans e5) (a7.trans e6)
              (a8.trans e7) (a9.trans e8) (hf3.trans (hf4.trans a10)) fun x hx hl hn => ?_
            simp only [fixTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
            rw [a11 x (by simp; exact ⟨hx.1, hx.2.1⟩) hn, temps_gso _ _ hx.2.2.1, temps_gso _ _ hl,
              temps_gso _ _ hx.2.2.2]
          by_cases hbt : b = true
          · have hp : fixPush first v2 v3 u (fixMid L.level first v2 v3 u) =
                (fixMid L.level first v2 v3 u).push first := by
              unfold fixPush; rw [ite_eq_left (by rw [← hb]; exact hbt)]
            rw [hp] at hfin
            subst hbt
            simp only [ite_true]
            refine wp_push hok hm5 hr5 ht5 (X := id.«v1») (T := idOf 745) (x := first)
              (by rw [temps_gso _ _ (by decide)]; exact hv1'') hfn hqm (by decide) (by decide) (by decide)
              fun le' m' S' a1 a2 a3 _ a5 a6 a7 a8 a9 a10 a11 a12 => hfin le' m' S' a1 a2 a3 a5 a6 a7 a8
                a9 a10 a11 fun y hy hn => a12 y (fun h => hy (by simp [h])) hn
          · have hp : fixPush first v2 v3 u (fixMid L.level first v2 v3 u) =
                (fixMid L.level first v2 v3 u).push v2 := by
              unfold fixPush; rw [ite_eq_right (by rw [← hb]; simpa using hbt)]
            rw [hp] at hfin
            obtain rfl : b = false := by simpa using hbt
            simp only [Bool.false_eq_true, ite_false]
            refine wp_push hok hm5 hr5 ht5 (X := id.«v2») (T := idOf 746) (x := v2)
              (by rw [temps_gso _ _ (by decide)]; exact hv2'') (by omega) hqm (by decide) (by decide) (by decide)
              fun le' m' S' a1 a2 a3 _ a5 a6 a7 a8 a9 a10 a11 a12 => hfin le' m' S' a1 a2 a3 a5 a6 a7 a8
                a9 a10 a11 fun y hy hn => a12 y (fun h => hy (by simp [h])) hn
        by_cases hle : (v2 : Int) - first ≤ v3 - v2
        · simp only [show decide ((v2 : Int) - first ≤ v3 - v2) = true by simpa using hle, ite_true]
          wp_step; wp_step
          apply wp_set_eval
          rw [Exec.evalExpr, Exec.evalExpr, eval_isAct hok hm5 ht4 (eval_tv hv1'') rfl hfn]
          simp only [typeof, notbool_ob, cast_b]
          exact fin _ (by
            have : decide (v2 - first ≤ v3 - v2) = true := by simp; omega
            rw [this]; rfl)
        · simp only [show decide ((v2 : Int) - first ≤ v3 - v2) = false by simpa using hle,
            Bool.false_eq_true, ite_false]
          apply wp_set_eval
          simp only [Exec.evalExpr]
          exact fin false (by
            have : decide (v2 - first ≤ v3 - v2) = false := by simp; omega
            rw [this]; rfl)
      have hQ' := hQ
      have mid : ∀ (Q' : Post), (∀ le' m' S', Mem m' L G (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) S' →
          Rep L (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) S' →
          Tmp le' L (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) →
          S'.w3 = S.w3 → S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 →
          S'.st2 = S.st2 → S'.mk2 = S.mk2 → Frame L m m' →
          (∀ x, x ∉ fixTemps → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le' = PTree.get x le) →
          Q'.normal E0 empty_env le' m') →
          ∀ (m2 : mem) (S2 : Scr) (cs : Array Nat), cs.size = n →
          cs = (if (v2 == first + 1) = true then u.cellstart.set! u.lab[first]! n else u.cellstart) →
          Mem m2 L G { u with numcells := u.numcells + 1, cellstart := cs } S2 →
          Rep L { u with numcells := u.numcells + 1, cellstart := cs } S2 →
          S2.w3 = S.w3 → S2.w4 = S.w4 → S2.st1 = S.st1 → S2.mk1 = S.mk1 → S2.st2 = S.st2 →
          S2.mk2 = S.mk2 → Frame L m m2 →
          Wp xi sge F (.Ssequence
            (sk (.Sifthenelse (.Ebinop .Oeq (tv id.«v3») (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint) tint)
              (sk (.Sassign (gix id.«nausparse:work1» (ix id.lab (tv id.«v2»))) (tv id.n))) .Sskip))
            (.Ssequence (sk (.Sassign (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint))
              (tv id.«level»)))
            (.Ssequence (sk (mash (tv id.«v2»)))
            (.Ssequence
              (sk (.Sifthenelse (.Ebinop .Ole (.Ebinop .Osub (tv id.«v2») (tv id.«v1») tint)
                  (.Ebinop .Osub (tv id.«v3») (tv id.«v2») tint) tint)
                (sk (.Sset (idOf 747) (.Ecast (.Eunop .Onotbool
                  (Set.isElement id.active id.«nausparse:bit» (tv id.«v1»)) tint) tbool)))
                (.Sset (idOf 747) (ci 0 tint))))
              (.Sifthenelse (tv (idOf 747))
                (.Ssequence (Set.addElementB id.active id.«nausparse:bit» (tv id.«v1»))
                  (.Ssequence (.Ssequence (sk (.Sset (idOf 745) (tv id.nactive)))
                    (.Sset id.nactive (.Ebinop .Oadd (tv (idOf 745)) (ci 1 tint) tint)))
                    (.Sassign (gix id.«nausparse:work2» (tv (idOf 745))) (tv id.«v1»))))
                (.Ssequence (Set.addElementB id.active id.«nausparse:bit» (tv id.«v2»))
                  (.Ssequence (.Ssequence (sk (.Sset (idOf 746) (tv id.nactive)))
                    (.Sset id.nactive (.Ebinop .Oadd (tv (idOf 746)) (ci 1 tint) tint)))
                    (.Sassign (gix id.«nausparse:work2» (tv (idOf 746))) (tv id.«v2»)))))))))
            Q' empty_env le1 m2 := by
        intro Q' hQ' m2 S2 cs hcsz hcse hm2 hr2 e3 e4 e5 e6 e7 e8 hf2
        have ht2 : Tmp le1 L { u with numcells := u.numcells + 1, cellstart := cs } := ht1.congr rfl rfl
        wp_step; wp_step; wp_step
        refine wp_if_ob (b := decide ((v3 : Int) = v2 + 1)) (eval_eqi (eval_tv hv3') rfl
          (eval_inc hv2') rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
        by_cases hB : v3 = v2 + 1
        · simp only [show decide ((v3 : Int) = v2 + 1) = true by simp; omega, ite_true]
          wp_step; wp_step
          refine wp_w1 hok hm2 (eval_lab hok hm2 ht2 (eval_tv hv2') rfl (by omega)) rfl
            (show u.lab[v2]! < L.c1 by have := hlb v2 (by omega); have := hok.c1; omega)
            (eval_tv ht2.n) rfl ?_
          intro m3 hm3 hf3
          simp only [E0_append]
          refine tail Q' hQ' m3 { S2 with w1 := upd S2.w1 u.lab[v2]! (.Vint (ir n)) } ?_ ?_
            e3 e4 e5 e6 e7 e8 (hf2.trans hf3)
          · refine hm3.congr rfl rfl rfl rfl
          · refine ⟨fun v hv => ?_, hr2.queue, hr2.w3size, hr2.w3small, hr2.ptnSmall⟩
            have := hcs u.lab[v2]! (hlb v2 (by omega)) S2.w1 cs hcsz hr2.starts v hv
            simp only [fixMid, RefineSt.hash, show (v3 == v2 + 1) = true by simp; omega, ite_true, ← hcse]
            exact this
        · simp only [show decide ((v3 : Int) = v2 + 1) = false by simp; omega, Bool.false_eq_true,
            ite_false]
          apply wp_skip
          simp only [E0_append]
          refine tail Q' hQ' m2 S2 ?_ ?_ e3 e4 e5 e6 e7 e8 hf2
          · refine hm2.congr rfl rfl rfl rfl
          · have hc : (fixMid L.level first v2 v3 u).cellstart = cs := by
              simp only [fixMid, RefineSt.hash, show (v3 == v2 + 1) = false by simp; omega,
                Bool.false_eq_true, ite_false, ← hcse]
            rw [hc]; exact hr2
      simp only [E0_append]
      wp_step; wp_step; wp_step
      refine wp_if_ob (b := decide ((v2 : Int) = first + 1)) (eval_eqi (eval_tv hv2') rfl
        (eval_inc hv1') rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
      have hQ0 : ∀ le' m' S', Mem m' L G (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) S' →
          Rep L (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) S' →
          Tmp le' L (fixPush first v2 v3 u (fixMid L.level first v2 v3 u)) →
          S'.w3 = S.w3 → S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 →
          S'.st2 = S.st2 → S'.mk2 = S.mk2 → Frame L m m' →
          (∀ x, x ∉ fixTemps → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le' = PTree.get x le) →
          (Q.after E0).normal E0 empty_env le' m' := by
        intro le' m' S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
        simpa [Post.after] using hQ le' m' S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
      by_cases hA : v2 = first + 1
      · simp only [show decide ((v2 : Int) = first + 1) = true by simp; omega, ite_true]
        wp_step; wp_step
        refine wp_w1 hok hm1 (eval_lab hok hm1 ht1' (eval_tv hv1') rfl hfn) rfl
          (show u.lab[first]! < L.c1 by have := hlb first hfn; have := hok.c1; omega)
          (eval_tv ht1'.n) rfl ?_
        intro m2 hm2 hf2
        simp only [E0_append]
        refine mid _ hQ0 m2 { S with w1 := upd S.w1 u.lab[first]! (.Vint (ir n)) }
          (u.cellstart.set! u.lab[first]! n) (by simp [hss])
          (by simp [show (v2 == first + 1) = true by simp; omega]) (hm2.congr rfl rfl rfl rfl) ?_
          rfl rfl rfl rfl rfl rfl (hf1.trans hf2)
        exact ⟨hcs _ (hlb first hfn) _ _ hss hr.starts, hr.queue, hr.w3size, hr.w3small, hr.ptnSmall⟩
      · simp only [show decide ((v2 : Int) = first + 1) = false by simp; omega, Bool.false_eq_true,
          ite_false]
        apply wp_skip
        simp only [E0_append]
        exact mid _ hQ0 m1 S u.cellstart hss
          (by simp [show (v2 == first + 1) = false by simp; omega]) (hm1.congr rfl rfl rfl rfl)
          ⟨hr.starts, hr.queue, hr.w3size, hr.w3small, hr.ptnSmall⟩ rfl rfl rfl rfl rfl rfl hf1

end NautyVerified.Proofs.Sparse.Refine.Trivial

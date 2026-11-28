import NautyVerified.Proofs.Sparse.Refine.Count.Sort

/-!
# The first two fragments installed

`wp_install`: the cell starts of the first two fragments, `++*numcells` and
the boundary `ptn[v2-1] = level` give HexGraphIso's `install2`.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- `CELLSTART[lab[x]] = rhs`. -/
theorem wp_startAt {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (hr : Rep L t S) (ht : Tmp le L t) (hcs : t.cellstart.size = n) {x : ident} {c : Nat}
    (hx : PTree.get x le = some (.Vint (ir c))) (hc : c < n) (hl : t.lab[c]! < n) {rhs : expr} {y : Nat}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir y))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G { t with cellstart := t.cellstart.set! t.lab[c]! y }
        { S with w1 := upd S.w1 t.lab[c]! (.Vint (ir y)) } →
      Rep L { t with cellstart := t.cellstart.set! t.lab[c]! y }
        { S with w1 := upd S.w1 t.lab[c]! (.Vint (ir y)) } → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge F (.Sassign (gix id.«nausparse:work1» (ix id.lab (tv x))) rhs) Q empty_env le m := by
  refine wp_w1F hok hm (eval_lab hok hm ht (show Exec.evalExpr sge empty_env le m (tv x) = _ from hx) rfl hc)
    rfl (by have := hok.c1; omega) hrhs hrty ?_
  intro m' hm' hf
  exact hQ m' (hm'.congr rfl rfl rfl rfl) (Rep.setStart hr hcs hl) hf

/-- The installation, up to the case split on the third fragment. -/
abbrev installS (rest : statement) : statement :=
  .Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Oeq (tv id.«v2») (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint) tint)
        (sk (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«v1»))) (tv id.«n»)))
        .Sskip))
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .Oeq (tv id.«v3») (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint) tint)
          (sk (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«v2»))) (tv id.«n»)))
          (.Ssequence (sk (.Sset id.«k» (tv id.«v2»))) startsD)))
      (.Ssequence
        (sk
          (.Sassign
            (.Ederef (pi id.«numcells») tint)
            (.Ebinop .Oadd (.Ederef (pi id.«numcells») tint) (ci 1 tint) tint)))
        (.Ssequence
          (sk
            (.Sassign (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint)) (tv id.«level»)))
          rest)))

theorem eval_eqInc {le : temp_env} {m : mem} {a b : ident} {A B : Nat} (hA : A < 1073741824)
    (hB : B < 1073741824) (ha : PTree.get a le = some (.Vint (ir A)))
    (hb : PTree.get b le = some (.Vint (ir B))) :
    Exec.evalExpr sge empty_env le m (.Ebinop .Oeq (tv a) (.Ebinop .Oadd (tv b) (ci 1 tint) tint) tint) =
      some (Val.of_bool (decide (A = B + 1))) := by
  rw [eval_binop (show Exec.evalExpr sge empty_env le m (tv a) = _ from ha) (eval_inc hb)]
  simp only [typeof, cop]
  rw [ir_eq (a := (A : Int)) (b := ((B + 1 : Nat) : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  congr 2
  exact decide_eq_decide.2 (by omega)

theorem foldl_set_size (lab : Array Nat) (v : Nat) :
    ∀ (l : List Nat) (a : Array Nat), (l.foldl (fun a k => a.set! lab[k]! v) a).size = a.size
  | [], _ => rfl
  | k :: l, a => by rw [List.foldl_cons, foldl_set_size lab v l]; simp

theorem wp_install {Q : Post} {le : temp_env} {m : mem} {rest : statement} (hok : Ok n L)
    (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {first v2 v3 : Nat}
    (h12 : first + 1 ≤ v2) (h23 : v2 ≤ v3) (h3 : v3 ≤ n) (hlab : ∀ q < n, t.lab[q]! < n)
    (hcs : t.cellstart.size = n) (hps : t.ptn.size = n)
    (hv1 : PTree.get id.«v1» le = some (.Vint (ir first)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir v2)))
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir v3)))
    (hQ : ∀ le' m' S', Mem m' L G (install2 L.level first t v2 v3) S' →
      Rep L (install2 L.level first t v2 v3) S' → Tmp le' L (install2 L.level first t v2 v3) →
      Frame L m m' → Keeps S S' → (∀ x, x ≠ id.«k» → PTree.get x le' = PTree.get x le) →
      Wp xi sge F rest Q empty_env le' m') :
    Wp xi sge F (installS rest) Q empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  -- the state after the second fragment's starts
  have hB : ∀ m1 S1 (cs1 : Array Nat), cs1.size = n →
      cs1 = (if v2 == first + 1 then t.cellstart.set! t.lab[first]! n else t.cellstart) →
      Mem m1 L G { t with cellstart := cs1 } S1 → Rep L { t with cellstart := cs1 } S1 → Frame L m m1 →
      Keeps S S1 →
      Wp xi sge F (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Oeq (tv id.«v3») (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint) tint)
            (sk (.Sassign (gix id.«nausparse:work1» (ix id.«lab» (tv id.«v2»))) (tv id.«n»)))
            (.Ssequence (sk (.Sset id.«k» (tv id.«v2»))) startsD)))
        (.Ssequence
          (sk
            (.Sassign
              (.Ederef (pi id.«numcells») tint)
              (.Ebinop .Oadd (.Ederef (pi id.«numcells») tint) (ci 1 tint) tint)))
          (.Ssequence
            (sk
              (.Sassign (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint)) (tv id.«level»)))
            rest))) Q empty_env le m1 := by
    intro m1 S1 cs1 hcs1 hcs1e hm1 hr1 hf1 hk1
    let t1 : RefineSt n := { t with cellstart := cs1 }
    have ht1 : Tmp le L t1 := ht.congr rfl rfl
    -- after the second fragment's starts, before the cell count
    have hC : ∀ le2 m2 S2 (cs2 : Array Nat), cs2.size = n →
        cs2 = (if v3 == v2 + 1 then cs1.set! t.lab[v2]! n else startsLit t.lab cs1 v2 v3) →
        Mem m2 L G { t with cellstart := cs2 } S2 → Rep L { t with cellstart := cs2 } S2 →
        Frame L m m2 → Keeps S S2 → Tmp le2 L t → (∀ x, x ≠ id.«k» → PTree.get x le2 = PTree.get x le) →
        Wp xi sge F (.Ssequence
          (sk
            (.Sassign
              (.Ederef (pi id.«numcells») tint)
              (.Ebinop .Oadd (.Ederef (pi id.«numcells») tint) (ci 1 tint) tint)))
          (.Ssequence
            (sk
              (.Sassign (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint)) (tv id.«level»)))
            rest)) Q empty_env le2 m2 := by
      intro le2 m2 S2 cs2 hcs2 hcs2e hm2 hr2 hf2 hk2 ht2 ho2
      let t2 : RefineSt n := { t with cellstart := cs2 }
      have ht2' : Tmp le2 L t2 := ht2.congr rfl rfl
      apply wp_seq
      wp_step; wp_step
      refine wp_ncF hok hm2 ht2' (x := t.numcells + 1) (by
        rw [eval_binop (eval_nc hm2 ht2') rfl]; simp only [typeof, cop, ir_add]; rfl) rfl ?_
      intro m3 hm3 hf3
      simp only [seqPost, after_E0, E0_append]
      apply wp_seq
      wp_step; wp_step
      have hv2' : PTree.get id.«v2» le2 = some (.Vint (ir v2)) := by rw [ho2 _ (by decide)]; exact hv2
      refine wp_ptnF (t := { t2 with numcells := t.numcells + 1 }) hok hm3 (ht2'.congr rfl rfl)
        (eval_dec (by omega) hv2') rfl (by omega)
        (show Exec.evalExpr sge empty_env le2 m3 (tv id.«level») = _ from ht2.level) rfl hps ?_
      intro m4 hm4 hf4
      simp only [seqPost, after_E0, E0_append]
      have hi : install2 L.level first t v2 v3 =
          { t with
            cellstart := cs2
            numcells := t.numcells + 1
            cellend := (t.cellend.set! first (v2 - 1)).set! v2 (v3 - 1)
            ptn := t.ptn.set! (v2 - 1) L.level } := by
        rw [hcs2e, hcs1e]; rfl
      refine hQ le2 m4 S2 ?_ ?_ ?_ (hf2.trans (hf3.trans hf4)) hk2 ho2
      · rw [hi]; exact hm4.congr rfl rfl rfl rfl
      · rw [hi]; have := Rep.setPtn hr2 hll (v2 - 1); exact { this with }
      · rw [hi]; exact ht2.congr rfl rfl
    have hm1' : Mem m1 L G t1 S1 := hm1
    apply wp_seq
    wp_step; wp_step
    apply wp_if_eval
    rw [eval_eqInc (by omega) (by omega) hv3 hv2]
    by_cases h32 : v3 = v2 + 1
    · simp (config := {decide := true}) only [show decide (v3 = v2 + 1) = true from decide_eq_true h32,
        Val.of_bool, cop, ite_true]
      wp_step; wp_step
      refine wp_startAt (t := t1) hok hm1' hr1 ht1 hcs1 hv2 (by omega) (hlab _ (by omega))
        (show Exec.evalExpr sge empty_env le m1 (tv id.«n») = _ from ht1.n) rfl ?_
      intro m2 hm2 hr2 hf2
      simp only [seqPost, after_E0, E0_append]
      exact hC le m2 _ (cs1.set! t.lab[v2]! n) (by simp [hcs1]) (by simp [h32]) hm2 hr2 (hf1.trans hf2)
        (hk1.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) ht (fun _ _ => rfl)
    · simp (config := {decide := true}) only [show decide (v3 = v2 + 1) = false from decide_eq_false h32,
        Val.of_bool, cop, ite_false]
      apply wp_seq
      wp_step; wp_step; wp_step
      simp only [hv2]
      have hk2 : PTree.get id.«k» (PTree.set id.«k» (.Vint (ir v2)) le) = some (.Vint (ir v2)) := temps_gss _ _ _
      refine wp_starts (t := t1) hok hm1' hr1 (ht1.set (x := id.«k») _ (by decide)) h23 h3 hlab hcs1 hk2
        (by rw [temps_gso _ _ (by decide)]; exact hv2) (by rw [temps_gso _ _ (by decide)]; exact hv3) ?_
      intro le2 m2 w hm2 hr2 hf2 _ ho2
      simp only [seqPost, after_E0, E0_append]
      refine hC le2 m2 _ (startsLit t.lab cs1 v2 v3) ?_ (by simp [h32]) hm2 hr2 (hf1.trans hf2)
        (hk1.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) ((ht.set (x := id.«k») _ (by decide)).frame
          (ws := [id.«k»]) (fun x hx => ho2 x (by simpa using hx)) (by decide))
        (fun x hx => by rw [ho2 x hx, temps_gso _ _ hx])
      rw [startsLit_eq, foldl_set_size]; exact hcs1
  -- the first fragment's start
  apply wp_seq
  wp_step; wp_step
  apply wp_if_eval
  rw [eval_eqInc (by omega) (by omega) hv2 hv1]
  by_cases h21 : v2 = first + 1
  · simp (config := {decide := true}) only [show decide (v2 = first + 1) = true from decide_eq_true h21,
      Val.of_bool, cop, ite_true]
    wp_step; wp_step
    refine wp_startAt hok hm hr ht hcs hv1 (by omega) (hlab _ (by omega))
      (show Exec.evalExpr sge empty_env le m (tv id.«n») = _ from ht.n) rfl ?_
    intro m1 hm1 hr1 hf1
    simp only [seqPost, after_E0, E0_append]
    exact hB m1 _ _ (by simp [hcs]) (by simp [h21]) hm1 hr1 hf1 ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp (config := {decide := true}) only [show decide (v2 = first + 1) = false from decide_eq_false h21,
      Val.of_bool, cop, ite_false]
    apply wp_skip
    exact hB m S t.cellstart hcs (by simp [h21]) hm hr (Frame.refl _ _) (Keeps.refl _)

end NautyVerified.Proofs.Sparse.Refine.Count

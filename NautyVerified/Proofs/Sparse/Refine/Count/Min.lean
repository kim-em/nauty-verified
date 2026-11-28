import NautyVerified.Proofs.Sparse.Refine.Count.RunLoop

set_option linter.unusedSimpArgs false

/-!
# The three-way insertion

`wp_min`: the do-while over `j` from `v2` to the cell's end computes
HexGraphIso's `minima` (a fold of `minStep`). The C's `w2` starts at
`NAUTY_INFINITY` = 2000000002 where the model's starts at `n + 2`; every key
is below `n + 2`, so the comparisons agree (`cw`).
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse


variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The insertion's case analysis on `w3`. -/
abbrev minCases : statement :=
  (.Sifthenelse
    (.Ebinop .Oeq (tv id.«w3») (tv id.«w1») tint)
    (.Ssequence
      (sk (.Sassign (ix id.«lab» (tv id.«j»)) (ix id.«lab» (tv id.«v3»))))
      (.Ssequence
        (sk (.Sassign (ix id.«lab» (tv id.«v3»)) (ix id.«lab» (tv id.«v2»))))
        (.Ssequence
          (sk (.Sassign (ix id.«lab» (tv id.«v2»)) (tv id.«lj»)))
          (.Ssequence
            (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint)))
            (sk (.Sset id.«v3» (.Ebinop .Oadd (tv id.«v3») (ci 1 tint) tint)))))))
    (sk
      (.Sifthenelse
        (.Ebinop .Oeq (tv id.«w3») (tv id.«w2») tint)
        (.Ssequence
          (sk (.Sassign (ix id.«lab» (tv id.«j»)) (ix id.«lab» (tv id.«v3»))))
          (.Ssequence
            (sk (.Sassign (ix id.«lab» (tv id.«v3»)) (tv id.«lj»)))
            (sk (.Sset id.«v3» (.Ebinop .Oadd (tv id.«v3») (ci 1 tint) tint)))))
        (sk
          (.Sifthenelse
            (.Ebinop .Olt (tv id.«w3») (tv id.«w1») tint)
            (.Ssequence
              (sk (.Sassign (ix id.«lab» (tv id.«j»)) (ix id.«lab» (tv id.«v2»))))
              (.Ssequence
                (sk (.Sassign (ix id.«lab» (tv id.«v2»)) (ix id.«lab» (tv id.«v1»))))
                (.Ssequence
                  (sk (.Sassign (ix id.«lab» (tv id.«v1»)) (tv id.«lj»)))
                  (.Ssequence
                    (sk (.Sset id.«v3» (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint)))
                    (.Ssequence
                      (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint)))
                      (.Ssequence
                        (sk (.Sset id.«w2» (tv id.«w1»)))
                        (sk (.Sset id.«w1» (tv id.«w3»)))))))))
            (sk
              (.Sifthenelse
                (.Ebinop .Olt (tv id.«w3») (tv id.«w2») tint)
                (.Ssequence
                  (sk (.Sassign (ix id.«lab» (tv id.«j»)) (ix id.«lab» (tv id.«v2»))))
                  (.Ssequence
                    (sk (.Sassign (ix id.«lab» (tv id.«v2»)) (tv id.«lj»)))
                    (.Ssequence
                      (sk (.Sset id.«v3» (.Ebinop .Oadd (tv id.«v2») (ci 1 tint) tint)))
                      (sk (.Sset id.«w2» (tv id.«w3»))))))
                .Sskip)))))))

/-- The insertion's loop step: `j++` and the test of `ptn[j]`. -/
abbrev minIter (t : Common.AST.ident) : statement :=
  (.Ssequence
    (.Ssequence (sk (.Sset t (tv id.«j»))) (.Sset id.«j» (.Ebinop .Oadd (tv t) (ci 1 tint) tint)))
    (.Sifthenelse (.Ebinop .Ogt (ix id.«ptn» (tv t)) (tv id.«level») tint) .Sskip .Sbreak))

theorem minG_eq (t : Common.AST.ident) : minG t =
    .Sloop (.Ssequence (sk (.Sset id.«lj» (ix id.«lab» (tv id.«j»))))
      (.Ssequence (sk (.Sset id.«w3» (gix id.«nausparse:work3» (tv id.«lj»)))) (sk minCases)))
      (minIter t) := rfl

/-- The C's value of the model's second key: `NAUTY_INFINITY` for the cap. -/
def cw (n w : Nat) : Nat := if w = n + 2 then 2000000002 else w

/-- `lab'` permutes `lab` inside `[lo, hi)` and agrees outside. -/
structure Win (lab lab' : Array Nat) (lo hi : Nat) : Prop where
  size : lab'.size = lab.size
  out : ∀ q, q < lo ∨ hi ≤ q → lab'[q]! = lab[q]!
  inn : ∀ q, lo ≤ q → q < hi → ∃ q', lo ≤ q' ∧ q' < hi ∧ lab'[q]! = lab[q']!

theorem Win.refl (lab : Array Nat) (lo hi : Nat) : Win lab lab lo hi :=
  ⟨rfl, fun _ _ => rfl, fun q h1 h2 => ⟨q, h1, h2, rfl⟩⟩

/-- Writing a window entry into a window position. -/
theorem Win.set {lab lab' : Array Nat} {lo hi : Nat} (h : Win lab lab' lo hi) {x v : Nat}
    (hx1 : lo ≤ x) (hx2 : x < hi) (hv : ∃ q', lo ≤ q' ∧ q' < hi ∧ v = lab[q']!) :
    Win lab (lab'.set! x v) lo hi := by
  refine ⟨by simp [h.size], fun q hq => ?_, fun q h1 h2 => ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]; exact h.out q hq
  · by_cases hqx : q = x
    · subst hqx
      by_cases hs : q < lab'.size
      · rw [Array.getElem!_set!_self _ _ _ hs]; exact hv
      · rw [show lab'.set! q v = lab' by simp [Array.set!, Array.setIfInBounds, hs]]
        exact h.inn q h1 h2
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hqx)]; exact h.inn q h1 h2

/-- An entry of a window. -/
theorem Win.get {lab lab' : Array Nat} {lo hi : Nat} (h : Win lab lab' lo hi) {x : Nat}
    (hx1 : lo ≤ x) (hx2 : x < hi) : ∃ q', lo ≤ q' ∧ q' < hi ∧ lab'[x]! = lab[q']! := h.inn x hx1 hx2

end NautyVerified.Proofs.Sparse.Refine.Count

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

/-- `lab[a] = lab[b];` -/
theorem wp_labFrom {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (ht : Tmp le L t) {a b : ident} {A B : Nat} (ha : PTree.get a le = some (.Vint (ir A)))
    (hb : PTree.get b le = some (.Vint (ir B))) (hA : A < n) (hB : B < n) (hsz : t.lab.size = n)
    (hQ : ∀ m', Mem m' L G { t with lab := t.lab.set! A t.lab[B]! } S → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge F (sk (.Sassign (ix id.lab (tv a)) (ix id.lab (tv b)))) Q empty_env le m := by
  wp_step; wp_step
  exact wp_labF hok hm ht (show Exec.evalExpr sge empty_env le m (tv a) = _ from ha) rfl hA
    (eval_lab hok hm ht (show Exec.evalExpr sge empty_env le m (tv b) = _ from hb) rfl hB) rfl hsz hQ

/-- `lab[a] = x;` for a temporary `x`. -/
theorem wp_labTmp {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (ht : Tmp le L t) {a x : ident} {A X : Nat} (ha : PTree.get a le = some (.Vint (ir A)))
    (hx : PTree.get x le = some (.Vint (ir X))) (hA : A < n) (hsz : t.lab.size = n)
    (hQ : ∀ m', Mem m' L G { t with lab := t.lab.set! A X } S → Frame L m m' →
      Q.normal E0 empty_env le m') :
    Wp xi sge F (sk (.Sassign (ix id.lab (tv a)) (tv x))) Q empty_env le m := by
  wp_step; wp_step
  exact wp_labF hok hm ht (show Exec.evalExpr sge empty_env le m (tv a) = _ from ha) rfl hA
    (show Exec.evalExpr sge empty_env le m (tv x) = _ from hx) rfl hsz hQ

end NautyVerified.Proofs.Sparse.Refine.Count

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The temporaries of the three-way insertion. -/
def minTemps (tv0 : ident) : List ident :=
  [id.«lj», id.«w3», id.«v2», id.«v3», id.«w1», id.«w2», id.«j», tv0]

/-- The C's state of the insertion: temporaries and memory for the model's
`(w1, v2, w2, v3, lab)`. -/
structure MinAt (L : Loc) (G : Hex.SparseGraph n) (t : RefineSt n) (S : Scr) (first last : Nat)
    (tv0 : ident) (le0 le : temp_env) (m0 m : mem) (j : Nat) (st : Nat × Nat × Nat × Nat × Array Nat) :
    Prop where
  mem : Mem m L G { t with lab := st.2.2.2.2 } S
  frame : Frame L m0 m
  win : Win t.lab st.2.2.2.2 first last
  v2lo : first + 1 ≤ st.2.1
  v2v3 : st.2.1 ≤ st.2.2.2.1
  w1 : st.1 < n + 2
  w2 : st.2.2.1 ≤ n + 2
  tj : PTree.get id.«j» le = some (.Vint (ir j))
  tw1 : PTree.get id.«w1» le = some (.Vint (ir st.1))
  tv2 : PTree.get id.«v2» le = some (.Vint (ir st.2.1))
  tw2 : PTree.get id.«w2» le = some (.Vint (ir (cw n st.2.2.1)))
  tv3 : PTree.get id.«v3» le = some (.Vint (ir st.2.2.2.1))
  temps : ∀ x, x ∉ minTemps tv0 → PTree.get x le = PTree.get x le0

end NautyVerified.Proofs.Sparse.Refine.Count

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem cw_eq {n w v : Nat} (hn : n < 1073741824) (hv : v < n + 2) : (v = cw n w) ↔ (v = w) := by
  unfold cw; split <;> omega

theorem cw_lt {n w v : Nat} (hn : n < 1073741824) (hv : v < n + 2) (hw : w ≤ n + 2) : (v < cw n w) ↔ (v < w) := by
  unfold cw; split <;> omega

theorem cw_small {n w : Nat} (hn : n < 1073741824) (hw : w ≤ n + 2) : cw n w < 2147483648 := by
  unfold cw; split <;> omega

theorem cw_of_lt {n w : Nat} (hw : w < n + 2) : cw n w = w := by
  unfold cw; split <;> omega

/-- Comparing two `int` temporaries. -/
theorem eval_cmp {le : temp_env} {m : mem} {op : Cfrontend.Cop.binary_operation} {a b : ident} {A B : Nat}
    (ha : PTree.get a le = some (.Vint (ir A))) (hb : PTree.get b le = some (.Vint (ir B))) :
    Exec.evalExpr sge empty_env le m (.Ebinop op (tv a) (tv b) tint) =
      Cfrontend.Cop.sem_binary_operation sge.genv_cenv op (.Vint (ir A)) tint (.Vint (ir B)) tint m :=
  eval_binop (show Exec.evalExpr sge empty_env le m (tv a) = _ from ha)
    (show Exec.evalExpr sge empty_env le m (tv b) = _ from hb)

end NautyVerified.Proofs.Sparse.Refine.Count

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The temporaries `minG`'s body may not clobber. -/
structure MinT (tv0 : ident) : Prop where
  ne : tv0 ∉ args ∧ tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive
  ne2 : tv0 ∉ [id.«lj», id.«w3», id.«v2», id.«v3», id.«w1», id.«w2», id.«j», id.«v1»]

theorem minTemps_ok {tv0 : ident} (h : MinT tv0) :
    ∀ x ∈ minTemps tv0, x ∉ args ∧ x ≠ id.longcode ∧ x ≠ id.nactive := by
  intro x hx
  simp only [minTemps, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | decide | exact h.ne

theorem v1_not {tv0 : ident} (htv : MinT tv0) : id.«v1» ∉ minTemps tv0 := by
  intro hm
  simp only [minTemps, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact htv.ne2 (by rw [h]; simp)

/-- The case analysis of one insertion step, given `lj = lab[j]` and `w3 = HITS[lj]`. -/
theorem wp_minCases {Q : Post} {le0 le : temp_env} {m0 m : mem} {tv0 : ident} (htv : MinT tv0)
    (hok : Ok n L) (ht0 : Tmp le0 L t) {first len j : Nat}
    (hk : Keys n L t S first len) (hsz : t.lab.size = n)
    (hv1 : PTree.get id.«v1» le0 = some (.Vint (ir first)))
    {W1 V2 W2 V3 : Nat} {lab' : Array Nat} (hj1 : V3 ≤ j) (hj2 : j < first + len)
    (h : MinAt L G t S first (first + len) tv0 le0 le m0 m j (W1, V2, W2, V3, lab'))
    (hlj : PTree.get id.«lj» le = some (.Vint (ir lab'[j]!)))
    (hw3 : PTree.get id.«w3» le = some (.Vint (ir t.hits[lab'[j]!]!)))
    (hQ : ∀ le' m', MinAt L G t S first (first + len) tv0 le0 le' m0 m' j
        (Count.minStep t.hits first (W1, V2, W2, V3, lab') j) →
      (Count.minStep t.hits first (W1, V2, W2, V3, lab') j).2.2.2.1 ≤ j + 1 →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F minCases Q empty_env le m := by
  have hnl := hok.nlt
  have hcl := hk.cell.1
  have hb := hk.bound
  have hlo := h.v2lo
  have hvv := h.v2v3
  simp only at hlo hvv
  have htj : PTree.get id.«j» le = some (.Vint (ir j)) := h.tj
  have htw1 : PTree.get id.«w1» le = some (.Vint (ir W1)) := h.tw1
  have htv2 : PTree.get id.«v2» le = some (.Vint (ir V2)) := h.tv2
  have htw2 : PTree.get id.«w2» le = some (.Vint (ir (cw n W2))) := h.tw2
  have htv3 : PTree.get id.«v3» le = some (.Vint (ir V3)) := h.tv3
  obtain ⟨q0, hq01, hq02, hq0⟩ := h.win.get (x := j) (by omega) hj2
  have hW3 : t.hits[lab'[j]!]! < n + 2 := by rw [hq0]; exact hk.small q0 hq01 hq02
  have hW1 : W1 < n + 2 := h.w1
  have hW2 : W2 ≤ n + 2 := h.w2
  have hlsz : lab'.size = n := h.win.size.trans hsz
  have ht : Tmp le L { t with lab := lab' } := (ht0.frame h.temps (minTemps_ok htv)).congr rfl rfl
  have hv1' : PTree.get id.«v1» le = some (.Vint (ir first)) := by
    rw [h.temps _ (v1_not htv)]; exact hv1
  have hwin : ∀ x, first ≤ x → x < first + len → ∃ q', first ≤ q' ∧ q' < first + len ∧
      lab'[x]! = t.lab[q']! := fun x h1 h2 => h.win.get h1 h2
  have hM := h.mem
  -- the stores below keep the window, the size and the frame
  apply wp_if_eval
  rw [eval_cmp hw3 htw1]
  simp only [typeof, cop]
  rw [ir_eq (a := (t.hits[lab'[j]!]! : Int)) (b := (W1 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hA : t.hits[lab'[j]!]! = W1
  · rw [show decide ((t.hits[lab'[j]!]! : Int) = W1) = true from decide_eq_true (by omega)]
    simp (config := {decide := true}) only [ite_true]
    have hst : Count.minStep t.hits first (W1, V2, W2, V3, lab') j =
        (W1, V2 + 1, W2, V3 + 1, ((lab'.set! j lab'[V3]!).set! V3 (lab'.set! j lab'[V3]!)[V2]!).set!
          V2 lab'[j]!) := by
      simp only [Count.minStep, hA, beq_self_eq_true, ↓reduceIte]
    rw [hst] at hQ
    have hl1 : (lab'.set! j lab'[V3]!).size = n := by simp [hlsz]
    have hw1' := h.win.set (x := j) (v := lab'[V3]!) (by omega) hj2 (hwin V3 (by omega) (by omega))
    wp_step
    refine wp_labFrom hok hM ht htj htv3 (by omega) (by omega) hlsz fun m1 hm1 hf1 => ?_
    simp only [seqPost, Post.after]
    wp_step
    have hw2' := hw1'.set (x := V3) (v := (lab'.set! j lab'[V3]!)[V2]!) (by omega) (by omega)
      (hw1'.get (x := V2) (by omega) (by omega))
    refine wp_labFrom hok hm1 (ht.congr rfl rfl) htv3 htv2 (by omega) (by omega) hl1 fun m2 hm2 hf2 => ?_
    simp only [seqPost, Post.after]
    wp_step
    have hw3' := hw2'.set (x := V2) (v := lab'[j]!) (by omega) (by omega) (hwin j (by omega) hj2)
    refine wp_labTmp hok hm2 (ht.congr rfl rfl) htv2 hlj (by omega) (by simp [hlsz]) fun m3 hm3 hf3 => ?_
    simp only [seqPost, Post.after]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, htv2, typeof, cop, ir_add]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gso _ _ (show id.«v3» ≠ id.«v2» by decide), htv3, typeof, cop, ir_add,
      E0_append]
    refine hQ _ _ ⟨hm3, ((h.frame.trans hf1).trans hf2).trans hf3, hw3', by simp only; omega, by simp only; omega, hW1, hW2, ?_, ?_, ?_,
      ?_, ?_, ?_⟩ (by simp only; omega)
    · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact htj
    · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact htw1
    · rw [temps_gso _ _ (by decide), temps_gss]; simp
    · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact htw2
    · rw [temps_gss]; simp
    · intro x hx
      rw [temps_gso _ _ (fun e => hx (by simp [minTemps, e])), temps_gso _ _ (fun e => hx (by simp [minTemps, e]))]
      exact h.temps x hx
  · rw [show decide ((t.hits[lab'[j]!]! : Int) = W1) = false from decide_eq_false (by omega)]
    simp (config := {decide := true}) only [ite_false]
    wp_step; wp_step
    apply wp_if_eval
    rw [eval_cmp hw3 htw2]
    simp only [typeof, cop]
    have hcw := cw_small hnl hW2
    rw [ir_eq (a := (t.hits[lab'[j]!]! : Int)) (b := (cw n W2 : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hB : t.hits[lab'[j]!]! = W2
    · rw [show decide ((t.hits[lab'[j]!]! : Int) = cw n W2) = true from
        decide_eq_true (by have := (cw_eq (w := W2) hnl hW3).2 hB; omega)]
      simp (config := {decide := true}) only [ite_true]
      have hst : Count.minStep t.hits first (W1, V2, W2, V3, lab') j =
          (W1, V2, W2, V3 + 1, (lab'.set! j lab'[V3]!).set! V3 lab'[j]!) := by
        simp only [Count.minStep, beq_iff_eq, hA, ↓reduceIte]; simp only [hB, ↓reduceIte]
      rw [hst] at hQ
      have hw1' := h.win.set (x := j) (v := lab'[V3]!) (by omega) hj2 (hwin V3 (by omega) (by omega))
      have hw2' := hw1'.set (x := V3) (v := lab'[j]!) (by omega) (by omega) (hwin j (by omega) hj2)
      wp_step
      refine wp_labFrom hok hM ht htj htv3 (by omega) (by omega) hlsz fun m1 hm1 hf1 => ?_
      simp only [seqPost, Post.after]
      wp_step
      refine wp_labTmp hok hm1 (ht.congr rfl rfl) htv3 hlj (by omega) (by simp [hlsz])
        fun m2 hm2 hf2 => ?_
      simp only [seqPost, Post.after]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, htv3, typeof, cop, ir_add, E0_append]
      refine hQ _ _ ⟨hm2, (h.frame.trans hf1).trans hf2, hw2', by simp only; omega, by simp only; omega, hW1, hW2, ?_, ?_, ?_,
        ?_, ?_, ?_⟩ (by simp only; omega)
      · rw [temps_gso _ _ (by decide)]; exact htj
      · rw [temps_gso _ _ (by decide)]; exact htw1
      · rw [temps_gso _ _ (by decide)]; exact htv2
      · rw [temps_gso _ _ (by decide)]; exact htw2
      · rw [temps_gss]; simp
      · intro x hx
        rw [temps_gso _ _ (fun e => hx (by simp [minTemps, e]))]
        exact h.temps x hx
    · rw [show decide ((t.hits[lab'[j]!]! : Int) = cw n W2) = false from
        decide_eq_false (by have := mt (cw_eq (w := W2) hnl hW3).1 hB; omega)]
      simp (config := {decide := true}) only [ite_false]
      wp_step; wp_step
      apply wp_if_eval
      rw [eval_cmp hw3 htw1]
      simp only [typeof, cop]
      rw [ir_lt (a := (t.hits[lab'[j]!]! : Int)) (b := (W1 : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
      by_cases hC : t.hits[lab'[j]!]! < W1
      · rw [show decide ((t.hits[lab'[j]!]! : Int) < W1) = true from decide_eq_true (by omega)]
        simp (config := {decide := true}) only [ite_true]
        have hst : Count.minStep t.hits first (W1, V2, W2, V3, lab') j =
            (t.hits[lab'[j]!]!, first + 1, W1, V2 + 1,
              ((lab'.set! j lab'[V2]!).set! V2 (lab'.set! j lab'[V2]!)[first]!).set! first lab'[j]!) := by
          simp only [Count.minStep, beq_iff_eq, hA, hB, hC, ↓reduceIte]
        rw [hst] at hQ
        have hw1' := h.win.set (x := j) (v := lab'[V2]!) (by omega) hj2 (hwin V2 (by omega) (by omega))
        have hw2' := hw1'.set (x := V2) (v := (lab'.set! j lab'[V2]!)[first]!) (by omega) (by omega)
          (hw1'.get (x := first) (Nat.le_refl _) (by omega))
        have hw3' := hw2'.set (x := first) (v := lab'[j]!) (Nat.le_refl _) (by omega)
          (hwin j (by omega) hj2)
        wp_step
        refine wp_labFrom hok hM ht htj htv2 (by omega) (by omega) hlsz fun m1 hm1 hf1 => ?_
        simp only [seqPost, Post.after]
        wp_step
        refine wp_labFrom hok hm1 (ht.congr rfl rfl) htv2 hv1' (by omega) (by omega) (by simp [hlsz])
          fun m2 hm2 hf2 => ?_
        simp only [seqPost, Post.after]
        wp_step
        refine wp_labTmp hok hm2 (ht.congr rfl rfl) hv1' hlj (by omega) (by simp [hlsz])
          fun m3 hm3 hf3 => ?_
        simp only [seqPost, Post.after]
        wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, htv2, typeof, cop, ir_add]
        wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gso _ _ (show id.«v1» ≠ id.«v3» by decide), hv1', typeof, cop,
          ir_add]
        wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gso _ _ (show id.«w1» ≠ id.«v2» by decide),
          temps_gso _ _ (show id.«w1» ≠ id.«v3» by decide), htw1]
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gso _ _ (show id.«w3» ≠ id.«w2» by decide),
          temps_gso _ _ (show id.«w3» ≠ id.«v2» by decide), temps_gso _ _ (show id.«w3» ≠ id.«v3» by decide),
          hw3, E0_append]
        refine hQ _ _ ⟨hm3, ((h.frame.trans hf1).trans hf2).trans hf3, hw3', by simp, by simp only; omega, by simp only; omega,
          by simp only; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by simp only; omega)
        · simp only [temps_gso _ _ (show id.«j» ≠ id.«w1» by decide), temps_gso _ _ (show id.«j» ≠ id.«w2» by decide),
            temps_gso _ _ (show id.«j» ≠ id.«v2» by decide), temps_gso _ _ (show id.«j» ≠ id.«v3» by decide)]
          exact htj
        · rw [temps_gss]
        · simp only [temps_gso _ _ (show id.«v2» ≠ id.«w1» by decide), temps_gso _ _ (show id.«v2» ≠ id.«w2» by decide),
            temps_gss]; simp
        · simp only [temps_gso _ _ (show id.«w2» ≠ id.«w1» by decide), temps_gss, cw_of_lt hW1]
        · simp only [temps_gso _ _ (show id.«v3» ≠ id.«w1» by decide), temps_gso _ _ (show id.«v3» ≠ id.«w2» by decide),
            temps_gso _ _ (show id.«v3» ≠ id.«v2» by decide), temps_gss]; simp
        · intro x hx
          have hne : ∀ y ∈ [id.«w1», id.«w2», id.«v2», id.«v3»], x ≠ y := fun y hy e => hx (by
            subst e; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
            rcases hy with rfl | rfl | rfl | rfl <;> simp [minTemps])
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hne
          rw [temps_gso _ _ hne.1, temps_gso _ _ hne.2.1, temps_gso _ _ hne.2.2.1, temps_gso _ _ hne.2.2.2]
          exact h.temps x hx
      · rw [show decide ((t.hits[lab'[j]!]! : Int) < W1) = false from decide_eq_false (by omega)]
        simp (config := {decide := true}) only [ite_false]
        wp_step; wp_step
        apply wp_if_eval
        rw [eval_cmp hw3 htw2]
        simp only [typeof, cop]
        rw [ir_lt (a := (t.hits[lab'[j]!]! : Int)) (b := (cw n W2 : Int)) ⟨by omega, by omega⟩
          ⟨by omega, by omega⟩]
        by_cases hD : t.hits[lab'[j]!]! < W2
        · rw [show decide ((t.hits[lab'[j]!]! : Int) < cw n W2) = true from
            decide_eq_true (by have := (cw_lt (w := W2) hnl hW3 hW2).2 hD; omega)]
          simp (config := {decide := true}) only [ite_true]
          have hst : Count.minStep t.hits first (W1, V2, W2, V3, lab') j =
              (W1, V2, t.hits[lab'[j]!]!, V2 + 1, (lab'.set! j lab'[V2]!).set! V2 lab'[j]!) := by
            simp only [Count.minStep, beq_iff_eq, hA, hB, hC, hD, ↓reduceIte]
          rw [hst] at hQ
          have hw1' := h.win.set (x := j) (v := lab'[V2]!) (by omega) hj2 (hwin V2 (by omega) (by omega))
          have hw2' := hw1'.set (x := V2) (v := lab'[j]!) (by omega) (by omega) (hwin j (by omega) hj2)
          wp_step
          refine wp_labFrom hok hM ht htj htv2 (by omega) (by omega) hlsz fun m1 hm1 hf1 => ?_
          simp only [seqPost, Post.after]
          wp_step
          refine wp_labTmp hok hm1 (ht.congr rfl rfl) htv2 hlj (by omega) (by simp [hlsz])
            fun m2 hm2 hf2 => ?_
          simp only [seqPost, Post.after]
          wp_step; wp_step; wp_step
          apply wp_set_eval
          simp only [Exec.evalExpr, htv2, typeof, cop, ir_add]
          wp_step; wp_step
          apply wp_set_eval
          simp only [Exec.evalExpr, temps_gso _ _ (show id.«w3» ≠ id.«v3» by decide), hw3, E0_append]
          refine hQ _ _ ⟨hm2, (h.frame.trans hf1).trans hf2, hw2', by simp only; omega, by simp only; omega, hW1, by simp only; omega,
            ?_, ?_, ?_, ?_, ?_, ?_⟩ (by simp only; omega)
          · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact htj
          · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact htw1
          · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact htv2
          · rw [temps_gss]; simp [cw_of_lt hW3]
          · rw [temps_gso _ _ (by decide), temps_gss]; simp
          · intro x hx
            rw [temps_gso _ _ (fun e => hx (by simp [minTemps, e])),
              temps_gso _ _ (fun e => hx (by simp [minTemps, e]))]
            exact h.temps x hx
        · rw [show decide ((t.hits[lab'[j]!]! : Int) < cw n W2) = false from
            decide_eq_false (by have := mt (cw_lt (w := W2) hnl hW3 hW2).1 hD; omega)]
          simp (config := {decide := true}) only [ite_false]
          wp_step
          have hst : Count.minStep t.hits first (W1, V2, W2, V3, lab') j = (W1, V2, W2, V3, lab') := by
            simp only [Count.minStep, beq_iff_eq, hA, hB, hC, hD, ↓reduceIte]
          rw [hst] at hQ
          exact hQ _ _ h (by simp only; omega)

theorem retempMin {tv0 : ident} {le0 le : temp_env} {m0 m : mem} {j first last : Nat}
    {st : Nat × Nat × Nat × Nat × Array Nat}
    (h : MinAt L G t S first last tv0 le0 le m0 m j st) {x : ident} (hx : x ∈ minTemps tv0)
    (hxj : x ≠ id.«j») (hx1 : x ≠ id.«w1») (hx2 : x ≠ id.«v2») (hx3 : x ≠ id.«w2») (hx4 : x ≠ id.«v3»)
    (v : val) : MinAt L G t S first last tv0 le0 (PTree.set x v le) m0 m j st :=
  { h with
    tj := by rw [temps_gso _ _ (Ne.symm hxj)]; exact h.tj
    tw1 := by rw [temps_gso _ _ (Ne.symm hx1)]; exact h.tw1
    tv2 := by rw [temps_gso _ _ (Ne.symm hx2)]; exact h.tv2
    tw2 := by rw [temps_gso _ _ (Ne.symm hx3)]; exact h.tw2
    tv3 := by rw [temps_gso _ _ (Ne.symm hx4)]; exact h.tv3
    temps := fun y hy => by
      rw [temps_gso _ _ (fun e => hy (by rw [e]; exact hx))]; exact h.temps y hy }

/-- The three-way insertion from `j = v2 = v3 = begin`, `w2 = NAUTY_INFINITY`
computes `minima`. -/
theorem wp_min {Q : Post} {le : temp_env} {m : mem} {tv0 : ident} (htv : MinT tv0)
    (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {first len begin : Nat}
    (hk : Keys n L t S first len) (hsz : t.lab.size = n) (hb1 : first + 1 ≤ begin)
    (hb2 : begin < first + len)
    (hv1 : PTree.get id.«v1» le = some (.Vint (ir first)))
    (hj : PTree.get id.«j» le = some (.Vint (ir begin)))
    (hv2 : PTree.get id.«v2» le = some (.Vint (ir begin)))
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir begin)))
    (hw1 : PTree.get id.«w1» le = some (.Vint (ir t.hits[t.lab[first]!]!)))
    (hw2 : PTree.get id.«w2» le = some (.Vint (ir 2000000002)))
    (hQ : ∀ le' m', MinAt L G t S first (first + len) tv0 le le' m m' (first + len)
        (Hex.GraphIso.Nauty.Sparse.CountSort.minima t.lab t.hits (n + 2) first (first + len) begin) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (minG tv0) Q empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  have hb := hk.bound
  let M := Hex.GraphIso.Nauty.Sparse.CountSort.minima t.lab t.hits (n + 2) first (first + len) begin
  let last := first + len
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ j st, v = last - j ∧ begin ≤ j ∧ j < last ∧ st.2.2.2.1 ≤ j ∧
      M = (List.range' j (last - j)).foldl (Count.minStep t.hits first) st ∧
      MinAt L G t S first last tv0 le le' m m' j st
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ j st, v = last - j ∧ begin ≤ j ∧ j < last ∧ st.2.2.2.1 ≤ j + 1 ∧
      M = (List.range' (j + 1) (last - (j + 1))).foldl (Count.minStep t.hits first) st ∧
      MinAt L G t S first last tv0 le le' m m' j st
  have h0 : MinAt L G t S first last tv0 le le m m begin
      (t.hits[t.lab[first]!]!, begin, n + 2, begin, t.lab) :=
    ⟨hm, Frame.refl _ _, Win.refl _ _ _, hb1, Nat.le_refl _, hk.small first (Nat.le_refl _) (by omega),
      Nat.le_refl _, hj, hw1, hv2, by simp [cw]; exact hw2, hv3, fun _ _ => rfl⟩
  rw [minG_eq]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := last - begin)
    ⟨rfl, rfl, begin, _, rfl, Nat.le_refl _, hb2, Nat.le_refl _, Count.minima_eq _ _ _ _ _ _, h0⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, j, ⟨W1, V2, W2, V3, lab'⟩, rfl, hj1, hj2, hv3j, hM, h⟩
    have ht' : Tmp le' L { t with lab := lab' } := (ht.frame h.temps (minTemps_ok htv)).congr rfl rfl
    obtain ⟨q0, hq01, hq02, hq0⟩ := h.win.get (x := j) (by have := h.v2lo; have := h.v2v3; omega) hj2
    have hlj : lab'[j]! < n := by rw [hq0]; exact hk.lab _ (by omega)
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_lab hok h.mem ht' (show Exec.evalExpr sge empty_env le' m' (tv id.«j») = _ from h.tj) rfl
      (by omega)]
    have h1 := retempMin h (x := id.«lj») (by simp [minTemps]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (.Vint (ir lab'[j]!))
    have ht1 : Tmp (PTree.set id.«lj» (.Vint (ir lab'[j]!)) le') L { t with lab := lab' } :=
      (ht.frame h1.temps (minTemps_ok htv)).congr rfl rfl
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_gw3 hok h.mem (show Exec.evalExpr sge empty_env _ m' (tv id.«lj») = _ from temps_gss _ _ _)
      rfl hlj, hk.hits _ hlj]
    have h2 := retempMin h1 (x := id.«w3») (by simp [minTemps]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (.Vint (ir t.hits[lab'[j]!]!))
    wp_step; wp_step
    refine wp_minCases htv hok ht hk hsz hv1 hv3j hj2 h2
      (by rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _) (temps_gss _ _ _) ?_
    intro le'' m'' h3 hb3
    simp only [E0_append]
    refine ⟨by simp, rfl, j, _, rfl, hj1, hj2, hb3, ?_, h3⟩
    rw [hM, show last - j = (last - (j + 1)) + 1 by omega, List.range'_succ, List.foldl_cons]
  · rintro v tr e' le' m' ⟨rfl, rfl, j, st, rfl, hj1, hj2, hv3j, hM, h⟩
    have ht' : Tmp le' L { t with lab := st.2.2.2.2 } := (ht.frame h.temps (minTemps_ok htv)).congr rfl rfl
    have htj : tv0 ≠ id.«j» := fun e => htv.ne2 (by simp [e])
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, h.tj]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]
    apply wp_if_eval
    let le2 := PTree.set id.«j» (.Vint (ir ((j : Int) + 1))) (PTree.set tv0 (.Vint (ir j)) le')
    have ht2 : Tmp le2 L { t with lab := st.2.2.2.2 } :=
      (ht'.set _ htv.ne).set _ (by decide)
    have hpj : Exec.evalExpr sge empty_env le2 m' (tv tv0) = some (.Vint (ir j)) := by
      simp only [Exec.evalExpr, le2]; rw [temps_gso _ _ htj, temps_gss]
    rw [eval_binop (eval_ptn hok h.mem ht2 hpj rfl (by omega))
      (show Exec.evalExpr sge empty_env le2 m' (tv id.«level») = _ from ht2.level)]
    simp only [typeof, cop]
    have hpl := hr.ptnSmall j (by omega)
    rw [ir_lt (a := (L.level : Int)) (b := (t.ptn[j]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have hgt := cell_gt hk.cell (q := j) (by have := h.v2lo; omega) hj2
    have h2 : MinAt L G t S first last tv0 le le2 m m' (j + 1) st :=
      { h with
        tj := by simp only [le2, temps_gss]; rfl
        tw1 := by simp only [le2]; rw [temps_gso _ _ (by decide), temps_gso _ _ (fun e => htv.ne2 (by simp [e]))]
                  exact h.tw1
        tv2 := by simp only [le2]; rw [temps_gso _ _ (by decide), temps_gso _ _ (fun e => htv.ne2 (by simp [e]))]
                  exact h.tv2
        tw2 := by simp only [le2]; rw [temps_gso _ _ (by decide), temps_gso _ _ (fun e => htv.ne2 (by simp [e]))]
                  exact h.tw2
        tv3 := by simp only [le2]; rw [temps_gso _ _ (by decide), temps_gso _ _ (fun e => htv.ne2 (by simp [e]))]
                  exact h.tv3
        temps := fun y hy => by
          simp only [le2]
          rw [temps_gso _ _ (fun e => hy (by simp [minTemps, e])), temps_gso _ _ (fun e => hy (by simp [minTemps, e]))]
          exact h.temps y hy }
    by_cases hlt : j + 1 < last
    · rw [show decide ((L.level : Int) < (t.ptn[j]! : Int)) = true from
        decide_eq_true (by have := hgt.2 hlt; omega)]
      simp (config := {decide := true}) only [ite_true]
      apply wp_skip
      exact ⟨last - (j + 1), by omega, by simp, rfl, j + 1, st, rfl, by omega, hlt, hv3j, hM, h2⟩
    · rw [show decide ((L.level : Int) < (t.ptn[j]! : Int)) = false from
        decide_eq_false (by have := mt hgt.1 hlt; omega)]
      simp (config := {decide := true}) only [ite_false]
      apply wp_break
      have hjl : j + 1 = last := by omega
      rw [hjl] at h2
      rw [show last - (j + 1) = 0 by omega] at hM
      simp only [List.range'_zero, List.foldl_nil] at hM
      rw [← hM] at h2
      simpa only [E0_append] using hQ _ _ h2

end NautyVerified.Proofs.Sparse.Refine.Count

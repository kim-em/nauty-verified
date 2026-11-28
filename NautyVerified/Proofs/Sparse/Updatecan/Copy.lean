import NautyVerified.Proofs.Sparse.Updatecan.Syntax
import NautyVerified.Proofs.Sparse.Updatecan.Rows
import NautyVerified.Proofs.Sparse.Testcanlab.Parts

/-!
# The copy loop of `updatecan_sg`

`wp_copy`: `for (j = 0; j < dli; ++j) ce[k++] = INVLAB[e[vli+j]];` writes the
`D` relabelled neighbours from `e[VL]` at `ce[K]`, …, leaves `ce` below `K`
alone and advances `k` to `K + D`.
-/

namespace NautyVerified.Proofs.Sparse.Updatecan

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat cast_l_i)
open NautyVerified.Proofs.Sparse.Testcanlab (wat eval_work1)
open Hex.GraphIso.Nauty.Sparse (Graph Rows inverse)

variable {xi : ExternalCalls}

abbrev F := sparse.fn.updatecan_sg

/-- The relabelled neighbour `j` of the row from `VL`. -/
abbrev nbv {n : Nat} (G : Hex.SparseGraph n) (lab : Array Nat) (VL j : Nat) : val :=
  .Vint (ir (((inverse n lab)[(Graph.ofGraph G).neighbor (VL + j)]! : Nat) : Int))

/-- `INVLAB[e[vli+j]]`. -/
theorem eval_invat {n : Nat} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {bW : block} {lab : Array Nat} {VL k : Nat}
    (he : PTree.get id.e le = some (.Vptr be eo))
    (hearr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size)
    (hvli : PTree.get id.vli le = some (.Vlong (lr VL)))
    (hj : PTree.get id.j le = some (.Vlong (lr k))) (hk : VL + k < G.neighbors.size)
    (hwp : Mem.load .Mint64 m Block.work1 (zOfInt 0) = some (.Vptr bW Ptrofs.zero))
    (hwarr : ArrayAt m .Mint32 bW 0 (fun p => .Vint (ir (((inverse n lab)[p]! : Nat) : Int))) n)
    (hn : n < 2147483648) :
    Exec.evalExpr sge empty_env le m invat = some (nbv G lab VL k) := by
  have hnd := Isautom.nde_lt hearr
  have hnb := neighbor_lt G hk
  have hel : Exec.evalExpr sge empty_env le m (iat id.e (.Ebinop .Oadd (tl id.vli) (tl id.j) tulong)) =
      some (.Vint (ir ((Graph.ofGraph G).neighbor (VL + k)))) := by
    refine eval_idx_l hearr (by omega) (by simp only [Exec.evalExpr]; exact he) rfl rfl rfl _ _
      hk ?_ rfl
    simp only [Exec.evalExpr, hvli, hj, typeof, cop, Sparse.lr_add]
  exact eval_idx (chunk := .Mint32) (bo := bW) (ofs := Ptrofs.zero) hwarr hn (eval_work1 hwp)
    rfl rfl rfl _ _ hnb hel rfl

/-- The copy loop. -/
theorem wp_copy {n : Nat} {Q : Post} {le : temp_env} {m : mem} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {bW : block} {lab : Array Nat} {cbe : block} {ceo : ptrofs} {ev : Nat → val}
    {N D K VL : Nat}
    (hce : PTree.get id.ce le = some (cePtr N cbe ceo))
    (hcearr : ArrayAt m .Mint32 cbe (intOfZ (Ptrofs.unsigned ceo)) ev N)
    (he : PTree.get id.e le = some (.Vptr be eo))
    (hearr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size)
    (hvli : PTree.get id.vli le = some (.Vlong (lr VL)))
    (hdli : PTree.get id.dli le = some (.Vint (ir D)))
    (hk : PTree.get id.k le = some (.Vlong (lr K)))
    (hVL : VL + D ≤ G.neighbors.size) (hKD : K + D ≤ N) (hN : N < 2147483648)
    (hwp : Mem.load .Mint64 m Block.work1 (zOfInt 0) = some (.Vptr bW Ptrofs.zero))
    (hwarr : ArrayAt m .Mint32 bW 0 (fun p => .Vint (ir (((inverse n lab)[p]! : Nat) : Int))) n)
    (hn : n < 2147483648) (hsep : 0 < N → cbe ≠ be ∧ cbe ≠ bW ∧ cbe ≠ Block.work1)
    (hQ : ∀ le' m' ev', ArrayAt m' .Mint32 cbe (intOfZ (Ptrofs.unsigned ceo)) ev' N →
      (∀ e, e < K → ev' e = ev e) → (∀ j < D, ev' (K + j) = nbv G lab VL j) →
      PTree.get id.k le' = some (.Vlong (lr (K + D))) →
      Unch m m' (fun z => 0 < N ∧ z = cbe) → Alloc.Keep m m' cbe →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ id.j → x ≠ id.k → x ≠ id.t2 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (jloop copyBody) Q empty_env le m := by
  have hD31 : D < 2147483648 := by omega
  let Fr := fun (le' : temp_env) => ∀ x, x ≠ id.j → x ≠ id.k → x ≠ id.t2 → PTree.get x le' = PTree.get x le
  let Mk := fun (q : Nat) (le' : temp_env) (m' : mem) => ∃ ev', ArrayAt m' .Mint32 cbe
      (intOfZ (Ptrofs.unsigned ceo)) ev' N ∧ (∀ e, e < K → ev' e = ev e) ∧
      (∀ j < q, ev' (K + j) = nbv G lab VL j) ∧ PTree.get id.k le' = some (.Vlong (lr (K + q))) ∧
      Unch m m' (fun z => 0 < N ∧ z = cbe) ∧ Alloc.Keep m m' cbe ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧ Fr le'
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ q, q ≤ D ∧ v = D - q ∧ PTree.get id.j le' = some (.Vlong (lr q)) ∧ Mk q le' m'
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ q, q < D ∧ v = D - q ∧ PTree.get id.j le' = some (.Vlong (lr q)) ∧ Mk (q + 1) le' m'
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := D - 0)
    ⟨rfl, rfl, 0, Nat.zero_le _, rfl, temps_gss _ _ _, ev, hcearr, fun _ _ => rfl,
      fun j hj => absurd hj (by omega), by rw [temps_gso _ _ (by decide)]; exact hk, Unch.refl _ _,
      Alloc.Keep.refl _ _, fun _ h => h, fun x hx _ _ => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, q, hq, rfl, hj, ev', harr', hlow, hrow, hk', hu, hkp, hg, ho⟩
    have hdli' : PTree.get id.dli le' = some (.Vint (ir D)) := by
      rw [ho _ (by decide) (by decide) (by decide)]; exact hdli
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj,
      show Exec.evalExpr sge empty_env le' m' (tv id.dli) = _ from hdli']
    simp only [typeof, cop, cast_l_i D hD31, Alloc.ltu_lr (a := q) (b := D) (by omega) (by omega)]
    by_cases hqD : q < D
    · rw [ite_eq_left (by simpa using hqD)]
      apply wp_skip
      have hN0 : 0 < N := by omega
      have hs := hsep hN0
      have hce' : PTree.get id.ce le' = some (.Vptr cbe ceo) := by
        rw [ho _ (by decide) (by decide) (by decide), hce, cePtr_pos hN0]
      have he' : PTree.get id.e le' = some (.Vptr be eo) := by
        rw [ho _ (by decide) (by decide) (by decide)]; exact he
      have hvli' : PTree.get id.vli le' = some (.Vlong (lr VL)) := by
        rw [ho _ (by decide) (by decide) (by decide)]; exact hvli
      have hearr' := hearr.unch hu (fun h => hs.1 h.2.symm)
      have hwp' : Mem.load .Mint64 m' Block.work1 (zOfInt 0) = some (.Vptr bW Ptrofs.zero) := by
        rw [hu.load _ _ _ (fun h => hs.2.2 h.2.symm)]; exact hwp
      have hwarr' := hwarr.unch hu (fun h => hs.2.1 h.2.symm)
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hk']
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      have hkv : Lib.Integers.Int64.add (lr ((K : Int) + q)) (Lib.Integers.Int64.repr
          (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 1)))) = lr ((K : Int) + q + 1) := by
        have := Alloc.add_lr_one (k := K + q); push_cast at this; exact this
      rw [hkv]
      let le2 := PTree.set id.k (.Vlong (lr (K + q + 1))) (PTree.set id.t2 (.Vlong (lr (K + q))) le')
      have ht2 : PTree.get id.t2 le2 = some (.Vlong (lr (K + q))) := by
        rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _
      have hj2 : PTree.get id.j le2 = some (.Vlong (lr q)) := by
        rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj
      refine wp_idx_store_l (chunk := .Mint32) (ty := tint) (pe := .Etempvar id.ce (tptr tint)) (bo := cbe) (ofs := ceo) harr' (by omega)
        ?hp
        rfl rfl rfl (.Etempvar id.t2 tulong) (K + q) (by omega) ht2 rfl invat tint rfl
        (nbv G lab VL q) (nbv G lab VL q)
        (eval_invat (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact he') hearr'
          (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hvli') hj2 (by omega)
          hwp' hwarr' hn) rfl rfl ?_
      case hp =>
        simp only [Exec.evalExpr]
        rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hce'
      intro m'' harr'' hu' hk'' hg'
      refine ⟨by simp, rfl, q, hqD, rfl, hj2, upd ev' (K + q) (nbv G lab VL q), harr'',
        fun e he => by rw [upd_ne _ _ (by omega)]; exact hlow e he, fun j hj => ?_,
        by rw [temps_gss]; push_cast; rfl, hu.trans (hu'.mono fun z hz => ⟨hN0, hz⟩), hkp.trans hk'',
        fun z h => hg' _ (hg _ h), fun x h1 h2 h3 => ?_⟩
      · by_cases hjq : j = q
        · subst hjq; exact upd_same _ _ _
        · rw [upd_ne _ _ (by omega)]; exact hrow j (by omega)
      · rw [temps_gso _ _ h2, temps_gso _ _ h3]; exact ho x h1 h2 h3
    · rw [ite_eq_right (by simpa using hqD)]
      apply wp_break
      have : q = D := by omega
      subst this
      exact hQ le' m' ev' harr' hlow hrow hk' hu hkp hg ho
  · rintro v t e' le' m' ⟨rfl, rfl, q, hq, rfl, hj, hmk⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj]
    simp only [Exec.evalExpr, typeof, cop, Alloc.add_lr_one]
    obtain ⟨ev', harr', hlow, hrow, hk', hu, hkp, hg, ho⟩ := hmk
    exact ⟨D - (q + 1), by omega, by simp, rfl, q + 1, by omega, rfl, temps_gss _ _ _, ev', harr', hlow,
      hrow, by rw [temps_gso _ _ (by decide)]; exact hk', hu, hkp, hg,
      fun x h1 h2 h3 => by rw [temps_gso _ _ h1]; exact ho x h1 h2 h3⟩

end NautyVerified.Proofs.Sparse.Updatecan

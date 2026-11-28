import NautyVerified.Proofs.Sparse.Testcanlab.Syntax
import NautyVerified.Proofs.Sparse.Testcanlab.Rows
import NautyVerified.Proofs.Sparse.Isautom.Loops
import NautyVerified.Proofs.Sparse.Canon

/-!
# The three neighbour loops of a row of `testcanlab_sg`

For row `i`, with `vi = cv[i]`, `di = cd[i]` (`D`) and `vli = v[lab[i]]`:
`wp_markLoop` (`for (j = 0; j < di; ++j) MARK1(ce[vi+j]);`) marks exactly the
stored row; `wp_unmarkLoop` (the candidate pass) leaves the marks and `mina`
that HexGraphIso's `unmark` computes over the relabelled candidate row;
`wp_checkLoop` returns `-1` exactly when a stored entry is still marked and
below `mina`.
-/

namespace NautyVerified.Proofs.Sparse.Testcanlab

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat mat cast_l_i)
open Hex.GraphIso.Nauty.Sparse (Graph Rows inverse)

variable {xi : ExternalCalls}

abbrev F := sparse.fn.testcanlab_sg

/-- The temporaries the neighbour loops change. -/
def LoopLocal (x : ident) : Prop := x = id.j ∨ x = id.k ∨ x = id.mina ∨ x = id.t2

instance (x : ident) : Decidable (LoopLocal x) := by unfold LoopLocal; infer_instance

/-- What the neighbour loops of a row read. -/
structure LoopCtx {n : Nat} (m : mem) (le : temp_env) (G : Hex.SparseGraph n) (be : block)
    (eo : ptrofs) (R : Rows n) (cbe : block) (ceo : ptrofs) (ev : Nat → val) (bW : block)
    (lab : Array Nat) (D VI VL : Nat) : Prop where
  hce : PTree.get id.ce le = some (.Vptr cbe ceo)
  he : PTree.get id.e le = some (.Vptr be eo)
  hdi : PTree.get id.di le = some (.Vint (ir D))
  hvi : PTree.get id.vi le = some (.Vlong (lr VI))
  hvli : PTree.get id.vli le = some (.Vlong (lr VL))
  hn : PTree.get id.n le = some (.Vint (ir n))
  cearr : ArrayAt m .Mint32 cbe (intOfZ (Ptrofs.unsigned ceo)) ev R.neighbors.size
  cev : ∀ j < D, ev (VI + j) = .Vint (ir ((R.neighbors[VI + j]! : Nat) : Int))
  csmall : ∀ j < D, R.neighbors[VI + j]! < n
  hVD : VI + D ≤ R.neighbors.size
  earr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size
  hVL : VL + D ≤ G.neighbors.size
  wptr : Mem.load .Mint64 m Block.work1 (zOfInt 0) = some (.Vptr bW Ptrofs.zero)
  warr : ArrayAt m .Mint32 bW 0 (fun p => .Vint (ir (((inverse n lab)[p]! : Nat) : Int))) n
  invlt : ∀ p : Nat, (inverse n lab)[p]! < n
  n31 : n < 2147483648
  nde31 : R.neighbors.size < 2147483648

theorem LoopCtx.temps {n : Nat} {m : mem} {le le' : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {R : Rows n} {cbe : block} {ceo : ptrofs} {ev : Nat → val} {bW : block}
    {lab : Array Nat} {D VI VL : Nat} (h : LoopCtx m le G be eo R cbe ceo ev bW lab D VI VL)
    (hle : ∀ x, ¬ LoopLocal x → PTree.get x le' = PTree.get x le) :
    LoopCtx m le' G be eo R cbe ceo ev bW lab D VI VL :=
  { h with
    hce := by rw [hle _ (by decide)]; exact h.hce
    he := by rw [hle _ (by decide)]; exact h.he
    hdi := by rw [hle _ (by decide)]; exact h.hdi
    hvi := by rw [hle _ (by decide)]; exact h.hvi
    hvli := by rw [hle _ (by decide)]; exact h.hvli
    hn := by rw [hle _ (by decide)]; exact h.hn }

theorem LoopCtx.mem {n : Nat} {m m' : mem} {le : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {R : Rows n} {cbe : block} {ceo : ptrofs} {ev : Nat → val} {bW : block}
    {lab : Array Nat} {D VI VL : Nat} (h : LoopCtx m le G be eo R cbe ceo ev bW lab D VI VL)
    {S : block → Prop} (hu : Unch m m' S) (hc : ¬ S cbe) (he : ¬ S be) (hw : ¬ S Block.work1)
    (hb : ¬ S bW) : LoopCtx m' le G be eo R cbe ceo ev bW lab D VI VL :=
  { h with
    cearr := h.cearr.unch hu hc
    earr := h.earr.unch hu he
    wptr := by rw [hu.load _ _ _ hw]; exact h.wptr
    warr := h.warr.unch hu hb }

theorem D_lt {n : Nat} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {R : Rows n} {cbe : block} {ceo : ptrofs} {ev : Nat → val} {bW : block}
    {lab : Array Nat} {D VI VL : Nat} (h : LoopCtx m le G be eo R cbe ceo ev bW lab D VI VL) :
    D < 2147483648 := by
  have := h.hVD; have := h.nde31; omega

/-- `ce[vi + j]`. -/
theorem eval_ceat {n : Nat} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {R : Rows n} {cbe : block} {ceo : ptrofs} {ev : Nat → val} {bW : block}
    {lab : Array Nat} {D VI VL : Nat} (h : LoopCtx m le G be eo R cbe ceo ev bW lab D VI VL)
    {k : Nat} (hj : PTree.get id.j le = some (.Vlong (lr k))) (hk : k < D) :
    Exec.evalExpr sge empty_env le m ceat = some (.Vint (ir ((R.neighbors[VI + k]! : Nat) : Int))) := by
  have hnd := h.nde31
  have hVD := h.hVD
  rw [← h.cev k hk]
  refine eval_idx_l h.cearr (by omega) (by simp only [Exec.evalExpr]; exact h.hce) rfl rfl rfl _ _
    (by omega) ?_ rfl
  simp only [Exec.evalExpr, h.hvi, hj, typeof, cop, Sparse.lr_add]

/-- `INVLAB[e[vli + j]]`. -/
theorem eval_inv {n : Nat} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {R : Rows n} {cbe : block} {ceo : ptrofs} {ev : Nat → val} {bW : block}
    {lab : Array Nat} {D VI VL : Nat} (h : LoopCtx m le G be eo R cbe ceo ev bW lab D VI VL)
    {k : Nat} (hj : PTree.get id.j le = some (.Vlong (lr k))) (hk : k < D) :
    Exec.evalExpr sge empty_env le m (wat (iat id.e (.Ebinop .Oadd (tl id.vli) (tl id.j) tulong))) =
      some (.Vint (ir (((inverse n lab)[(Graph.ofGraph G).neighbor (VL + k)]! : Nat) : Int))) := by
  have hVL := h.hVL
  have hnd := Isautom.nde_lt h.earr
  have hnb := neighbor_lt G (show VL + k < G.neighbors.size by omega)
  have hel : Exec.evalExpr sge empty_env le m (iat id.e (.Ebinop .Oadd (tl id.vli) (tl id.j) tulong)) =
      some (.Vint (ir ((Graph.ofGraph G).neighbor (VL + k)))) := by
    refine eval_idx_l h.earr (by omega) (by simp only [Exec.evalExpr]; exact h.he) rfl rfl rfl _ _
      (by omega) ?_ rfl
    simp only [Exec.evalExpr, h.hvli, hj, typeof, cop, Sparse.lr_add]
  exact eval_idx (chunk := .Mint32) (bo := bW) (ofs := Ptrofs.zero) h.warr h.n31
    (by simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get id.work1 (empty_env : env) = none from rfl, find_work1, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq]; exact h.wptr)
    rfl rfl rfl _ _ hnb hel rfl

/-- The mark loop. -/
theorem wp_markLoop {n : Nat} {Q : Post} {le : temp_env} {m : mem} {G : Hex.SparseGraph n}
    {be : block} {eo : ptrofs} {R : Rows n} {cbe : block} {ceo : ptrofs} {ev : Nat → val} {bW : block}
    {lab : Array Nat} {D VI VL : Nat} {cap : Nat} {b : block} {st : Nat} {marks : Nat → Int}
    (hc : LoopCtx m le G be eo R cbe ceo ev bW lab D VI VL)
    (hM : MarksAt m cap b st marks) (hnc : n ≤ cap)
    (hbelow : ∀ x < cap, marks x < st)
    (hsep : 0 < cap → b ≠ cbe ∧ b ≠ be ∧ b ≠ bW ∧ b ≠ Block.work1)
    (hQ : ∀ le' m' marks', MarksAt m' cap b st marks' →
      (∀ x < cap, marks' x = st ↔ ∃ j < D, R.neighbors[VI + j]! = x) →
      Unch m m' (fun z => 0 < cap ∧ z = b) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F (jloop mark) Q empty_env le m := by
  have hn31 := hc.n31
  have hD31 := D_lt hc
  have hcap31 := hM.dyn.capLt
  let Hit := fun (k : Nat) (x : Nat) => ∃ j < k, R.neighbors[VI + j]! = x
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k marks', k ≤ D ∧ v = D - k ∧ PTree.get id.j le' = some (.Vlong (lr k)) ∧
      MarksAt m' cap b st marks' ∧ (∀ x < cap, marks' x = st ↔ Hit k x) ∧
      Unch m m' (fun z => 0 < cap ∧ z = b) ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
      ∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k marks', k < D ∧ v = D - k ∧ PTree.get id.j le' = some (.Vlong (lr k)) ∧
      MarksAt m' cap b st marks' ∧ (∀ x < cap, marks' x = st ↔ Hit (k + 1) x) ∧
      Unch m m' (fun z => 0 < cap ∧ z = b) ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
      ∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := D - 0)
    ⟨rfl, rfl, 0, marks, Nat.zero_le _, rfl, temps_gss _ _ _, hM, fun x hx =>
      ⟨fun h => absurd h (by have := hbelow x hx; omega), fun ⟨j, hj, _⟩ => absurd hj (by omega)⟩,
      Unch.refl _ _, fun _ h => h, fun x hx => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, k, marks', hk, rfl, hj, hM', hhit, hu, hg, ho⟩
    have hc' := (hc.temps fun x hx => ho x (fun h => hx (.inl h))).mem hu
      (fun ⟨h0, h⟩ => (hsep h0).1 h.symm) (fun ⟨h0, h⟩ => (hsep h0).2.1 h.symm)
      (fun ⟨h0, h⟩ => (hsep h0).2.2.2 h.symm) (fun ⟨h0, h⟩ => (hsep h0).2.2.1 h.symm)
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj,
      show Exec.evalExpr sge empty_env le' m' (tv id.di) = _ from hc'.hdi]
    simp only [typeof, cop, cast_l_i D hD31, Alloc.ltu_lr (a := k) (b := D) (by omega) (by omega)]
    by_cases hkD : k < D
    · rw [ite_eq_left (by simpa using hkD)]
      apply wp_skip
      wp_step; wp_step
      have hx := hc.csmall k hkD
      have hcap0 : 0 < cap := by omega
      have hse := Search.sign_ext16_ir (a := (st : Int)) (by omega) (by have := hM'.val32; omega)
      refine wp_idx_store (chunk := .Mint16signed) (bo := b) (ofs := Ptrofs.zero) hM'.arr hcap31
        (eval_vmark1 (hM'.dyn.ptr hcap0)) rfl rfl rfl ceat _ (by omega)
        (eval_ceat hc' hj hkD) rfl _ tshort rfl (.Vint (ir st)) (.Vint (ir st))
        (eval_val hM'.valLd) (by rw [Search.cast_ss, hse]) (by
          exact congrArg val.Vint hse) ?_
      intro m'' harr'' hu' hk' hg'
      let c := R.neighbors[VI + k]!
      refine ⟨by simp, rfl, k, fun x => if x = c then st else marks' x, hkD, rfl, hj,
        hM'.update hcap0 hu' hk' (harr''.congr fun i _ => ?_) (fun i hi => ?_), fun x hx => ?_,
        hu.trans (hu'.mono fun z hz => ⟨hcap0, hz⟩), fun z h => hg' _ (hg _ h), ho⟩
      · by_cases hic : i = c
        · rw [hic]; exact (upd_same _ _ _).trans (by simp only [markVals, ite_true])
        · rw [upd_ne _ _ hic]; simp [markVals, hic]
      · by_cases hic : i = c
        · simp only [hic, ite_true]; exact ⟨by omega, Int.le_refl _⟩
        · simp only [hic, ite_false]; exact hM'.bounds i hi
      · by_cases hxc : x = c
        · simp only [hxc, ite_true, true_iff]
          exact ⟨k, by omega, rfl⟩
        · simp only [hxc, ite_false]
          rw [hhit x hx]
          constructor
          · rintro ⟨j, hj, he⟩; exact ⟨j, by omega, he⟩
          · rintro ⟨j, hj, he⟩
            refine ⟨j, ?_, he⟩
            rcases Nat.lt_or_ge j k with h | h
            · exact h
            · exact absurd (show j = k by omega ▸ he).symm hxc
    · rw [ite_eq_right (by simpa using hkD)]
      apply wp_break
      have : k = D := by omega
      subst this
      exact hQ le' m' marks' hM' hhit hu hg ho
  · rintro v t e' le' m' ⟨rfl, rfl, k, marks', hk, rfl, hj, hM', hhit, hu, hg, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj]
    simp only [Exec.evalExpr, typeof, cop, Alloc.add_lr_one]
    exact ⟨D - (k + 1), by omega, by simp, rfl, k + 1, marks', by omega, rfl, temps_gss _ _ _, hM',
      hhit, hu, hg, fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩

theorem unmark_le : ∀ (B : List Nat) (mk : Nat → Bool) (mina : Nat), (unmark B mk mina).2 ≤ mina
  | [], _, _ => Nat.le_refl _
  | k :: B, mk, mina => by
    have h : unmark (k :: B) mk mina = unmark B (unmarkStep (mk, mina) k).1 (unmarkStep (mk, mina) k).2 := rfl
    rw [h]
    refine Nat.le_trans (unmark_le B _ _) ?_
    unfold unmarkStep
    split
    · exact Nat.le_refl _
    · simp only; split <;> omega

/-- The relabelled candidate entries from `VL`. -/
abbrev cands {n : Nat} (G : Hex.SparseGraph n) (lab : Array Nat) (VL k : Nat) : List Nat :=
  (List.range' VL k).map (fun j => (inverse n lab)[(Graph.ofGraph G).neighbor j]!)

theorem cands_succ {n : Nat} (G : Hex.SparseGraph n) (lab : Array Nat) (VL k : Nat) :
    cands G lab VL (k + 1) = cands G lab VL k ++ [(inverse n lab)[(Graph.ofGraph G).neighbor (VL + k)]!] := by
  simp [cands, List.range'_concat]

/-- The candidate pass. -/
theorem wp_unmarkLoop {n : Nat} {Q : Post} {le : temp_env} {m : mem} {G : Hex.SparseGraph n}
    {be : block} {eo : ptrofs} {R : Rows n} {cbe : block} {ceo : ptrofs} {ev : Nat → val} {bW : block}
    {lab : Array Nat} {D VI VL : Nat} {cap : Nat} {b : block} {st : Nat} {marks : Nat → Int}
    {mk : Nat → Bool}
    (hc : LoopCtx m le G be eo R cbe ceo ev bW lab D VI VL)
    (hM : MarksAt m cap b st marks) (hnc : n ≤ cap) (hmk : ∀ x < n, marks x = st ↔ mk x = true)
    (hmina : PTree.get id.mina le = some (.Vint (ir n)))
    (hsep : 0 < cap → b ≠ cbe ∧ b ≠ be ∧ b ≠ bW ∧ b ≠ Block.work1)
    (hQ : ∀ le' m' marks', MarksAt m' cap b st marks' →
      (∀ x < n, marks' x = st ↔ (unmark (cands G lab VL D) mk n).1 x = true) →
      PTree.get id.mina le' = some (.Vint (ir (unmark (cands G lab VL D) mk n).2)) →
      Unch m m' (fun z => 0 < cap ∧ z = b) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ id.j → x ≠ id.k → x ≠ id.mina → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (jloop unmarkBody) Q empty_env le m := by
  have hn31 := hc.n31
  have hD31 := D_lt hc
  have hcap31 := hM.dyn.capLt
  have hst1 := hM.val1
  let U := fun k => unmark (cands G lab VL k) mk n
  let Fr := fun (le' : temp_env) => ∀ x, x ≠ id.j → x ≠ id.k → x ≠ id.mina → PTree.get x le' = PTree.get x le
  let Mk := fun (k : Nat) (le' : temp_env) (m' : mem) => ∃ marks', MarksAt m' cap b st marks' ∧
    (∀ x < n, marks' x = st ↔ (U k).1 x = true) ∧
    PTree.get id.mina le' = some (.Vint (ir (U k).2)) ∧
    Unch m m' (fun z => 0 < cap ∧ z = b) ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧ Fr le'
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k, k ≤ D ∧ v = D - k ∧ PTree.get id.j le' = some (.Vlong (lr k)) ∧ Mk k le' m'
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k, k < D ∧ v = D - k ∧ PTree.get id.j le' = some (.Vlong (lr k)) ∧
      Mk (k + 1) le' m'
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := D - 0)
    ⟨rfl, rfl, 0, Nat.zero_le _, rfl, temps_gss _ _ _, marks, hM, hmk,
      by rw [temps_gso _ _ (by decide)]; exact hmina, Unch.refl _ _, fun _ h => h,
      fun x hx _ _ => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, k, hk, rfl, hj, marks', hM', hrel, hmn, hu, hg, ho⟩
    have hc' := (hc.temps fun x hx => by
      simp only [LoopLocal, not_or] at hx
      exact ho x hx.1 hx.2.1 hx.2.2.1).mem hu
      (fun ⟨h0, h⟩ => (hsep h0).1 h.symm) (fun ⟨h0, h⟩ => (hsep h0).2.1 h.symm)
      (fun ⟨h0, h⟩ => (hsep h0).2.2.2 h.symm) (fun ⟨h0, h⟩ => (hsep h0).2.2.1 h.symm)
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj,
      show Exec.evalExpr sge empty_env le' m' (tv id.di) = _ from hc'.hdi]
    simp only [typeof, cop, cast_l_i D hD31, Alloc.ltu_lr (a := k) (b := D) (by omega) (by omega)]
    by_cases hkD : k < D
    · rw [ite_eq_left (by simpa using hkD)]
      apply wp_skip
      let K := (inverse n lab)[(Graph.ofGraph G).neighbor (VL + k)]!
      have hK : K < n := hc.invlt _
      have hcap0 : 0 < cap := by omega
      have hstep : U (k + 1) = unmarkStep (U k) K := by
        simp only [U, cands_succ, unmark_concat]; rfl
      have hUle : (U k).2 ≤ n := unmark_le (cands G lab VL k) mk n
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_inv hc' hj hkD]
      have hkt : PTree.get id.k (PTree.set id.k (.Vint (ir K)) le') = some (.Vint (ir K)) := temps_gss _ _ _
      have hb := hM'.bounds K (by omega)
      have hst := hM'.val32
      have hel := eval_idx (chunk := .Mint16signed) (bo := b) (ofs := Ptrofs.zero) (le := PTree.set id.k (.Vint (ir K)) le')
        hM'.arr hcap31 (eval_vmark1 (hM'.dyn.ptr hcap0)) rfl rfl rfl (tv id.k) K (by omega) hkt rfl
      wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hel, eval_val hM'.valLd]
      simp only [markVals, typeof, cop]
      rw [ir_eq (a := marks' K) (b := (st : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      have hFr : ∀ le'', (∀ x, x ≠ id.j → x ≠ id.k → x ≠ id.mina → PTree.get x le'' = PTree.get x le') →
          Fr le'' := fun le'' h x h1 h2 h3 => by rw [h x h1 h2 h3, ho x h1 h2 h3]
      by_cases hm : marks' K = st
      · rw [show decide (marks' K = st) = true from decide_eq_true hm]
        simp (config := {decide := true}) only [cop, ite_true]
        have hUK : (U k).1 K = true := (hrel K hK).1 hm
        wp_step; wp_step
        refine wp_idx_store (chunk := .Mint16signed) (bo := b) (ofs := Ptrofs.zero) hM'.arr hcap31
          (eval_vmark1 (hM'.dyn.ptr hcap0)) rfl rfl rfl (tv id.k) K (by omega) hkt rfl _ tint rfl
          (.Vint (ir 0)) (.Vint (ir 0)) rfl (cast_zero_short _) rfl ?_
        intro m'' harr'' hu' hk' hg'
        refine ⟨by simp, rfl, k, hkD, rfl, by rw [temps_gso _ _ (by decide)]; exact hj,
          fun x => if x = K then 0 else marks' x,
          hM'.update hcap0 hu' hk' (harr''.congr fun i _ => ?_) (fun i hi => ?_), fun x hx => ?_,
          ?_, hu.trans (hu'.mono fun z hz => ⟨hcap0, hz⟩), fun z h => hg' _ (hg _ h),
          hFr _ fun x h1 h2 h3 => temps_gso _ _ h2⟩
        · by_cases hic : i = K
          · rw [hic]; exact (upd_same _ _ _).trans (by simp only [markVals, ite_true])
          · rw [upd_ne _ _ hic]; simp [markVals, hic]
        · by_cases hic : i = K
          · simp only [hic, ite_true]; exact ⟨Int.le_refl _, by omega⟩
          · simp only [hic, ite_false]; exact hM'.bounds i hi
        · rw [hstep]
          simp only [unmarkStep, hUK, ite_true]
          by_cases hxK : x = K
          · simp only [hxK, ite_true]; constructor
            · intro h; omega
            · intro h; exact absurd h (by decide)
          · simp only [hxK, ite_false]; exact hrel x hx
        · rw [hstep]; simp only [unmarkStep, hUK, ite_true]
          rw [temps_gso _ _ (by decide)]; exact hmn
      · rw [show decide (marks' K = st) = false from decide_eq_false hm]
        simp (config := {decide := true}) only [cop, ite_false]
        have hUK : (U k).1 K = false := Bool.eq_false_iff.2 fun h => hm ((hrel K hK).2 h)
        have hmn' : PTree.get id.mina (PTree.set id.k (.Vint (ir K)) le') =
            some (.Vint (ir (U k).2)) := by rw [temps_gso _ _ (by decide)]; exact hmn
        wp_step; wp_step
        apply wp_if_eval
        rw [Exec.evalExpr, show Exec.evalExpr sge empty_env _ m' (tv id.k) = _ from hkt,
          show Exec.evalExpr sge empty_env _ m' (tv id.mina) = _ from hmn']
        simp only [typeof, cop]
        rw [ir_lt (a := (K : Int)) (b := ((U k).2 : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
        by_cases hlt : K < (U k).2
        · rw [ite_eq_left (by simpa using hlt)]
          wp_step; wp_step
          apply wp_set_eval
          simp only [Exec.evalExpr, temps_gss]
          refine ⟨by simp, rfl, k, hkD, rfl, by
            rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj, marks', hM',
            fun x hx => ?_, ?_, hu, hg, hFr _ fun x h1 h2 h3 => by
              rw [temps_gso _ _ h3, temps_gso _ _ h2]⟩
          · rw [hstep]; simp only [unmarkStep, hUK]; exact hrel x hx
          · rw [hstep]; simp only [unmarkStep, hUK, hlt, ite_true, Bool.false_eq_true, ite_false]
            exact temps_gss _ _ _
        · rw [ite_eq_right (by simpa using hlt)]
          apply wp_skip
          refine ⟨by simp, rfl, k, hkD, rfl, by rw [temps_gso _ _ (by decide)]; exact hj, marks', hM',
            fun x hx => ?_, ?_, hu, hg, hFr _ fun x h1 h2 h3 => temps_gso _ _ h2⟩
          · rw [hstep]; simp only [unmarkStep, hUK]; exact hrel x hx
          · rw [hstep]; simp only [unmarkStep, hUK, hlt, Bool.false_eq_true, ite_false]
            exact hmn'
    · rw [ite_eq_right (by simpa using hkD)]
      apply wp_break
      have : k = D := by omega
      subst this
      exact hQ le' m' marks' hM' hrel hmn hu hg ho
  · rintro v t e' le' m' ⟨rfl, rfl, k, hk, rfl, hj, marks', hM', hrel, hmn, hu, hg, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj]
    simp only [Exec.evalExpr, typeof, cop, Alloc.add_lr_one]
    exact ⟨D - (k + 1), by omega, by simp, rfl, k + 1, by omega, rfl, temps_gss _ _ _, marks', hM',
      hrel, by rw [temps_gso _ _ (by decide)]; exact hmn, hu, hg,
      fun x h1 h2 h3 => by rw [temps_gso _ _ h1, ho x h1 h2 h3]⟩

theorem neg_one : Lib.Integers.Int.neg (ir 1) = ir (-1) := by decide

/-- `return -1;` -/
theorem wp_ret_neg {Q : Post} {le : temp_env} {m : mem} (h : Q.ret E0 (.Vint (ir (-1))) m) :
    Wp xi sge F (sk (.Sreturn (some (.Eunop .Oneg (ci 1 tint) tint)))) Q empty_env le m := by
  wp_step; wp_step
  apply wp_return_some_eval
  simp only [Exec.evalExpr, typeof, cop, sparse.fn.testcanlab_sg.fn_return_eq, Isautom.free_empty]
  rw [neg_one]; exact h

/-- `return c;` for a constant `c`. -/
theorem wp_ret_const {Q : Post} {le : temp_env} {m : mem} {c : Nat} (h : Q.ret E0 (.Vint (ir c)) m) :
    Wp xi sge F (sk (.Sreturn (some (ci c tint)))) Q empty_env le m := by
  wp_step; wp_step
  apply wp_return_some_eval
  simp only [Exec.evalExpr, typeof, cop, sparse.fn.testcanlab_sg.fn_return_eq, Isautom.free_empty]
  exact h

/-- The check loop. -/
theorem wp_checkLoop {n : Nat} {Q : Post} {le : temp_env} {m : mem} {G : Hex.SparseGraph n}
    {be : block} {eo : ptrofs} {R : Rows n} {cbe : block} {ceo : ptrofs} {ev : Nat → val} {bW : block}
    {lab : Array Nat} {D VI VL : Nat} {cap : Nat} {b : block} {st : Nat} {marks : Nat → Int}
    {MN : Nat}
    (hc : LoopCtx m le G be eo R cbe ceo ev bW lab D VI VL)
    (hM : MarksAt m cap b st marks) (hnc : n ≤ cap) (hMN : MN ≤ n)
    (hmina : PTree.get id.mina le = some (.Vint (ir MN)))
    (hQn : (∀ j < D, marks R.neighbors[VI + j]! = st → MN ≤ R.neighbors[VI + j]!) →
      ∀ le', (∀ x, x ≠ id.j → x ≠ id.k → x ≠ id.t2 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m)
    (hQr : (∃ j < D, marks R.neighbors[VI + j]! = st ∧ R.neighbors[VI + j]! < MN) →
      Q.ret E0 (.Vint (ir (-1))) m) :
    Wp xi sge F (jloop checkBody) Q empty_env le m := by
  have hn31 := hc.n31
  have hD31 := D_lt hc
  have hcap31 := hM.dyn.capLt
  let Fr := fun (le' : temp_env) => ∀ x, x ≠ id.j → x ≠ id.k → x ≠ id.t2 → PTree.get x le' = PTree.get x le
  let Ok := fun (k : Nat) => ∀ j < k, marks R.neighbors[VI + j]! = st → MN ≤ R.neighbors[VI + j]!
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ k, k ≤ D ∧ v = D - k ∧ PTree.get id.j le' = some (.Vlong (lr k)) ∧
      Ok k ∧ Fr le'
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ k, k < D ∧ v = D - k ∧ PTree.get id.j le' = some (.Vlong (lr k)) ∧
      Ok (k + 1) ∧ Fr le'
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := D - 0)
    ⟨rfl, rfl, rfl, 0, Nat.zero_le _, rfl, temps_gss _ _ _, fun j hj => absurd hj (by omega),
      fun x hx _ _ => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, k, hk, rfl, hj, hok, ho⟩
    have hc' := hc.temps fun x hx => by
      simp only [LoopLocal, not_or] at hx
      exact ho x hx.1 hx.2.1 hx.2.2.2
    have hmina' : PTree.get id.mina le' = some (.Vint (ir MN)) := by
      rw [ho _ (by decide) (by decide) (by decide)]; exact hmina
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' _ (tl id.j) = _ from hj,
      show Exec.evalExpr sge empty_env le' _ (tv id.di) = _ from hc'.hdi]
    simp only [typeof, cop, cast_l_i D hD31, Alloc.ltu_lr (a := k) (b := D) (by omega) (by omega)]
    by_cases hkD : k < D
    · rw [ite_eq_left (by simpa using hkD)]
      apply wp_skip
      have hx := hc.csmall k hkD
      have hcap0 : 0 < cap := by omega
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_ceat hc' hj hkD]
      let K := R.neighbors[VI + k]!
      have hkt : PTree.get id.k (PTree.set id.k (.Vint (ir K)) le') = some (.Vint (ir K)) := temps_gss _ _ _
      have hb := hM.bounds K (by omega)
      have hst := hM.val32
      have hel := eval_idx (chunk := .Mint16signed) (bo := b) (ofs := Ptrofs.zero)
        (le := PTree.set id.k (.Vint (ir K)) le')
        hM.arr hcap31 (eval_vmark1 (hM.dyn.ptr hcap0)) rfl rfl rfl (tv id.k) K (by omega) hkt rfl
      have hmn' : PTree.get id.mina (PTree.set id.k (.Vint (ir K)) le') = some (.Vint (ir MN)) := by
        rw [temps_gso _ _ (by decide)]; exact hmina'
      wp_step; wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hel, eval_val hM.valLd]
      simp only [markVals, typeof, cop]
      rw [ir_eq (a := marks K) (b := (st : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      have hFr : ∀ le'', (∀ x, x ≠ id.j → x ≠ id.k → x ≠ id.t2 → PTree.get x le'' = PTree.get x le') →
          Fr le'' := fun le'' h x h1 h2 h3 => by rw [h x h1 h2 h3, ho x h1 h2 h3]
      by_cases hm : marks K = st
      · rw [show decide (marks K = st) = true from decide_eq_true hm]
        simp (config := {decide := true}) only [cop, ite_true]
        wp_step; wp_step
        apply wp_set_eval
        rw [Exec.evalExpr, Exec.evalExpr, show Exec.evalExpr sge empty_env _ _ (tv id.k) = _ from hkt,
          show Exec.evalExpr sge empty_env _ _ (tv id.mina) = _ from hmn']
        simp only [typeof, cop]
        rw [ir_lt (a := (K : Int)) (b := (MN : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
        by_cases hlt : K < MN
        · rw [show decide ((K : Int) < MN) = true from decide_eq_true (by omega)]
          simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
          apply wp_if_eval
          simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ite_true]
          exact wp_ret_neg (hQr ⟨k, hkD, hm, hlt⟩)
        · rw [show decide ((K : Int) < MN) = false from decide_eq_false (by omega)]
          simp (config := {decide := true}) only [Val.of_bool, cop, ite_false]
          apply wp_if_eval
          simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ite_false]
          apply wp_skip
          refine ⟨by simp, rfl, rfl, k, hkD, rfl, by
            rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj, fun j hj' hmj => ?_,
            hFr _ fun x h1 h2 h3 => by rw [temps_gso _ _ h3, temps_gso _ _ h2]⟩
          rcases Nat.lt_or_ge j k with h | h
          · exact hok j h hmj
          · have : j = k := by omega
            subst this; omega
      · rw [show decide (marks K = st) = false from decide_eq_false hm]
        simp (config := {decide := true}) only [cop, ite_false]
        apply wp_set_eval
        simp only [Exec.evalExpr]
        apply wp_if_eval
        simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ite_false]
        apply wp_skip
        refine ⟨by simp, rfl, rfl, k, hkD, rfl, by
          rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj, fun j hj' hmj => ?_,
          hFr _ fun x h1 h2 h3 => by rw [temps_gso _ _ h3, temps_gso _ _ h2]⟩
        rcases Nat.lt_or_ge j k with h | h
        · exact hok j h hmj
        · have : j = k := by omega
          subst this; exact absurd hmj hm
    · rw [ite_eq_right (by simpa using hkD)]
      apply wp_break
      have : k = D := by omega
      subst this
      exact hQn hok le' ho
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, k, hk, rfl, hj, hok, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' _ (tl id.j) = _ from hj]
    simp only [Exec.evalExpr, typeof, cop, Alloc.add_lr_one]
    exact ⟨D - (k + 1), by omega, by simp, rfl, rfl, k + 1, by omega, rfl, temps_gss _ _ _, hok,
      fun x h1 h2 h3 => by rw [temps_gso _ _ h1, ho x h1 h2 h3]⟩

end NautyVerified.Proofs.Sparse.Testcanlab

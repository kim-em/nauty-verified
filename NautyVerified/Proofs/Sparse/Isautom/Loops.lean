import NautyVerified.Proofs.Sparse.Isautom.Syntax

/-!
# The two neighbour loops of `isautom_sg`

`wp_markLoop`: `for (j = 0; j < di; ++j) MARK1(p[e[vi+j]]);` marks exactly
the images under `p` of the `di` entries of `e` from `vi`, starting from
marks all below the stamp. `wp_checkLoop`:
`for (j = 0; j < di; ++j) if (ISNOTMARKED1(e[vpi+j])) return FALSE;`
returns `FALSE` exactly when one of the `di` entries from `vpi` is unmarked.
-/

namespace NautyVerified.Proofs.Sparse.Isautom

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse

variable {xi : ExternalCalls}

abbrev F := sparse.fn.isautom_sg

theorem cast_l_i (a : Nat) (h : a < 2147483648) :
    Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir a)) = lr a :=
  cast_int_long_ir (a := a) ⟨by omega, by omega⟩

/-- What the neighbour loops read. -/
structure LoopCtx {n : Nat} (m : mem) (le : temp_env) (G : Hex.SparseGraph n) (be : block)
    (eo : ptrofs) (bp : block) (pofs : ptrofs) (perm : Array Nat) (D : Nat) : Prop where
  he : PTree.get id.e le = some (.Vptr be eo)
  hp : PTree.get id.p le = some (.Vptr bp pofs)
  hdi : PTree.get id.di le = some (.Vint (ir D))
  earr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size
  parr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n
  psmall : ∀ x, x < n → perm[x]! < n
  n31 : n < 2147483648
  D31 : D < 2147483648

theorem LoopCtx.temps {n : Nat} {m : mem} {le le' : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {bp : block} {pofs : ptrofs} {perm : Array Nat} {D : Nat}
    (h : LoopCtx m le G be eo bp pofs perm D) (hle : ∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le) :
    LoopCtx m le' G be eo bp pofs perm D :=
  { h with
    he := by rw [hle _ (by decide)]; exact h.he
    hp := by rw [hle _ (by decide)]; exact h.hp
    hdi := by rw [hle _ (by decide)]; exact h.hdi }

theorem LoopCtx.mem {n : Nat} {m m' : mem} {le : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {bp : block} {pofs : ptrofs} {perm : Array Nat} {D : Nat}
    (h : LoopCtx m le G be eo bp pofs perm D) {S : block → Prop} (hu : Unch m m' S)
    (hbe : ¬ S be) (hbp : ¬ S bp) : LoopCtx m' le G be eo bp pofs perm D :=
  { h with earr := h.earr.unch hu hbe, parr := h.parr.unch hu hbp }

theorem nde_lt {n : Nat} {m : mem} {G : Hex.SparseGraph n} {be : block} {eo : ptrofs}
    (h : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size) :
    G.neighbors.size < 2 ^ 62 := by
  have hf : intOfZ (Ptrofs.unsigned eo) + 4 * (G.neighbors.size : Int) < 2 ^ 64 := h.fits
  have := h.base_nonneg
  omega

/-- `e[x + j]`, for `x + j` inside the neighbour array. -/
theorem eval_eat {n : Nat} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {bp : block} {pofs : ptrofs} {perm : Array Nat} {D : Nat}
    (h : LoopCtx m le G be eo bp pofs perm D) {x : Common.AST.ident} {X k : Nat}
    (hx : PTree.get x le = some (.Vlong (lr X))) (hj : PTree.get id.j le = some (.Vlong (lr k)))
    (hk : X + k < G.neighbors.size) :
    Exec.evalExpr sge empty_env le m (eat x) = some (eVals G (X + k)) := by
  have hnd := nde_lt h.earr
  refine eval_idx_l h.earr (by omega) (by simp only [Exec.evalExpr]; exact h.he) rfl rfl rfl _ _ hk ?_ rfl
  simp only [Exec.evalExpr, hx, hj, typeof, cop, lr_add]

theorem eVals_eq {n : Nat} (G : Hex.SparseGraph n) (j : Nat) :
    eVals G j = .Vint (ir ((Hex.GraphIso.Nauty.Sparse.Graph.ofGraph G).neighbor j)) := rfl

/-- The mark loop. -/
theorem wp_markLoop {n : Nat} {Q : Post} {le : temp_env} {m : mem} {G : Hex.SparseGraph n}
    {be : block} {eo : ptrofs} {bp : block} {pofs : ptrofs} {perm : Array Nat} {D VI : Nat}
    {cap : Nat} {b : block} {st : Nat} {marks : Nat → Int}
    (hc : LoopCtx m le G be eo bp pofs perm D) (hvi : PTree.get id.vi le = some (.Vlong (lr VI)))
    (hVD : VI + D ≤ G.neighbors.size) (hM : MarksAt m cap b st marks) (hnc : n ≤ cap)
    (hbelow : ∀ x < cap, marks x < st) (hsep : 0 < cap → b ≠ be ∧ b ≠ bp)
    (hQ : ∀ le' m' marks', MarksAt m' cap b st marks' →
      (∀ x < cap, marks' x = st ↔
        ∃ j < D, perm[(Hex.GraphIso.Nauty.Sparse.Graph.ofGraph G).neighbor (VI + j)]! = x) →
      Unch m m' (fun z => 0 < cap ∧ z = b) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F (jloop mark) Q empty_env le m := by
  let g := Hex.GraphIso.Nauty.Sparse.Graph.ofGraph G
  have hn31 := hc.n31
  have hD31 := hc.D31
  have hcap31 := hM.dyn.capLt
  let Hit := fun (k : Nat) (x : Nat) => ∃ j < k, perm[g.neighbor (VI + j)]! = x
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
    have hc' := (hc.temps ho).mem hu (fun ⟨h0, h⟩ => (hsep h0).1 h.symm)
      (fun ⟨h0, h⟩ => (hsep h0).2 h.symm)
    have hvi' : PTree.get id.vi le' = some (.Vlong (lr VI)) := by rw [ho _ (by decide)]; exact hvi
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj,
      show Exec.evalExpr sge empty_env le' m' (tv id.di) = _ from hc'.hdi]
    simp only [typeof, cop, cast_l_i D hD31, Alloc.ltu_lr (a := k) (b := D) (by omega) (by omega)]
    by_cases hkD : k < D
    · rw [ite_eq_left (by simpa using hkD)]
      apply wp_skip
      wp_step; wp_step
      have hkn : VI + k < G.neighbors.size := by omega
      have hnb := neighbor_lt G hkn
      have hpx := hc.psmall _ hnb
      have hcap0 : 0 < cap := by omega
      have hse := Search.sign_ext16_ir (a := (st : Int)) (by omega) (by have := hM'.val32; omega)
      refine wp_idx_store (chunk := .Mint16signed) (bo := b) (ofs := Ptrofs.zero) hM'.arr hcap31
        (eval_vmark1 (hM'.dyn.ptr hcap0)) rfl rfl rfl (iat id.p (eat id.vi)) _ (by omega)
        (eval_idx hc'.parr hn31 (by simp only [Exec.evalExpr]; exact hc'.hp) rfl rfl rfl _ _ hnb
          (eval_eat hc' hvi' hj hkn) rfl) rfl _ tshort rfl (.Vint (ir st)) (.Vint (ir st))
        (eval_val hM'.valLd) (by rw [Search.cast_ss, hse]) (by
          exact congrArg val.Vint hse) ?_
      intro m'' harr'' hu' hk' hg'
      let c := perm[g.neighbor (VI + k)]!
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

theorem free_empty (m : mem) : Mem.free_list m (blocks_of_env sge empty_env) = some m := rfl

/-- The check loop. -/
theorem wp_checkLoop {n : Nat} {Q : Post} {le : temp_env} {m : mem} {G : Hex.SparseGraph n}
    {be : block} {eo : ptrofs} {bp : block} {pofs : ptrofs} {perm : Array Nat} {D VP : Nat}
    {cap : Nat} {b : block} {st : Nat} {marks : Nat → Int}
    (hc : LoopCtx m le G be eo bp pofs perm D) (hvpi : PTree.get id.vpi le = some (.Vlong (lr VP)))
    (hVD : VP + D ≤ G.neighbors.size) (hM : MarksAt m cap b st marks) (hnc : n ≤ cap)
    (hQn : (∀ j < D, marks ((Hex.GraphIso.Nauty.Sparse.Graph.ofGraph G).neighbor (VP + j)) = st) →
      ∀ le', (∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m)
    (hQr : (∃ j < D, marks ((Hex.GraphIso.Nauty.Sparse.Graph.ofGraph G).neighbor (VP + j)) ≠ st) →
      Q.ret E0 (.Vint (ir 0)) m) :
    Wp xi sge F (jloop check) Q empty_env le m := by
  let g := Hex.GraphIso.Nauty.Sparse.Graph.ofGraph G
  have hn31 := hc.n31
  have hD31 := hc.D31
  have hcap31 := hM.dyn.capLt
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ k, k ≤ D ∧ v = D - k ∧ PTree.get id.j le' = some (.Vlong (lr k)) ∧
      (∀ j < k, marks (g.neighbor (VP + j)) = st) ∧ ∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ k, k < D ∧ v = D - k ∧ PTree.get id.j le' = some (.Vlong (lr k)) ∧
      (∀ j < k + 1, marks (g.neighbor (VP + j)) = st) ∧ ∀ x, x ≠ id.j → PTree.get x le' = PTree.get x le
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := D - 0)
    ⟨rfl, rfl, rfl, 0, Nat.zero_le _, rfl, temps_gss _ _ _, fun j hj => absurd hj (by omega),
      fun x hx => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, k, hk, rfl, hj, hok, ho⟩
    have hc' := hc.temps ho
    have hvpi' : PTree.get id.vpi le' = some (.Vlong (lr VP)) := by rw [ho _ (by decide)]; exact hvpi
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj,
      show Exec.evalExpr sge empty_env le' m' (tv id.di) = _ from hc'.hdi]
    simp only [typeof, cop, cast_l_i D hD31, Alloc.ltu_lr (a := k) (b := D) (by omega) (by omega)]
    by_cases hkD : k < D
    · rw [ite_eq_left (by simpa using hkD)]
      apply wp_skip
      wp_step; wp_step
      have hkn : VP + k < G.neighbors.size := by omega
      have hnb : g.neighbor (VP + k) < n := neighbor_lt G hkn
      have hcap0 : 0 < cap := by omega
      have hb := hM.bounds _ (show g.neighbor (VP + k) < cap by omega)
      have hst := hM.val32
      have hel := eval_idx (chunk := .Mint16signed) (bo := b) (ofs := Ptrofs.zero) hM.arr hcap31
        (eval_vmark1 (hM.dyn.ptr hcap0)) rfl rfl rfl (eat id.vpi) (g.neighbor (VP + k)) (by omega)
        (eval_eat hc' hvpi' hj hkn) rfl
      apply wp_if_eval
      rw [Exec.evalExpr, hel, eval_val hM.valLd]
      simp only [markVals, typeof, cop]
      rw [ir_eq (a := marks (g.neighbor (VP + k))) (b := (st : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
      by_cases hm : marks (g.neighbor (VP + k)) = st
      · rw [show decide (marks (g.neighbor (VP + k)) = st) = true from decide_eq_true hm]
        simp only [Bool.not_true]
        simp (config := {decide := true}) only [cop, ite_false]
        apply wp_skip
        refine ⟨by simp, rfl, rfl, k, hkD, rfl, hj, fun j hj' => ?_, ho⟩
        rcases Nat.lt_or_ge j k with h | h
        · exact hok j h
        · rw [show j = k by omega]; exact hm
      · rw [show decide (marks (g.neighbor (VP + k)) = st) = false from decide_eq_false hm]
        simp (config := {decide := true}) only [ite_true, cop]
        wp_step; wp_step
        apply wp_return_some_eval
        simp only [Exec.evalExpr, typeof, cop, sparse.fn.isautom_sg.fn_return_eq, free_empty]
        exact hQr ⟨k, hkD, hm⟩
    · rw [ite_eq_right (by simpa using hkD)]
      apply wp_break
      have : k = D := by omega
      subst this
      exact hQn hok le' ho
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, k, hk, rfl, hj, hok, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj]
    simp only [Exec.evalExpr, typeof, cop, Alloc.add_lr_one]
    exact ⟨D - (k + 1), by omega, by simp, rfl, rfl, k + 1, by omega, rfl, temps_gss _ _ _, hok,
      fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩

end NautyVerified.Proofs.Sparse.Isautom

import NautyVerified.Proofs.Sparse.Bestcell.Scan

/-!
# `bestcell_sg`'s counts

`wp_jloop`: `for (j = 0; j < di; ++j) body` with `size_t j`, as
`wp_forLoop`. `wp_zero`: `HITS[i] = COUNT[i] = 0` for the `nnt` cells.
`wp_hits`, `wp_counts`: the two passes over a row, as `hitStep` and
`countStep` fold over it. `wp_joins`: the loop over the cells leaves
`COUNT[i]` holding `countAt i` (the hits are all zero between cells,
`joins_zero`).
-/

namespace NautyVerified.Proofs.Sparse.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse NautyVerified.Program
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat cast_l_i)
open NautyVerified.Proofs.Sparse.Testcanlab (jloop)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

theorem wp_jloop {Q : Logic.Post} {e : env} {le : temp_env} {m : mem} (body : statement) (D : Nat)
    (hD : D < 2147483648) (Inv Mid : Nat → temp_env → mem → Prop)
    (hinv : ∀ k le m, Inv k le m → k ≤ D ∧ PTree.get id.j le = some (.Vlong (lr k)) ∧
      PTree.get id.di le = some (.Vint (ir D)))
    (hinit : Inv 0 (PTree.set id.j (.Vlong (lr 0)) le) m)
    (hbody : ∀ k le m, k < D → Inv k le m → Wp xi sge F body
      { normal := fun t _ le' m' => t = E0 ∧ Mid k le' m' } e le m)
    (hmid : ∀ k le m, Mid k le m → PTree.get id.j le = some (.Vlong (lr k)) ∧
      Inv (k + 1) (PTree.set id.j (.Vlong (lr (k + 1))) le) m)
    (hexit : ∀ le m, Inv D le m → Q.normal E0 e le m) :
    Wp xi sge F (jloop body) Q e le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩, seqPost,
    Post.after, E0_append]
  refine wp_loop (I := fun v t e' le' m' => t = E0 ∧ e = e' ∧ Inv (D - v) le' m' ∧ v ≤ D)
    (J := fun v t e' le' m' => t = E0 ∧ e = e' ∧ ∃ k, k < D ∧ v = D - k ∧ Mid k le' m') ?_ ?_
    (n := D) ⟨rfl, rfl, by simpa using hinit, Nat.le_refl _⟩
  · rintro v t e' le' m' ⟨rfl, rfl, hI, hv⟩
    obtain ⟨hk, hj, hdi⟩ := hinv _ _ _ hI
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge e le' m' (tl id.j) = _ from hj,
      show Exec.evalExpr sge e le' m' (tv id.di) = _ from hdi]
    simp only [typeof, cop, cast_l_i D hD, Alloc.ltu_lr (a := D - v) (b := D) (by omega) (by omega)]
    by_cases hlt : D - v < D
    · rw [ite_eq_left (by simpa using hlt)]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      refine wp_conseq ?_ ?_ ?_ ?_ (wp_env (hbody _ _ _ hlt hI))
      · rintro t e'' le'' m'' ⟨rfl, rfl, hm⟩
        exact ⟨by simp, rfl, D - v, hlt, by omega, hm⟩
      · intro _ _ _ _ h; exact h.elim
      · intro _ _ _ _ h; exact h.elim
      · intro _ _ _ h; exact h.elim
    · rw [ite_eq_right (by simpa using hlt)]
      apply wp_break
      simp only [E0_append]
      apply hexit
      rw [show D = D - v by omega]
      exact hI
  · rintro v t e' le' m' ⟨rfl, rfl, k, hk, rfl, hM⟩
    obtain ⟨hj, hI⟩ := hmid _ _ _ hM
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge e le' m' (tl id.j) = _ from hj]
    simp only [Exec.evalExpr, typeof, cop, Alloc.add_lr_one]
    refine ⟨D - (k + 1), by omega, by simp, trivial, ?_, by omega⟩
    rw [show D - (D - (k + 1)) = k + 1 by omega]
    simpa using hI

section
variable {n : Nat} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {bv : block} {vo : ptrofs}
  {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {bl : block} {lofs : ptrofs}
  {lab : Array Nat} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {level : Nat}
  {w : Fin 4 → block} {o1b : ptrofs}

/-- `for (i = 0; i < nnt; ++i) HITS[i] = COUNT[i] = 0;` -/
theorem wp_zero {Q : Logic.Post} {W3 W4 : Nat → val} {K : Nat}
    (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (hw3 : ArrayAt m .Mint32 (w 2) 0 W3 n) (hw4 : ArrayAt m .Mint32 (w 3) 0 W4 n)
    (hK : PTree.get id.nnt le = some (.Vint (ir K))) (hKn : K ≤ n)
    (hQ : ∀ le' m' W3' W4', ArrayAt m' .Mint32 (w 2) 0 W3' n → ArrayAt m' .Mint32 (w 3) 0 W4' n →
      (∀ k < K, W3' k = .Vint (ir 0) ∧ W4' k = .Vint (ir 0)) →
      Unch m m' (fun z => z = w 2 ∨ z = w 3) → Keep m m' (w 2) → Keep m m' (w 3) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ id.i → x ≠ id.tz → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (cloop zero) Q empty_env le m := by
  have hnlt := h.nlt
  let A := fun (k : Nat) (le' : temp_env) (m' : mem) => ∃ W3' W4',
    ArrayAt m' .Mint32 (w 2) 0 W3' n ∧ ArrayAt m' .Mint32 (w 3) 0 W4' n ∧
    (∀ j < k, W3' j = .Vint (ir 0) ∧ W4' j = .Vint (ir 0)) ∧
    Unch m m' (fun z => z = w 2 ∨ z = w 3) ∧ Keep m m' (w 2) ∧ Keep m m' (w 3) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, x ≠ id.i → x ≠ id.tz → PTree.get x le' = PTree.get x le
  refine wp_forLoop id.i id.nnt _ K (by omega)
    (fun k le' m' => k ≤ K ∧ PTree.get id.i le' = some (.Vint (ir k)) ∧
      PTree.get id.nnt le' = some (.Vint (ir K)) ∧ A k le' m')
    (fun k le' m' => PTree.get id.i le' = some (.Vint (ir k)) ∧ k < K ∧
      PTree.get id.nnt le' = some (.Vint (ir K)) ∧ A (k + 1) le' m') ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, hn', -⟩
    exact ⟨hk, hi, hn'⟩
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hK, W3, W4, hw3, hw4,
      fun _ h => absurd h (Nat.not_lt_zero _), Unch.refl _ _, Keep.refl _ _, Keep.refl _ _,
      fun _ h => h, fun x hx _ => temps_gso _ _ hx⟩
  · rintro k le' m' hk ⟨-, hi, hn', W3', W4', hw3', hw4', hz, hu, hk2, hk3, hg, ho⟩
    have hf := (h.unch (hu.mono fun _ hz => hz.elim (fun e => ⟨2, e⟩) (fun e => ⟨3, e⟩))).temps (le' := le') fun x hx => ho x
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop]
    have hi1 : PTree.get id.i (PTree.set id.tz (.Vint (ir 0)) le') = some (.Vint (ir k)) := by
      rw [temps_gso _ _ (by decide)]; exact hi
    refine wp_idx_store (pe := .Evar id.work4 (tptr tint)) (ofs := Ptrofs.zero) hw4' (by omega)
      (eval_gvar (k := 3) find_work4 (hf.wptr 3)) rfl rfl rfl (tv id.i) k (by omega)
      (by simp only [Exec.evalExpr]; exact hi1) rfl (tv id.tz) tint rfl (.Vint (ir 0)) (.Vint (ir 0))
      (by simp only [Exec.evalExpr, temps_gss]) rfl rfl ?_
    intro m1 hw4a hu1 hk1 hg1
    have hf1 := hf.unch (m' := m1) (hu1.mono fun _ hz => ⟨3, hz⟩)
    refine wp_idx_store (pe := .Evar id.work3 (tptr tint)) (ofs := Ptrofs.zero)
      (hw3'.unch hu1 (hf.wdist 2 3 (by decide))) (by omega)
      (eval_gvar (k := 2) find_work3 (hf1.wptr 2)) rfl rfl rfl (tv id.i) k (by omega)
      (by simp only [Exec.evalExpr]; exact hi1) rfl (tv id.tz) tint rfl (.Vint (ir 0)) (.Vint (ir 0))
      (by simp only [Exec.evalExpr, temps_gss]) rfl rfl ?_
    intro m2 hw3a hu2 hk2' hg2
    refine ⟨by simp, hi1, hk, by rw [temps_gso _ _ (by decide)]; exact hn', _, _, hw3a,
      hw4a.unch hu2 (hf.wdist 3 2 (by decide)), fun j hj => ?_,
      (hu.trans (hu1.mono fun _ hz => .inr hz)).trans (hu2.mono fun _ hz => .inl hz),
      (hk2.trans (Keep.unch hu1 (hf.wdist 2 3 (by decide)))).trans hk2',
      (hk3.trans hk1).trans (Keep.unch hu2 (hf.wdist 3 2 (by decide))),
      fun z hz => hg2 _ (hg1 _ (hg _ hz)), fun x a b => by rw [temps_gso _ _ b, ho x a b]⟩
    by_cases hjk : j = k
    · subst hjk; exact ⟨upd_same _ _ _, upd_same _ _ _⟩
    · rw [upd_ne _ _ hjk, upd_ne _ _ hjk]; exact hz j (by omega)
  · rintro k le' m' ⟨hi, hk, hn', W3', W4', hw3', hw4', hz, hu, hk2, hk3, hg, ho⟩
    exact ⟨hi, by omega, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hn', W3', W4', hw3',
      hw4', hz, hu, hk2, hk3, hg, fun x a b => by rw [temps_gso _ _ a, ho x a b]⟩
  · rintro le' m' ⟨-, -, -, W3', W4', hw3', hw4', hz, hu, hk2, hk3, hg, ho⟩
    exact hQ le' m' W3' W4' hw3' hw4' hz hu hk2 hk3 hg ho

/-- `NNTCELL[e[vi+j]]`. -/
theorem eval_nnt (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    {W2 : Nat → val} (hw2 : ArrayAt m .Mint32 (w 1) 0 W2 n) {VI p : Nat}
    (hvi : PTree.get id.vi le = some (.Vlong (lr VI))) (hj : PTree.get id.j le = some (.Vlong (lr p)))
    (hp : VI + p < G.neighbors.size) :
    Exec.evalExpr sge empty_env le m nntAt = some (W2 ((Graph.ofGraph G).neighbor (VI + p))) := by
  have hnd := Isautom.nde_lt h.earr
  have hnlt := h.nlt
  refine eval_idx (pe := .Evar id.work2 (tptr tint)) (ofs := Ptrofs.zero) hw2 (by omega)
    (eval_gvar (k := 1) find_work2 (h.wptr 1)) rfl rfl rfl _ _ (neighbor_lt G hp) ?_ rfl
  refine eval_idx_l (pe := .Etempvar id.e (tptr tint)) h.earr (by omega)
    (by simp only [Exec.evalExpr]; exact h.he) rfl rfl rfl _ (VI + p) hp ?_ rfl
  simp only [Exec.evalExpr, hvi, hj, typeof, cop, lr_add]

/-- The temporaries the row loops set. -/
def RowLocal (x : ident) : Prop := x = id.j ∨ x = id.k ∨ x = id.th

instance (x : ident) : Decidable (RowLocal x) := by unfold RowLocal; infer_instance

theorem args_not_row : ∀ x, Args x → ¬ RowLocal x := by
  intro x hx hs
  rcases hs with rfl | rfl | rfl <;> revert hx <;> decide

/-- The first pass over a row: `k = NNTCELL[e[vi+j]]; if (k != n) ++HITS[k];` -/
theorem wp_hits {Q : Logic.Post} {c : Cells} {W2 W3 : Nat → val} {H : Array Nat} {VI D : Nat}
    (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (hgood : Good n lab c)
    (hw2 : ArrayAt m .Mint32 (w 1) 0 W2 n) (hW2 : ∀ v < n, W2 v = .Vint (ir (c.nntcell[v]! : Int)))
    (hvi : PTree.get id.vi le = some (.Vlong (lr VI))) (hdi : PTree.get id.di le = some (.Vint (ir D)))
    (hVD : VI + D ≤ G.neighbors.size) (hDn : D ≤ n)
    (hH : H.size = c.starts.size) (hHb : ∀ k : Nat, H[k]! ≤ n)
    (hw3 : ArrayAt m .Mint32 (w 2) 0 W3 n) (hW3 : ∀ k < c.starts.size, W3 k = .Vint (ir (H[k]! : Int)))
    (hQ : ∀ le' m' W3', ArrayAt m' .Mint32 (w 2) 0 W3' n →
      (∀ k < c.starts.size, W3' k = .Vint (ir
        (((List.range' VI D).foldl (hitStep (Graph.ofGraph G) c.nntcell) H)[k]! : Int))) →
      Unch m m' (· = w 2) → Keep m m' (w 2) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, ¬ RowLocal x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F (jloop hitBody) Q empty_env le m := by
  have hnlt := h.nlt
  have hKn : c.starts.size ≤ n := by have := hgood.half; have := hgood.fle; omega
  let g := Graph.ofGraph G
  let S := fun p => (List.range' VI p).foldl (hitStep g c.nntcell) H
  have hSs : ∀ p, S (p + 1) = hitStep g c.nntcell (S p) (VI + p) := fun p => by
    simp only [S, List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hSb : ∀ p, ∀ k : Nat, (S p)[k]! ≤ n + p := fun p k => by
    have := (hit_fold g c.nntcell (List.range' VI p) H).2.1 k
    simp only [List.length_range'] at this
    have := hHb k
    simp only [S]; omega
  have hSz : ∀ p, (S p).size = c.starts.size := fun p => by
    rw [← hH]; exact (hit_fold g c.nntcell (List.range' VI p) H).1
  let A := fun (p : Nat) (le' : temp_env) (m' : mem) => ∃ W3', ArrayAt m' .Mint32 (w 2) 0 W3' n ∧
    (∀ k < c.starts.size, W3' k = .Vint (ir ((S p)[k]! : Int))) ∧ Unch m m' (· = w 2) ∧
    Keep m m' (w 2) ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, ¬ RowLocal x → PTree.get x le' = PTree.get x le
  refine wp_jloop _ D (by omega)
    (fun p le' m' => p ≤ D ∧ PTree.get id.j le' = some (.Vlong (lr p)) ∧
      PTree.get id.di le' = some (.Vint (ir D)) ∧ A p le' m')
    (fun p le' m' => PTree.get id.j le' = some (.Vlong (lr p)) ∧ p < D ∧
      PTree.get id.di le' = some (.Vint (ir D)) ∧ A (p + 1) le' m') ?_ ?_ ?_ ?_ ?_
  · rintro p le' m' ⟨hp, hj, hd, -⟩
    exact ⟨hp, hj, hd⟩
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hdi, W3, hw3, hW3,
      Unch.refl _ _, Keep.refl _ _, fun _ h => h, fun x hx => temps_gso _ _ fun e => hx (.inl e)⟩
  · rintro p le' m' hp ⟨-, hj, hd, W3', hw3', hW3', hu, hk, hg, ho⟩
    have hf := (h.unch (hu.mono fun _ hz => ⟨2, hz⟩)).temps (le' := le') fun x hx =>
      ho x (args_not_row x hx)
    have hvi' : PTree.get id.vi le' = some (.Vlong (lr VI)) := by rw [ho _ (by decide)]; exact hvi
    have hw2' := hw2.unch hu (hf.wdist 1 2 (by decide))
    have hpn : VI + p < G.neighbors.size := by omega
    have hnb := neighbor_lt G hpn
    obtain ⟨x, hx⟩ : ∃ x, x = c.nntcell[g.neighbor (VI + p)]! := ⟨_, rfl⟩
    have hxi := hgood.idx _ hnb
    rw [← hx] at hxi
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_nnt hf hw2' hvi' hj hpn, hW2 _ hnb, ← hx]
    let le1 := PTree.set id.k (.Vint (ir (x : Int))) le'
    have hk1 : PTree.get id.k le1 = some (.Vint (ir (x : Int))) := temps_gss _ _ _
    have hf1 := hf.temps (le' := le1) fun z hz => temps_gso _ _ (by
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    show Wp xi sge F _ _ empty_env le1 m'
    wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hk1, hf1.hn, typeof, cop]
    rw [ir_eq (a := (x : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have hS1 := hSs p
    by_cases hxn : x = n
    · rw [ite_eq_right (by simp [hxn])]
      apply wp_skip
      have : S (p + 1) = S p := by
        rw [hS1]; unfold hitStep; rw [← hx, ite_eq_right (by simp [hxn])]
      refine ⟨by simp, by rw [temps_gso _ _ (by decide)]; exact hj, hp, by rw [temps_gso _ _ (by decide)]; exact hd,
        W3', hw3', by rw [this]; exact hW3', hu, hk, hg, fun z hz => by
          rw [temps_gso _ _ (fun e => hz (.inr (.inl e))), ho z hz]⟩
    · rw [ite_eq_left (by simp; omega)]
      have hxK : x < c.starts.size := by omega
      have hv := eval_idx (pe := .Evar id.work3 (tptr tint)) (ofs := Ptrofs.zero) (e := empty_env) (le := le1)
        hw3' (by omega) (eval_gvar (k := 2) find_work3 (hf1.wptr 2)) rfl rfl rfl (tv id.k) x (by omega)
        hk1 rfl
      rw [hW3' x hxK] at hv
      have hb := hSb p x
      wp_step; wp_step
      refine wp_idx_store (pe := .Evar id.work3 (tptr tint)) (ofs := Ptrofs.zero) hw3' (by omega)
        (eval_gvar (k := 2) find_work3 (hf1.wptr 2)) rfl rfl rfl (tv id.k) x (by omega) hk1 rfl _ tint rfl
        (.Vint (ir (((S p)[x]! + 1 : Nat) : Int))) (.Vint (ir (((S p)[x]! + 1 : Nat) : Int)))
        (by rw [Exec.evalExpr, hv]; simp only [Exec.evalExpr, typeof, cop, ir_add]; push_cast; rfl)
        rfl rfl ?_
      intro m1 hw3a hu1 hk1' hg1
      have hS' : S (p + 1) = (S p).set! x ((S p)[x]! + 1) := by
        rw [hS1]; unfold hitStep; rw [← hx, ite_eq_left (by simp [hxn])]
      refine ⟨by simp, by rw [temps_gso _ _ (by decide)]; exact hj, hp, by rw [temps_gso _ _ (by decide)]; exact hd,
        _, hw3a, fun k hk' => ?_, hu.trans hu1, hk.trans hk1', fun z hz => hg1 _ (hg _ hz), fun z hz => by
          rw [temps_gso _ _ (fun e => hz (.inr (.inl e))), ho z hz]⟩
      rw [hS', get_set]
      by_cases hkx : k = x
      · subst hkx; rw [upd_same, ite_eq_left ⟨rfl, by rw [hSz]; exact hxK⟩]
      · rw [upd_ne _ _ hkx, ite_eq_right (fun e => hkx e.1.symm)]; exact hW3' k hk'
  · rintro p le' m' ⟨hj, hp, hd, W3', hw3', hW3', hu, hk, hg, ho⟩
    exact ⟨hj, by omega, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hd, W3', hw3', hW3', hu, hk,
      hg, fun x hx => by rw [temps_gso _ _ (fun e => hx (.inl e)), ho x hx]⟩
  · rintro le' m' ⟨-, -, -, W3', hw3', hW3', hu, hk, hg, ho⟩
    exact hQ le' m' W3' hw3' hW3' hu hk hg ho

/-- `th = HITS[k] > 0 && HITS[k] < SIZE[k];` -/
theorem wp_th {Q : Logic.Post} {c : Cells} {W1 W3 : Nat → val} {x hx : Nat}
    (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (hgood : Good n lab c)
    (hw1 : ArrayAt m .Mint32 (w 0) 0 W1 n)
    (hW1 : ∀ k < c.starts.size, W1 (n / 2 + k) = .Vint (ir (c.sizes[k]! : Int)))
    (hw3 : ArrayAt m .Mint32 (w 2) 0 W3 n) (hW3 : W3 x = .Vint (ir (hx : Int)))
    (hxK : x < c.starts.size) (hxb : hx < 2147483648)
    (hk : PTree.get id.k le = some (.Vint (ir (x : Int))))
    (hQ : Q.normal E0 empty_env (PTree.set id.th
      (Val.of_bool (decide (hx > 0) && decide (hx < c.sizes[x]!))) le) m) :
    Wp xi sge F (sk (.Sifthenelse (.Ebinop .Ogt (gat id.work3 (tv id.k)) (ci 0 tint) tint)
      (sk (.Sset id.th (.Ecast (.Ebinop .Olt (gat id.work3 (tv id.k)) (iat id.work1b (tv id.k)) tint)
        tbool)))
      (.Sset id.th (ci 0 tint)))) Q empty_env le m := by
  have hnlt := h.nlt
  have hKn : 2 * c.starts.size ≤ n := by have := hgood.half; have := hgood.fle; omega
  have hsz := hgood.sizeLe x hxK
  have hv := eval_idx (pe := .Evar id.work3 (tptr tint)) (ofs := Ptrofs.zero) (e := empty_env) (le := le)
    hw3 (by omega) (eval_gvar (k := 2) find_work3 (h.wptr 2)) rfl rfl rfl (tv id.k) x (by omega) hk rfl
  rw [hW3] at hv
  wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, hv]
  simp only [Exec.evalExpr, typeof, cop]
  rw [ir_lt (a := 0) (b := (hx : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases h0 : 0 < hx
  · rw [ite_eq_left (by simpa using h0)]
    have hs := eval_off (pe := .Etempvar id.work1b (tptr tint)) (e := empty_env) (le := le) (off := n / 2)
      hw1 (by omega) (by simp only [Exec.evalExpr]; exact h.h1b) rfl h.o1b (tv id.k) x (by omega) hk rfl
    rw [hW1 x hxK] at hs
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, Exec.evalExpr, hv, hs]
    simp only [typeof, cop]
    rw [ir_lt (a := (hx : Int)) (b := (c.sizes[x]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have e : (decide (hx > 0) && decide (hx < c.sizes[x]!)) = decide ((hx : Int) < c.sizes[x]!) := by
      simp only [h0, decide_true, Bool.true_and]; exact decide_eq_decide.2 (by omega)
    rw [e] at hQ
    cases hb : decide ((hx : Int) < c.sizes[x]!) <;> rw [hb] at hQ <;> exact hQ
  · rw [ite_eq_right (by simpa using h0)]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    have e : (decide (hx > 0) && decide (hx < c.sizes[x]!)) = false := by simp; omega
    rw [e] at hQ
    exact hQ

/-- The second pass over the row of cell `I`: `k = NNTCELL[e[vi+j]]; if (k != n)
{ if (HITS[k] > 0 && HITS[k] < SIZE[k]) ++COUNT[i]; HITS[k] = 0; }` -/
theorem wp_counts {Q : Logic.Post} {c : Cells} {W1 W2 W3 W4 : Nat → val} {H : Array Nat}
    {VI D I : Nat}
    (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (hgood : Good n lab c)
    (hw1 : ArrayAt m .Mint32 (w 0) 0 W1 n)
    (hW1 : ∀ k < c.starts.size, W1 (n / 2 + k) = .Vint (ir (c.sizes[k]! : Int)))
    (hw2 : ArrayAt m .Mint32 (w 1) 0 W2 n) (hW2 : ∀ v < n, W2 v = .Vint (ir (c.nntcell[v]! : Int)))
    (hvi : PTree.get id.vi le = some (.Vlong (lr VI))) (hdi : PTree.get id.di le = some (.Vint (ir D)))
    (hVD : VI + D ≤ G.neighbors.size) (hDn : D ≤ n)
    (hi : PTree.get id.i le = some (.Vint (ir (I : Int)))) (hI : I < c.starts.size)
    (hH : H.size = c.starts.size) (hHb : ∀ k : Nat, H[k]! ≤ 2 * n)
    (hw3 : ArrayAt m .Mint32 (w 2) 0 W3 n) (hW3 : ∀ k < c.starts.size, W3 k = .Vint (ir (H[k]! : Int)))
    (hw4 : ArrayAt m .Mint32 (w 3) 0 W4 n) (hW4 : W4 I = .Vint (ir 0))
    (hQ : ∀ le' m' W3' W4', ArrayAt m' .Mint32 (w 2) 0 W3' n → ArrayAt m' .Mint32 (w 3) 0 W4' n →
      (∀ k < c.starts.size, W3' k = .Vint (ir
        (((List.range' VI D).foldl (countStep (Graph.ofGraph G) c.nntcell c.sizes) (H, 0)).1[k]! :
          Int))) →
      W4' I = .Vint (ir
        (((List.range' VI D).foldl (countStep (Graph.ofGraph G) c.nntcell c.sizes) (H, 0)).2 : Int)) →
      (∀ k, k ≠ I → W4' k = W4 k) →
      Unch m m' (fun z => z = w 2 ∨ z = w 3) → Keep m m' (w 2) → Keep m m' (w 3) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, ¬ RowLocal x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F (jloop countBody) Q empty_env le m := by
  have hnlt := h.nlt
  have hKn : 2 * c.starts.size ≤ n := by have := hgood.half; have := hgood.fle; omega
  let g := Graph.ofGraph G
  let S := fun p => (List.range' VI p).foldl (countStep g c.nntcell c.sizes) (H, 0)
  have hSs : ∀ p, S (p + 1) = countStep g c.nntcell c.sizes (S p) (VI + p) := fun p => by
    simp only [S, List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hSb : ∀ p, (S p).1.size = c.starts.size ∧ (∀ k : Nat, (S p).1[k]! ≤ 2 * n) ∧ (S p).2 ≤ p := fun p => by
    obtain ⟨a, b, d⟩ := count_bound g c.nntcell c.sizes (List.range' VI p) H 0
    simp only [List.length_range'] at d
    exact ⟨by simp only [S]; rw [a, hH], fun k => by have := b k; have := hHb k; simp only [S]; omega,
      by simp only [S]; omega⟩
  have hFr : ∀ {m' : mem} {le' : temp_env}, Unch m m' (fun z => z = w 2 ∨ z = w 3) →
      (∀ x, ¬ RowLocal x → PTree.get x le' = PTree.get x le) →
      Frame m' le' G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b := fun hu ho =>
    (h.unch (hu.mono fun _ hz => hz.elim (fun e => ⟨2, e⟩) (fun e => ⟨3, e⟩))).temps fun x hx =>
      ho x (args_not_row x hx)
  have hn23 : ∀ z, z = w 0 ∨ z = w 1 → ¬ (z = w 2 ∨ z = w 3) := by
    rintro z (rfl | rfl) (e | e)
    · exact h.wdist 0 2 (by decide) e
    · exact h.wdist 0 3 (by decide) e
    · exact h.wdist 1 2 (by decide) e
    · exact h.wdist 1 3 (by decide) e
  let A := fun (p : Nat) (le' : temp_env) (m' : mem) => ∃ W3' W4',
    ArrayAt m' .Mint32 (w 2) 0 W3' n ∧ ArrayAt m' .Mint32 (w 3) 0 W4' n ∧
    (∀ k < c.starts.size, W3' k = .Vint (ir ((S p).1[k]! : Int))) ∧
    W4' I = .Vint (ir ((S p).2 : Int)) ∧ (∀ k, k ≠ I → W4' k = W4 k) ∧
    Unch m m' (fun z => z = w 2 ∨ z = w 3) ∧ Keep m m' (w 2) ∧ Keep m m' (w 3) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, ¬ RowLocal x → PTree.get x le' = PTree.get x le
  refine wp_jloop _ D (by omega)
    (fun p le' m' => p ≤ D ∧ PTree.get id.j le' = some (.Vlong (lr p)) ∧
      PTree.get id.di le' = some (.Vint (ir D)) ∧ A p le' m')
    (fun p le' m' => PTree.get id.j le' = some (.Vlong (lr p)) ∧ p < D ∧
      PTree.get id.di le' = some (.Vint (ir D)) ∧ A (p + 1) le' m') ?_ ?_ ?_ ?_ ?_
  · rintro p le' m' ⟨hp, hj, hd, -⟩
    exact ⟨hp, hj, hd⟩
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hdi, W3, W4, hw3, hw4,
      hW3, hW4, fun _ _ => rfl, Unch.refl _ _, Keep.refl _ _, Keep.refl _ _, fun _ h => h,
      fun x hx => temps_gso _ _ fun e => hx (.inl e)⟩
  · rintro p le' m' hp ⟨-, hj, hd, W3', W4', hw3', hw4', hW3', hW4', hW4o, hu, hk3, hk4, hg, ho⟩
    have hf := hFr hu ho
    have hvi' : PTree.get id.vi le' = some (.Vlong (lr VI)) := by rw [ho _ (by decide)]; exact hvi
    have hi' : PTree.get id.i le' = some (.Vint (ir (I : Int))) := by rw [ho _ (by decide)]; exact hi
    have hw2' := hw2.unch hu (hn23 _ (.inr rfl))
    have hw1' := hw1.unch hu (hn23 _ (.inl rfl))
    have hpn : VI + p < G.neighbors.size := by omega
    have hnb := neighbor_lt G hpn
    obtain ⟨x, hx⟩ : ∃ x, x = c.nntcell[g.neighbor (VI + p)]! := ⟨_, rfl⟩
    have hxi := hgood.idx _ hnb
    rw [← hx] at hxi
    obtain ⟨hSz, hSbd, hSc⟩ := hSb p
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_nnt hf hw2' hvi' hj hpn, hW2 _ hnb, ← hx]
    let le1 := PTree.set id.k (.Vint (ir (x : Int))) le'
    have hk1 : PTree.get id.k le1 = some (.Vint (ir (x : Int))) := temps_gss _ _ _
    have hf1 := hf.temps (le' := le1) fun z hz => temps_gso _ _ (by
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    show Wp xi sge F _ _ empty_env le1 m'
    wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hk1, hf1.hn, typeof, cop]
    rw [ir_eq (a := (x : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have hS1 := hSs p
    by_cases hxn : x = n
    · rw [ite_eq_right (by simp [hxn])]
      apply wp_skip
      have : S (p + 1) = S p := by
        rw [hS1]; unfold countStep; rw [← hx, ite_eq_right (by simp [hxn])]
      refine ⟨by simp, by rw [temps_gso _ _ (by decide)]; exact hj, hp,
        by rw [temps_gso _ _ (by decide)]; exact hd, W3', W4', hw3', hw4', by rw [this]; exact hW3',
        by rw [this]; exact hW4', hW4o, hu, hk3, hk4, hg, fun z hz => by
          rw [temps_gso _ _ (fun e => hz (.inr (.inl e))), ho z hz]⟩
    · rw [ite_eq_left (by simp; omega)]
      have hxK : x < c.starts.size := by omega
      have hhx := hSbd x
      obtain ⟨b, hb⟩ : ∃ b, b = (decide ((S p).1[x]! > 0) && decide ((S p).1[x]! < c.sizes[x]!)) :=
        ⟨_, rfl⟩
      have hS' : S (p + 1) = ((S p).1.set! x 0, if b then (S p).2 + 1 else (S p).2) := by
        rw [hS1]; unfold countStep; rw [← hx, ite_eq_left (by simp; omega), hb]
      wp_step; wp_step
      refine wp_th hf1 hgood hw1' hW1 hw3' (hW3' x hxK) hxK (by omega) hk1 ?_
      rw [← hb]
      let le2 := PTree.set id.th (Val.of_bool b) le1
      have hk2 : PTree.get id.k le2 = some (.Vint (ir (x : Int))) := by
        rw [temps_gso _ _ (by decide)]; exact hk1
      have hi2 : PTree.get id.i le2 = some (.Vint (ir (I : Int))) := by
        rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hi'
      have hf2 := hf1.temps (le' := le2) fun z hz => temps_gso _ _ (by
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      -- the tail `HITS[k] = 0;`, from any `COUNT`
      have tail : ∀ m2 W4'', ArrayAt m2 .Mint32 (w 3) 0 W4'' n →
          W4'' I = .Vint (ir ((S (p + 1)).2 : Int)) → (∀ k, k ≠ I → W4'' k = W4 k) →
          Unch m' m2 (· = w 3) → Keep m' m2 (w 3) →
          (∀ z, Mem.valid_block m' z → Mem.valid_block m2 z) →
          Wp xi sge F (sk (.Sassign (gat id.work3 (tv id.k)) (ci 0 tint)))
            { normal := fun t _ le' m' => t = E0 ∧ PTree.get id.j le' = some (.Vlong (lr p)) ∧ p < D ∧
                PTree.get id.di le' = some (.Vint (ir D)) ∧ A (p + 1) le' m' } empty_env le2 m2 := by
        intro m2 W4'' hw4a hW4a hW4b hu2 hk2' hg2
        have hf3 := hf2.unch (m' := m2) (hu2.mono fun _ hz => ⟨3, hz⟩)
        wp_step; wp_step
        refine wp_idx_store (pe := .Evar id.work3 (tptr tint)) (ofs := Ptrofs.zero)
          (hw3'.unch hu2 (h.wdist 2 3 (by decide))) (by omega)
          (eval_gvar (k := 2) find_work3 (hf3.wptr 2)) rfl rfl rfl (tv id.k) x (by omega) hk2 rfl
          (ci 0 tint) tint rfl (.Vint (ir 0)) (.Vint (ir 0)) rfl rfl rfl ?_
        intro m3 hw3a hu3 hk3' hg3
        refine ⟨by simp, by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj, hp,
          by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hd, _, W4'', hw3a,
          hw4a.unch hu3 (h.wdist 3 2 (by decide)), fun k hk' => ?_, hW4a, hW4b,
          (hu.trans (hu2.mono fun _ hz => .inr hz)).trans (hu3.mono fun _ hz => .inl hz),
          (hk3.trans (Keep.unch hu2 (h.wdist 2 3 (by decide)))).trans hk3',
          (hk4.trans hk2').trans (Keep.unch hu3 (h.wdist 3 2 (by decide))),
          fun z hz => hg3 _ (hg2 _ (hg _ hz)), fun z hz => by
            rw [temps_gso _ _ (fun e => hz (.inr (.inr e))), temps_gso _ _ (fun e => hz (.inr (.inl e))),
              ho z hz]⟩
        rw [hS', get_set]
        by_cases hkx : k = x
        · subst hkx; rw [upd_same, ite_eq_left ⟨rfl, by rw [hSz]; exact hxK⟩]; rfl
        · rw [upd_ne _ _ hkx, ite_eq_right (fun e => hkx e.1.symm)]; exact hW3' k hk'
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        apply wp_skip
        exact tail m' W4' hw4' (by rw [hS']; exact hW4') hW4o (Unch.refl _ _) (Keep.refl _ _) fun _ h => h
      · simp only [ite_true]
        have hv := eval_idx (pe := .Evar id.work4 (tptr tint)) (ofs := Ptrofs.zero) (e := empty_env)
          (le := le2) hw4' (by omega) (eval_gvar (k := 3) find_work4 (hf2.wptr 3)) rfl rfl rfl (tv id.i) I
          (by omega) hi2 rfl
        rw [hW4'] at hv
        wp_step; wp_step
        refine wp_idx_store (pe := .Evar id.work4 (tptr tint)) (ofs := Ptrofs.zero) hw4' (by omega)
          (eval_gvar (k := 3) find_work4 (hf2.wptr 3)) rfl rfl rfl (tv id.i) I (by omega) hi2 rfl _ tint
          rfl (.Vint (ir (((S p).2 + 1 : Nat) : Int))) (.Vint (ir (((S p).2 + 1 : Nat) : Int)))
          (by rw [Exec.evalExpr, hv]; simp only [Exec.evalExpr, typeof, cop, ir_add]; push_cast; rfl)
          rfl rfl ?_
        intro m2 hw4a hu2 hk2' hg2
        exact tail m2 _ hw4a (by rw [upd_same, hS']; rfl)
          (fun k hk' => by rw [upd_ne _ _ hk', hW4o k hk']) hu2 hk2' hg2
  · rintro p le' m' ⟨hj, hp, hd, W3', W4', hw3', hw4', hW3', hW4', hW4o, hu, hk3, hk4, hg, ho⟩
    exact ⟨hj, by omega, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hd, W3', W4', hw3',
      hw4', hW3', hW4', hW4o, hu, hk3, hk4, hg, fun x hx => by
        rw [temps_gso _ _ (fun e => hx (.inl e)), ho x hx]⟩
  · rintro le' m' ⟨-, -, -, W3', W4', hw3', hw4', hW3', hW4', hW4o, hu, hk3, hk4, hg, ho⟩
    exact hQ le' m' W3' W4' hw3' hw4' hW3' hW4' hW4o hu hk3 hk4 hg ho

/-- The temporaries the loop over the cells sets. -/
def JLocal (x : ident) : Prop := x = id.i ∨ x = id.vi ∨ x = id.di ∨ RowLocal x

instance (x : ident) : Decidable (JLocal x) := by unfold JLocal; infer_instance

theorem args_not_j : ∀ x, Args x → ¬ JLocal x := by
  intro x hx hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hx <;> decide

/-- `for (i = 0; i < nnt; ++i) { vi = v[lab[START[i]]]; di = d[lab[START[i]]]; … }` -/
theorem wp_joins {Q : Logic.Post} {c : Cells} {W1 W2 W3 W4 : Nat → val}
    (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (hgood : Good n lab c)
    (hw1 : ArrayAt m .Mint32 (w 0) 0 W1 n)
    (hW1 : ∀ k < c.starts.size, W1 k = .Vint (ir (c.starts[k]! : Int)) ∧
      W1 (n / 2 + k) = .Vint (ir (c.sizes[k]! : Int)))
    (hw2 : ArrayAt m .Mint32 (w 1) 0 W2 n) (hW2 : ∀ v < n, W2 v = .Vint (ir (c.nntcell[v]! : Int)))
    (hw3 : ArrayAt m .Mint32 (w 2) 0 W3 n) (hw4 : ArrayAt m .Mint32 (w 3) 0 W4 n)
    (hz : ∀ k < c.starts.size, W3 k = .Vint (ir 0) ∧ W4 k = .Vint (ir 0))
    (hK : PTree.get id.nnt le = some (.Vint (ir (c.starts.size : Int))))
    (hQ : ∀ le' m' W4', ArrayAt m' .Mint32 (w 3) 0 W4' n →
      (∀ k < c.starts.size, W4' k = .Vint (ir (countAt (Graph.ofGraph G) lab c k : Int))) →
      Unch m m' (fun z => z = w 2 ∨ z = w 3) → Keep m m' (w 2) → Keep m m' (w 3) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, ¬ JLocal x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F (cloop cellJoins) Q empty_env le m := by
  have hnlt := h.nlt
  have hKn : 2 * c.starts.size ≤ n := by have := hgood.half; have := hgood.fle; omega
  let g := Graph.ofGraph G
  let K := c.starts.size
  let P := fun q => ((List.range q).foldl (pick g lab c) (Array.replicate K 0, 0, 0)).1
  have hP : ∀ q, Zero K (P q) := fun q => zero_pick g lab c _ _ (zero_init K)
  have hn23 : ∀ z, z = w 0 ∨ z = w 1 → ¬ (z = w 2 ∨ z = w 3) := by
    rintro z (rfl | rfl) (e | e)
    · exact h.wdist 0 2 (by decide) e
    · exact h.wdist 0 3 (by decide) e
    · exact h.wdist 1 2 (by decide) e
    · exact h.wdist 1 3 (by decide) e
  have hm23 : ∀ {m' : mem}, Unch m m' (fun z => z = w 2 ∨ z = w 3) → Keep m m' (w 2) →
      Keep m m' (w 3) → Mod m m' w := fun hu hk2 hk3 =>
    ⟨hu.mono fun _ hz => hz.elim (fun e => ⟨2, e⟩) (fun e => ⟨3, e⟩), fun k => by
      match k with
      | 0 => exact Keep.unch hu (hn23 _ (.inl rfl))
      | 1 => exact Keep.unch hu (hn23 _ (.inr rfl))
      | 2 => exact hk2
      | 3 => exact hk3⟩
  let A := fun (q : Nat) (le' : temp_env) (m' : mem) => ∃ W3' W4',
    ArrayAt m' .Mint32 (w 2) 0 W3' n ∧ ArrayAt m' .Mint32 (w 3) 0 W4' n ∧
    (∀ k < K, W3' k = .Vint (ir 0)) ∧ (∀ k < q, W4' k = .Vint (ir (countAt g lab c k : Int))) ∧
    (∀ k, q ≤ k → k < K → W4' k = .Vint (ir 0)) ∧ Unch m m' (fun z => z = w 2 ∨ z = w 3) ∧
    Keep m m' (w 2) ∧ Keep m m' (w 3) ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, ¬ JLocal x → PTree.get x le' = PTree.get x le
  refine wp_forLoop id.i id.nnt _ K (by omega)
    (fun q le' m' => q ≤ K ∧ PTree.get id.i le' = some (.Vint (ir q)) ∧
      PTree.get id.nnt le' = some (.Vint (ir K)) ∧ A q le' m')
    (fun q le' m' => PTree.get id.i le' = some (.Vint (ir q)) ∧ q < K ∧
      PTree.get id.nnt le' = some (.Vint (ir K)) ∧ A (q + 1) le' m') ?_ ?_ ?_ ?_ ?_
  · rintro q le' m' ⟨hq, hi, hn', -⟩
    exact ⟨hq, hi, hn'⟩
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hK, W3, W4, hw3, hw4,
      fun k hk => (hz k hk).1, fun _ h => absurd h (Nat.not_lt_zero _), fun k _ hk => (hz k hk).2,
      Unch.refl _ _, Keep.refl _ _, Keep.refl _ _, fun _ h => h,
      fun x hx => temps_gso _ _ fun e => hx (.inl e)⟩
  · rintro q le' m' hq ⟨-, hi, hn', W3', W4', hw3', hw4', hz3, hc4, hz4, hu, hk2, hk3, hg, ho⟩
    have hf := (h.unch (hm23 hu hk2 hk3).1).temps (le' := le') fun x hx => ho x (args_not_j x hx)
    have hw1' := hw1.unch hu (hn23 _ (.inl rfl))
    have hw2' := hw2.unch hu (hn23 _ (.inr rfl))
    have hst := hgood.startLt q hq
    obtain ⟨st, hst'⟩ : ∃ st, st = c.starts[q]! := ⟨_, rfl⟩
    rw [← hst'] at hst
    have hu' := h.lsmall st hst
    obtain ⟨u, hu''⟩ : ∃ u, u = lab[st]! := ⟨_, rfl⟩
    rw [← hu''] at hu'
    have eF : ∀ le'', PTree.get id.i le'' = some (.Vint (ir q)) →
        PTree.get id.lab le'' = some (.Vptr bl lofs) →
        Exec.evalExpr sge empty_env le'' m' firstV = some (.Vint (ir (u : Int))) := fun le'' h1 h2 => by
      have e1 := eval_idx (pe := .Evar id.work1 (tptr tint)) (ofs := Ptrofs.zero) (e := empty_env)
        (le := le'') hw1' (by omega) (eval_gvar (k := 0) find_work1 (hf.wptr 0)) rfl rfl rfl (tv id.i) q
        (by omega) h1 rfl
      rw [(hW1 q hq).1, ← hst'] at e1
      have e2 := eval_tidx (e := empty_env) (ty := tint) hf.larr (by omega) h2 rfl rfl _ st hst e1 rfl
      rw [hu''] ; exact e2
    have hlast := offsets_last G (show u + 1 ≤ n by omega)
    have hmono := offsets_le G (show u ≤ u + 1 by omega) (show u + 1 ≤ n by omega)
    have hDn := degree_lt G hu'
    -- `vi = v[lab[START[i]]]; di = d[lab[START[i]]];`
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_tidx (e := empty_env) (ty := tulong) hf.varr (by omega) hf.hv rfl rfl _ u hu' (eF le' hi hf.hlab) rfl]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_tidx (e := empty_env) (ty := tint) hf.darr (by omega)
      (by rw [temps_gso _ _ (by decide)]; exact hf.hd) rfl rfl _ u hu'
      (eF _ (by rw [temps_gso _ _ (by decide)]; exact hi) (by rw [temps_gso _ _ (by decide)]; exact hf.hlab))
      rfl]
    let le2 := PTree.set id.di (dVals G u) (PTree.set id.vi (vVals G u) le')
    have ho2 : ∀ x, ¬ JLocal x → PTree.get x le2 = PTree.get x le := fun x hx => by
      simp only [le2]
      rw [temps_gso _ _ (fun e => hx (.inr (.inr (.inl e)))), temps_gso _ _ (fun e => hx (.inr (.inl e))),
        ho x hx]
    have hf2 := hf.temps (le' := le2) fun x hx => by
      simp only [le2]
      rw [temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        temps_gso _ _ (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    have hvi2 : PTree.get id.vi le2 = some (.Vlong (lr ((g.offsets[u]! : Nat) : Int))) := by
      simp only [le2]; rw [temps_gso _ _ (by decide), temps_gss]; rfl
    have hdi2 : PTree.get id.di le2 = some (.Vint (ir ((g.degree u : Nat) : Int))) := by
      simp only [le2]; rw [temps_gss]; rfl
    have hi2 : PTree.get id.i le2 = some (.Vint (ir q)) := by
      simp only [le2]; rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hi
    have hn2 : PTree.get id.nnt le2 = some (.Vint (ir K)) := by
      simp only [le2]; rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hn'
    have hVD : g.offsets[u]! + g.degree u ≤ G.neighbors.size := by
      show (Graph.ofGraph G).offsets[u]! + ((Graph.ofGraph G).offsets[u + 1]! -
        (Graph.ofGraph G).offsets[u]!) ≤ G.neighbors.size
      omega
    have hDn' : g.degree u ≤ n := hDn
    obtain ⟨hPs, hPz⟩ := hP q
    wp_step
    refine wp_hits (H := P q) hf2 hgood hw2' hW2 hvi2 hdi2 hVD hDn hPs (fun k => by rw [hPz k]; omega)
      hw3' (fun k hk => by rw [hz3 k hk, hPz k]; rfl) ?_
    intro le3 m3 W3a hw3a hW3a hu3 hk3' hg3 ho3
    have hf3 := (hf2.unch (m' := m3) (hu3.mono fun _ hz => ⟨2, hz⟩)).temps (le' := le3) fun x hx =>
      ho3 x (args_not_row x hx)
    have gr : ∀ x, ¬ RowLocal x → PTree.get x le3 = PTree.get x le2 := ho3
    obtain ⟨hHs, hHb, -⟩ := hit_fold g c.nntcell (List.range' g.offsets[u]! (g.degree u)) (P q)
    simp only [List.length_range'] at hHb
    refine wp_counts (I := q) hf3 hgood (hw1'.unch hu3 (h.wdist 0 2 (by decide))) (fun k hk => (hW1 k hk).2)
      (hw2'.unch hu3 (h.wdist 1 2 (by decide))) hW2
      (by rw [gr _ (by decide)]; exact hvi2) (by rw [gr _ (by decide)]; exact hdi2) hVD hDn
      (by rw [gr _ (by decide)]; exact hi2) hq (by rw [hHs, hPs]) (fun k => by
        have h1 := hHb k; rw [hPz k] at h1
        exact (Nat.le_trans h1 (by omega) : _ ≤ 2 * n))
      hw3a hW3a (hw4'.unch hu3 (h.wdist 3 2 (by decide))) (hz4 q (Nat.le_refl _) hq) ?_
    intro le4 m4 W3b W4b hw3b hw4b hW3b hW4b hW4o hu4 hk43 hk44 hg4 ho4
    have hJ := joins_zero g c.nntcell c.sizes (h := P q) hPz u
    have eJ : joins g c.nntcell c.sizes (P q) u = (List.range' g.offsets[u]! (g.degree u)).foldl
        (countStep g c.nntcell c.sizes)
        ((List.range' g.offsets[u]! (g.degree u)).foldl (hitStep g c.nntcell) (P q), 0) := rfl
    have eC : countAt g lab c q = (joins g c.nntcell c.sizes (P q) u).2 := by
      rw [hu'', hst']; rfl
    rw [eJ] at hJ
    refine ⟨by simp, by rw [ho4 _ (by decide), gr _ (by decide)]; exact hi2, hq,
      by rw [ho4 _ (by decide), gr _ (by decide)]; exact hn2, W3b, W4b, hw3b, hw4b,
      fun k hk => by rw [hW3b k hk, hJ.2.1 k]; rfl, fun k hk => ?_, fun k hk1 hk2 => ?_,
      (hu.trans (hu3.mono fun _ hz => .inl hz)).trans hu4, (hk2.trans hk3').trans hk43,
      (hk3.trans (Keep.unch hu3 (h.wdist 3 2 (by decide)))).trans hk44,
      fun z hz => hg4 _ (hg3 _ (hg _ hz)), fun x hx => ?_⟩
    · by_cases hkq : k = q
      · subst hkq; rw [hW4b, eC, eJ]
      · rw [hW4o k hkq]; exact hc4 k (by omega)
    · rw [hW4o k (by omega)]; exact hz4 k (by omega) hk2
    · rw [ho4 x (fun e => hx (.inr (.inr (.inr e)))), gr x (fun e => hx (.inr (.inr (.inr e)))), ho2 x hx]
  · rintro q le' m' ⟨hi, hq, hn', W3', W4', hw3', hw4', hz3, hc4, hz4, hu, hk2, hk3, hg, ho⟩
    exact ⟨hi, by omega, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hn', W3', W4', hw3',
      hw4', hz3, hc4, hz4, hu, hk2, hk3, hg, fun x hx => by rw [temps_gso _ _ (fun e => hx (.inl e)), ho x hx]⟩
  · rintro le' m' ⟨-, -, -, W3', W4', hw3', hw4', hz3, hc4, hz4, hu, hk2, hk3, hg, ho⟩
    exact hQ le' m' W4' hw4' hc4 hu hk2 hk3 hg ho

end

end NautyVerified.Proofs.Sparse.Bestcell

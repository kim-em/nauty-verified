import NautyVerified.Proofs.Sparse.Distvals.Syntax
import NautyVerified.Proofs.Sparse.Distvals.Model
import NautyVerified.Proofs.Sparse.Isautom.Loops
import NautyVerified.Logic.For

/-!
# The loops of `distvals`

`wp_fill`: `for (i = 0; i < n; ++i) dist[i] = n;`. `wp_edges`: the scan of
the row of the dequeued vertex `i` (`vi = v[i]`, `di = d[i]`) leaves `dist`,
the queue below `tail` and `tail` as `Distvals.scan` computes them, with
`next = dist[i] + 1` (the C reads `dist[i]` at each new vertex; it does not
change during the scan since `i` is already seen).
-/

namespace NautyVerified.Proofs.Sparse.Distvals

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat cast_l_i)
open Hex.GraphIso.Nauty.Sparse (Graph)

variable {xi : ExternalCalls}

abbrev F := sparse.fn.distvals

theorem eval_work4 {le : temp_env} {m : mem} {bQ : block}
    (h : Mem.load .Mint64 m Block.work4 (zOfInt 0) = some (.Vptr bQ Ptrofs.zero)) :
    Exec.evalExpr sge empty_env le m (.Evar id.work4 (tptr tint)) = some (.Vptr bQ Ptrofs.zero) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get id.work4 (empty_env : env) = none from rfl,
    find_work4, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq]
  exact h

/-- `dist` after `fill` has run up to `k`. -/
def filled (n : Nat) (dv : Nat → val) (k x : Nat) : val := if x < k then .Vint (ir n) else dv x

/-- The fill loop. -/
theorem wp_fill {Q : Post} {le : temp_env} {m : mem} {bD : block} {Dofs : ptrofs}
    {dv : Nat → val} {n : Nat}
    (hd : PTree.get id.dist le = some (.Vptr bD Dofs)) (hnv : PTree.get id.n le = some (.Vint (ir n)))
    (hn : n < 2147483648) (harr : ArrayAt m .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) dv n)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) (fun _ => .Vint (ir n)) n →
      Unch m m' (· = bD) → Alloc.Keep m m' bD → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F fill Q empty_env le m := by
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) => k ≤ n ∧
    PTree.get id.i le' = some (.Vint (ir k)) ∧ PTree.get id.n le' = some (.Vint (ir n)) ∧
    ArrayAt m' .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) (filled n dv k) n ∧ Unch m m' (· = bD) ∧
    Alloc.Keep m m' bD ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    PTree.get id.i le' = some (.Vint (ir k)) ∧ k < n ∧ PTree.get id.n le' = some (.Vint (ir n)) ∧
    ArrayAt m' .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) (filled n dv (k + 1)) n ∧ Unch m m' (· = bD) ∧
    Alloc.Keep m m' bD ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le
  refine wp_forLoop id.i id.n _ n hn Inv Mid ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, hn', -⟩
    exact ⟨hk, hi, hn'⟩
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, by rw [temps_gso _ _ (by decide)]; exact hnv,
      harr.congr fun p _ => by simp [filled], Unch.refl _ _, Alloc.Keep.refl _ _, fun _ h => h,
      fun x hx => temps_gso _ _ hx⟩
  · rintro k le' m' hk ⟨-, hi, hn', harr', hu, hkp, hg, ho⟩
    have hd' : PTree.get id.dist le' = some (.Vptr bD Dofs) := by rw [ho _ (by decide)]; exact hd
    wp_step; wp_step
    refine wp_idx_store (chunk := .Mint32) (pe := .Etempvar id.dist (tptr tint)) harr' hn
      (by simp only [Exec.evalExpr]; exact hd')
      rfl rfl rfl (tv id.i) k hk hi rfl (tv id.n) tint rfl (.Vint (ir n)) (.Vint (ir n)) hn' rfl rfl ?_
    intro m'' harr'' hu' hk' hg'
    refine ⟨by simp, hi, hk, hn', harr''.congr fun p _ => ?_, hu.trans hu', hkp.trans hk',
      fun z h => hg' _ (hg _ h), ho⟩
    simp only [upd, filled]
    by_cases hp : p = k
    · simp [hp]
    · rw [ite_eq_right hp]
      by_cases hpk : p < k
      · rw [ite_eq_left hpk, ite_eq_left (by omega)]
      · rw [ite_eq_right hpk, ite_eq_right (by omega)]
  · rintro k le' m' ⟨hi, hk, hn', harr', hu, hkp, hg, ho⟩
    exact ⟨hi, by omega, temps_gss _ _ _,
      by rw [temps_gso _ _ (by decide)]; exact hn', harr', hu, hkp, hg,
      fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩
  · rintro le' m' ⟨-, -, -, harr', hu, hkp, hg, ho⟩
    exact hQ le' m' (harr'.congr fun p hp => by simp [filled, hp]) hu hkp hg ho

/-- The queue `q` below `t` in the values `qv`. -/
abbrev QueueIs (qv : Nat → val) (q : Array Nat) (t : Nat) : Prop :=
  ∀ p < t, qv p = .Vint (ir (q[p]! : Int))

/-- The temporaries the edge loop changes. -/
def EdgeLocal (x : ident) : Prop := x = id.j ∨ x = id.k ∨ x = id.tail ∨ x = id.t3

instance (x : ident) : Decidable (EdgeLocal x) := by unfold EdgeLocal; infer_instance

/-- What the edge loop reads. -/
structure ECtx {n : Nat} (m : mem) (le : temp_env) (G : Hex.SparseGraph n) (be : block)
    (eo : ptrofs) (bD : block) (Dofs : ptrofs) (bQ : block) (I D VI : Nat) : Prop where
  he : PTree.get id.e le = some (.Vptr be eo)
  hdist : PTree.get id.dist le = some (.Vptr bD Dofs)
  hn : PTree.get id.n le = some (.Vint (ir n))
  hi : PTree.get id.i le = some (.Vint (ir I))
  hdi : PTree.get id.di le = some (.Vint (ir D))
  hvi : PTree.get id.vi le = some (.Vlong (lr VI))
  earr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size
  wptr : Mem.load .Mint64 m Block.work4 (zOfInt 0) = some (.Vptr bQ Ptrofs.zero)
  hVD : VI + D ≤ G.neighbors.size
  hI : I < n
  Dn : D ≤ n
  n31 : n < 2147483648
  bDe : bD ≠ be
  bQe : bQ ≠ be
  bDQ : bD ≠ bQ
  bDW : bD ≠ Block.work4
  bQW : bQ ≠ Block.work4

theorem ECtx.temps {n : Nat} {m : mem} {le le' : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {bD : block} {Dofs : ptrofs} {bQ : block} {I D VI : Nat}
    (h : ECtx m le G be eo bD Dofs bQ I D VI) (hle : ∀ x, ¬ EdgeLocal x → PTree.get x le' = PTree.get x le) :
    ECtx m le' G be eo bD Dofs bQ I D VI :=
  { h with
    he := by rw [hle _ (by decide)]; exact h.he
    hdist := by rw [hle _ (by decide)]; exact h.hdist
    hn := by rw [hle _ (by decide)]; exact h.hn
    hi := by rw [hle _ (by decide)]; exact h.hi
    hdi := by rw [hle _ (by decide)]; exact h.hdi
    hvi := by rw [hle _ (by decide)]; exact h.hvi }

theorem ECtx.mem {n : Nat} {m m' : mem} {le : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {bD : block} {Dofs : ptrofs} {bQ : block} {I D VI : Nat}
    (h : ECtx m le G be eo bD Dofs bQ I D VI) (hu : Unch m m' (fun z => z = bD ∨ z = bQ)) :
    ECtx m' le G be eo bD Dofs bQ I D VI :=
  { h with
    earr := h.earr.unch hu fun h' => h'.elim (fun e => h.bDe e.symm) (fun e => h.bQe e.symm)
    wptr := by
      rw [hu.load _ _ _ fun h' => h'.elim (fun e => h.bDW e.symm) (fun e => h.bQW e.symm)]
      exact h.wptr }

/-- `e[vi + j]`. -/
theorem eval_e {n : Nat} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {bD : block} {Dofs : ptrofs} {bQ : block} {I D VI : Nat}
    (h : ECtx m le G be eo bD Dofs bQ I D VI) {k : Nat}
    (hj : PTree.get id.j le = some (.Vlong (lr k))) (hk : k < D) :
    Exec.evalExpr sge empty_env le m (iat id.e (.Ebinop .Oadd (tl id.vi) (tl id.j) tulong)) =
      some (.Vint (ir ((Graph.ofGraph G).neighbor (VI + k)))) := by
  have hnd := Isautom.nde_lt h.earr
  have := h.hVD
  refine eval_idx_l h.earr (by omega) (by simp only [Exec.evalExpr]; exact h.he) rfl rfl rfl _ _
    (by omega) ?_ rfl
  simp only [Exec.evalExpr, h.hvi, hj, typeof, cop, lr_add]

/-- The edge loop: from distances `d`, queue `q` and tail `t` (all `Good`,
`i` seen, `next = d[i] + 1` below `n` and at most `t`), the scan of the
`D` edges from `VI`. -/
theorem wp_edges {n : Nat} {Q : Post} {le : temp_env} {m : mem} {G : Hex.SparseGraph n} {be : block}
    {eo : ptrofs} {bD : block} {Dofs : ptrofs} {bQ : block} {I D VI : Nat} {d q : Array Nat} {t : Nat}
    {qv : Nat → val}
    (hc : ECtx m le G be eo bD Dofs bQ I D VI) (hgood : Good n d q t)
    (hdI : d[I]! ≠ n) (hnext : d[I]! + 1 < n) (hnt : d[I]! + 1 ≤ t)
    (htail : PTree.get id.tail le = some (.Vint (ir t)))
    (hdarr : ArrayAt m .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) (ints d) n)
    (hqarr : ArrayAt m .Mint32 bQ 0 qv n) (hq : QueueIs qv q t)
    (hQ : ∀ le' m' qv',
      ArrayAt m' .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs))
        (ints (scan (Graph.ofGraph G) (d[I]! + 1) (d, q, t) (List.range' VI D)).1) n →
      ArrayAt m' .Mint32 bQ 0 qv' n →
      QueueIs qv' (scan (Graph.ofGraph G) (d[I]! + 1) (d, q, t) (List.range' VI D)).2.1
        (scan (Graph.ofGraph G) (d[I]! + 1) (d, q, t) (List.range' VI D)).2.2 →
      PTree.get id.tail le' =
        some (.Vint (ir (scan (Graph.ofGraph G) (d[I]! + 1) (d, q, t) (List.range' VI D)).2.2)) →
      Unch m m' (fun z => z = bD ∨ z = bQ) → Alloc.Keep m m' bD → Alloc.Keep m m' bQ →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, ¬ EdgeLocal x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F edges Q empty_env le m := by
  let g := Graph.ofGraph G
  let next := d[I]! + 1
  have hn31 := hc.n31
  have hVD := hc.hVD
  have hnd := Isautom.nde_lt hc.earr
  have hD31 : D < 2147483648 := by have := hc.Dn; omega
  have hdsz := hgood.dsize
  have hrow : ∀ k ≤ D, ∀ j ∈ List.range' VI k, g.neighbor j < n := fun k hk j hj => by
    rw [List.mem_range'_1] at hj
    exact neighbor_lt G (by omega)
  let S := fun k => scan g next (d, q, t) (List.range' VI k)
  have hS : ∀ k ≤ D, Good n (S k).1 (S k).2.1 (S k).2.2 ∧ t ≤ (S k).2.2 := fun k hk =>
    Good.scan _ (hrow k hk) hgood hnext hnt
  have hSI : ∀ k, (S k).1[I]! = d[I]! := fun k =>
    (scan_keep (g := g) (next := next) (q := q) (t := t) _ (by rw [hdsz]; exact hc.hI) hdI).1
  have hSsucc : ∀ k, S (k + 1) = edge g next (S k) (VI + k) := fun k => by
    simp only [S, scan, List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
  let At := fun (k c : Nat) (le' : temp_env) (m' : mem) => ∃ qv',
    PTree.get id.j le' = some (.Vlong (lr c)) ∧
    PTree.get id.tail le' = some (.Vint (ir (S k).2.2)) ∧
    ArrayAt m' .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) (ints (S k).1) n ∧
    ArrayAt m' .Mint32 bQ 0 qv' n ∧ QueueIs qv' (S k).2.1 (S k).2.2 ∧
    Unch m m' (fun z => z = bD ∨ z = bQ) ∧ Alloc.Keep m m' bD ∧ Alloc.Keep m m' bQ ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, ¬ EdgeLocal x → PTree.get x le' = PTree.get x le
  let I' := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ k, k ≤ D ∧ v = D - k ∧ At k k le' m'
  let J' := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ k, k < D ∧ v = D - k ∧ At (k + 1) k le' m'
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
  refine wp_loop (I := I') (J := J') ?_ ?_ (n := D - 0)
    ⟨rfl, rfl, 0, Nat.zero_le _, rfl, qv, temps_gss _ _ _,
      by rw [temps_gso _ _ (by decide)]; exact htail, hdarr, hqarr, hq, Unch.refl _ _,
      Alloc.Keep.refl _ _, Alloc.Keep.refl _ _, fun _ h => h,
      fun x hx => temps_gso _ _ (fun h => hx (.inl h))⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, k, hk, rfl, qv', hj, ht, hda, hqa, hqi, hu, hkD, hkQ, hg, ho⟩
    have hc' := (hc.temps ho).mem hu
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj,
      show Exec.evalExpr sge empty_env le' m' (tv id.di) = _ from hc'.hdi]
    simp only [typeof, cop, cast_l_i D hD31, Alloc.ltu_lr (a := k) (b := D) (by omega) (by omega)]
    by_cases hkD' : k < D
    · rw [ite_eq_left (by simpa using hkD')]
      apply wp_skip
      have hkn : VI + k < G.neighbors.size := by omega
      have hnb : g.neighbor (VI + k) < n := neighbor_lt G hkn
      obtain ⟨hGk, htk⟩ := hS k (by omega)
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_e hc' hj hkD']
      have hdk := hGk.dle hnb
      have hkv : PTree.get id.k (PTree.set id.k (.Vint (ir (g.neighbor (VI + k)))) le') =
          some (.Vint (ir (g.neighbor (VI + k)))) := temps_gss _ _ _
      have hc'' := hc'.temps (le' := PTree.set id.k (.Vint (ir (g.neighbor (VI + k)))) le')
        fun x hx => temps_gso _ _ fun h => hx (.inr (.inl h))
      have hdat := eval_idx (ge := sge) (pe := .Etempvar id.dist (tptr tint)) (e := empty_env)
        (le := PTree.set id.k (.Vint (ir (g.neighbor (VI + k)))) le') hda hn31
        (by simp only [Exec.evalExpr]; exact hc''.hdist) rfl rfl rfl (tv id.k) _ hnb hkv rfl
      wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hdat, show Exec.evalExpr sge empty_env _ m' (tv id.n) = _ from hc''.hn]
      simp only [ints, typeof, cop]
      rw [ir_eq (a := ((S k).1[g.neighbor (VI + k)]! : Int)) (b := (n : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
      have hkv' := hc''.hn
      by_cases hdn : (S k).1[g.neighbor (VI + k)]! = n
      · rw [ite_eq_left (by simp [hdn])]
        have hSk1 : S (k + 1) = ((S k).1.set! (g.neighbor (VI + k)) next,
            (S k).2.1.set! (S k).2.2 (g.neighbor (VI + k)), (S k).2.2 + 1) := by
          rw [hSsucc]; unfold edge; simp [hdn]
        have htn : (S k).2.2 < n := hGk.tlt hnb hdn
        have hdatI := eval_idx (ge := sge) (pe := .Etempvar id.dist (tptr tint)) (e := empty_env)
          (le := PTree.set id.k (.Vint (ir (g.neighbor (VI + k)))) le') hda hn31
          (by simp only [Exec.evalExpr]; exact hc''.hdist) rfl rfl rfl (tv id.i) _ hc''.hI hc''.hi rfl
        wp_step; wp_step; wp_step
        refine wp_idx_store (pe := .Etempvar id.dist (tptr tint)) hda hn31
          (by simp only [Exec.evalExpr]; exact hc''.hdist) rfl rfl rfl (tv id.k) _ hnb hkv rfl
          (.Ebinop .Oadd (dat (tv id.i)) (ci 1 tint) tint) tint rfl (.Vint (ir (next : Nat)))
          (.Vint (ir (next : Nat))) (by
            rw [Exec.evalExpr, hdatI]
            simp only [ints, hSI, Exec.evalExpr, typeof, cop, ir_add, next]
            push_cast; rfl) rfl rfl ?_
        intro m1 hda1 hu1 hk1 hg1
        dsimp only
        wp_step; wp_step; wp_step; wp_step
        have ht1 : PTree.get id.tail (PTree.set id.k (.Vint (ir (g.neighbor (VI + k)))) le') =
            some (.Vint (ir (S k).2.2)) := by rw [temps_gso _ _ (by decide)]; exact ht
        apply wp_set_eval
        simp only [Exec.evalExpr, ht1, E0_append]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add, E0_append]
        have hqa1 : ArrayAt m1 .Mint32 bQ 0 qv' n := hqa.unch hu1 (fun h => hc.bDQ h.symm)
        have hw1 : Mem.load .Mint64 m1 Block.work4 (zOfInt 0) = some (.Vptr bQ Ptrofs.zero) := by
          rw [hu1.load _ _ _ (fun h => hc.bDW h.symm)]; exact hc'.wptr
        refine wp_idx_store (pe := .Evar id.work4 (tptr tint)) (ofs := Ptrofs.zero) hqa1 hn31
          (eval_work4 hw1) rfl rfl rfl (tv id.t3) (S k).2.2 htn
          (by simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide), temps_gss]) rfl
          (tv id.k) tint rfl _ _ (by simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide),
            temps_gso _ _ (by decide), hkv]) rfl rfl ?_
        intro m2 hqa2 hu2 hk2 hg2
        have hdsk := hGk.dsize
        have hqsk := hGk.qsize
        refine ⟨by simp, rfl, k, hkD', rfl, upd qv' (S k).2.2 (.Vint (ir (g.neighbor (VI + k)))),
          by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hj,
          by rw [hSk1, temps_gss]; push_cast; rfl,
          ?_, hqa2, ?_, (hu.trans (hu1.mono fun z hz => .inl hz)).trans (hu2.mono fun z hz => .inr hz),
          (hkD.trans hk1).trans (Alloc.Keep.unch hu2 hc.bDQ),
          (hkQ.trans (Alloc.Keep.unch hu1 (fun h => hc.bDQ h.symm))).trans hk2,
          fun z h => hg2 _ (hg1 _ (hg _ h)), fun x hx => ?_⟩
        · refine (hda1.unch hu2 hc.bDQ).congr fun p hp => ?_
          rw [hSk1]
          simp only [ints, upd]
          rw [get_set (a := (S k).1) (by rw [hdsk]; exact hp)]
          by_cases hp' : p = g.neighbor (VI + k)
          · simp [hp']
          · rw [ite_eq_right hp', ite_eq_right (Ne.symm hp')]
        · intro p hp
          rw [hSk1] at hp ⊢
          dsimp only at hp ⊢
          simp only [upd]
          rw [get_set (a := (S k).2.1) (by rw [hqsk]; omega)]
          by_cases hp' : p = (S k).2.2
          · simp [hp']
          · rw [ite_eq_right hp', ite_eq_right (Ne.symm hp')]
            exact hqi p (by omega)
        · rw [temps_gso _ _ (fun h => hx (.inr (.inr (.inl h)))),
            temps_gso _ _ (fun h => hx (.inr (.inr (.inr h)))),
            temps_gso _ _ (fun h => hx (.inr (.inl h))), ho x hx]
      · rw [ite_eq_right (by simp only [decide_eq_true_eq]; omega)]
        have hSk1 : S (k + 1) = S k := by
          rw [hSsucc]; unfold edge
          have : ((S k).1[g.neighbor (VI + k)]! == n) = false := by simpa using hdn
          simp only [this, Bool.false_eq_true, ite_false]
        apply wp_skip
        refine ⟨by simp, rfl, k, hkD', rfl, qv', by rw [temps_gso _ _ (by decide)]; exact hj,
          by rw [hSk1, temps_gso _ _ (by decide)]; exact ht, by rw [hSk1]; exact hda, hqa,
          by rw [hSk1]; exact hqi, hu, hkD, hkQ, hg, fun x hx => ?_⟩
        rw [temps_gso _ _ (fun h => hx (.inr (.inl h))), ho x hx]
    · rw [ite_eq_right (by simpa using hkD')]
      apply wp_break
      have : k = D := by omega
      subst this
      exact hQ le' m' qv' hda hqa hqi ht hu hkD hkQ hg ho
  · rintro v tr e' le' m' ⟨rfl, rfl, k, hk, rfl, qv', hj, ht, hda, hqa, hqi, hu, hkD, hkQ, hg, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tl id.j) = _ from hj]
    simp only [Exec.evalExpr, typeof, cop, Alloc.add_lr_one]
    exact ⟨D - (k + 1), by omega, by simp, rfl, k + 1, by omega, rfl, qv', temps_gss _ _ _,
      by rw [temps_gso _ _ (by decide)]; exact ht, hda, hqa, hqi, hu, hkD, hkQ, hg,
      fun x hx => by rw [temps_gso _ _ (fun h => hx (.inl h)), ho x hx]⟩

end NautyVerified.Proofs.Sparse.Distvals

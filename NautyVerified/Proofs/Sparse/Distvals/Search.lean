import NautyVerified.Proofs.Sparse.Distvals.Loops

/-!
# The breadth-first search of `distvals`

`wp_search`: from `dist` filled with `n`, `QUEUE[0] = v0; dist[v0] = 0;
head = 0; tail = 1;` and the `while (tail < n && head < tail)` loop leave
`dist` holding HexGraphIso's `Sparse.distvals (ofGraph G) v0`. The loop runs
`Distvals.outer` once per iteration; its variant is `n - head`.
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
open Hex.GraphIso.Nauty.Sparse (Graph distvals)

variable {xi : ExternalCalls}

theorem cast_b (b : Bool) (m : mem) {a a' : Cfrontend.Ctypes.attr} :
    Cfrontend.Cop.sem_cast (Val.of_bool b) (.Tint .I32 .Signed a) (.Tint .IBool .Signed a') m =
      some (Val.of_bool b) := by
  cases b <;> rfl

/-- The temporaries the search changes. -/
def SearchLocal (x : ident) : Prop :=
  x = id.i ∨ x = id.head ∨ x = id.tail ∨ x = id.vi ∨ x = id.di ∨ x = id.j ∨ x = id.k ∨
    x = id.t1 ∨ x = id.t2 ∨ x = id.t3

instance (x : ident) : Decidable (SearchLocal x) := by unfold SearchLocal; infer_instance

/-- What the search reads. -/
structure SCtx {n : Nat} (m : mem) (le : temp_env) (G : Hex.SparseGraph n) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (bD : block)
    (Dofs : ptrofs) (bQ : block) : Prop where
  hv : PTree.get id.v le = some (.Vptr bv vo)
  hd : PTree.get id.d le = some (.Vptr bd dofs)
  he : PTree.get id.e le = some (.Vptr be eo)
  hdist : PTree.get id.dist le = some (.Vptr bD Dofs)
  hn : PTree.get id.n le = some (.Vint (ir n))
  varr : ArrayAt m .Mint64 bv (intOfZ (Ptrofs.unsigned vo)) (vVals G) n
  darr : ArrayAt m .Mint32 bd (intOfZ (Ptrofs.unsigned dofs)) (dVals G) n
  earr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size
  wptr : Mem.load .Mint64 m Block.work4 (zOfInt 0) = some (.Vptr bQ Ptrofs.zero)
  n31 : n < 2147483648
  /-- `bD` and `bQ` are apart from each other, the graph's arrays and `work4`. -/
  sep : ∀ z, z = bv ∨ z = bd ∨ z = be ∨ z = Block.work4 → z ≠ bD ∧ z ≠ bQ
  bDQ : bD ≠ bQ

theorem SCtx.temps {n : Nat} {m : mem} {le le' : temp_env} {G : Hex.SparseGraph n} {bv : block}
    {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {bD : block}
    {Dofs : ptrofs} {bQ : block} (h : SCtx m le G bv vo bd dofs be eo bD Dofs bQ)
    (hle : ∀ x, ¬ SearchLocal x → PTree.get x le' = PTree.get x le) :
    SCtx m le' G bv vo bd dofs be eo bD Dofs bQ :=
  { h with
    hv := by rw [hle _ (by decide)]; exact h.hv
    hd := by rw [hle _ (by decide)]; exact h.hd
    he := by rw [hle _ (by decide)]; exact h.he
    hdist := by rw [hle _ (by decide)]; exact h.hdist
    hn := by rw [hle _ (by decide)]; exact h.hn }

theorem SCtx.mem {n : Nat} {m m' : mem} {le : temp_env} {G : Hex.SparseGraph n} {bv : block}
    {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {bD : block}
    {Dofs : ptrofs} {bQ : block} (h : SCtx m le G bv vo bd dofs be eo bD Dofs bQ)
    (hu : Unch m m' (fun z => z = bD ∨ z = bQ)) : SCtx m' le G bv vo bd dofs be eo bD Dofs bQ :=
  have hs : ∀ z, z = bv ∨ z = bd ∨ z = be ∨ z = Block.work4 → ¬ (z = bD ∨ z = bQ) := fun z hz h' =>
    h'.elim (h.sep z hz).1 (h.sep z hz).2
  { h with
    varr := h.varr.unch hu (hs _ (.inl rfl))
    darr := h.darr.unch hu (hs _ (.inr (.inl rfl)))
    earr := h.earr.unch hu (hs _ (.inr (.inr (.inl rfl))))
    wptr := by rw [hu.load _ _ _ (hs _ (.inr (.inr (.inr rfl))))]; exact h.wptr }

theorem rows_ofGraph {n : Nat} (G : Hex.SparseGraph n) : Rows n (Graph.ofGraph G) := by
  intro i hi j hj
  rw [List.mem_range'_1] at hj
  have := offsets_last G (show i + 1 ≤ n by omega)
  exact neighbor_lt G (by omega)

/-- The state of the search at the loop head (or after an iteration). -/
def At {n : Nat} (m m' : mem) (le le' : temp_env) (G : Hex.SparseGraph n) (bD : block)
    (Dofs : ptrofs) (bQ : block) (v0 : Nat) (s : St) (qv : Nat → val) : Prop :=
  Good n s.dist s.queue s.tail ∧ s.head ≤ s.tail ∧
    run (Graph.ofGraph G) (n - s.head) s = run (Graph.ofGraph G) n (start n v0) ∧
    PTree.get id.head le' = some (.Vint (ir s.head)) ∧ PTree.get id.tail le' = some (.Vint (ir s.tail)) ∧
    ArrayAt m' .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) (ints s.dist) n ∧
    ArrayAt m' .Mint32 bQ 0 qv n ∧ QueueIs qv s.queue s.tail ∧
    Unch m m' (fun z => z = bD ∨ z = bQ) ∧ DOut m m' bD Dofs n ∧ Alloc.Keep m m' bD ∧ Alloc.Keep m m' bQ ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, ¬ SearchLocal x → PTree.get x le' = PTree.get x le

/-- One iteration of the search, after the test succeeded. -/
theorem wp_body {n : Nat} {Q : Post} {le le' le1 : temp_env} {m m' : mem} {G : Hex.SparseGraph n}
    {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {bD : block}
    {Dofs : ptrofs} {bQ : block} {v0 : Nat} {s : St} {qv : Nat → val}
    (hA : At m m' le le' G bD Dofs bQ v0 s qv) (htn : s.tail < n) (hht : s.head < s.tail)
    (hc : SCtx m' le' G bv vo bd dofs be eo bD Dofs bQ)
    (h1 : ∀ x, x ≠ id.t1 → PTree.get x le1 = PTree.get x le')
    (hQ : ∀ le'' m'' s' qv', n - s'.head < n - s.head → At m m'' le le'' G bD Dofs bQ v0 s' qv' →
      Q.normal E0 empty_env le'' m'') :
    Wp xi sge F step Q empty_env le1 m' := by
  obtain ⟨hgood, hht', hrun, hhd, htl, hda, hqa, hqi, hu, hout, hkD, hkQ, hg, ho⟩ := hA
  have hn31 := hc.n31
  have hTn := hgood.tle
  have hH : s.head < n := by omega
  have hI := hgood.qlt s.head hht
  have hdep := hgood.depth s.head hht
  have hdI : s.dist[s.queue[s.head]!]! ≠ n := (hgood.seen _ hI).2 ⟨s.head, hht, rfl⟩
  have hns : ¬ Stop n s := by simp only [Stop]; omega
  have hhd1 : PTree.get id.head le1 = some (.Vint (ir s.head)) := by rw [h1 _ (by decide)]; exact hhd
  wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hhd1]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add, E0_append]
  apply wp_set_eval
  let le2 := PTree.set id.head (.Vint (ir ((s.head : Int) + 1))) (PTree.set id.t2 (.Vint (ir s.head)) le1)
  have hget2 : ∀ x, x ≠ id.head → x ≠ id.t2 → x ≠ id.t1 → PTree.get x le2 = PTree.get x le' :=
    fun x a b c => by simp only [le2]; rw [temps_gso _ _ a, temps_gso _ _ b, h1 _ c]
  rw [eval_idx (ge := sge) (pe := .Evar id.work4 (tptr tint)) (ofs := Ptrofs.zero) hqa hn31
    (eval_work4 (le := le2) hc.wptr) rfl rfl rfl (tv id.t2) s.head hH
    (by simp only [Exec.evalExpr, le2]; rw [temps_gso _ _ (by decide), temps_gss]) rfl,
    hqi s.head hht]
  dsimp only
  let I0 := s.queue[s.head]!
  let le3 := PTree.set id.i (.Vint (ir (I0 : Int))) le2
  have hi3 : PTree.get id.i le3 = some (.Vint (ir (I0 : Int))) := temps_gss _ _ _
  have hget3 : ∀ x, ¬ SearchLocal x → PTree.get x le3 = PTree.get x le' := fun x hx => by
    simp only [le3]
    rw [temps_gso _ _ (by rintro rfl; exact hx (by decide)),
      hget2 x (by rintro rfl; exact hx (by decide)) (by rintro rfl; exact hx (by decide))
        (by rintro rfl; exact hx (by decide))]
  have hc3 := hc.temps hget3
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_idx (ge := sge) (pe := .Etempvar id.v (tptr tulong)) hc3.varr hn31
    (by simp only [Exec.evalExpr]; exact hc3.hv) rfl rfl rfl (tv id.i) I0 hI hi3 rfl]
  dsimp only
  wp_step; wp_step; wp_step
  apply wp_set_eval
  let le4 := PTree.set id.vi (vVals G I0) le3
  rw [eval_idx (ge := sge) (pe := .Etempvar id.d (tptr tint)) hc3.darr hn31
    (by simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide)]; exact hc3.hd) rfl rfl rfl (tv id.i) I0
    hI (by simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide)]; exact hi3) rfl]
  let le5 := PTree.set id.di (dVals G I0) le4
  have hget5 : ∀ x, ¬ SearchLocal x → PTree.get x le5 = PTree.get x le' := fun x hx => by
    simp only [le5, le4]
    rw [temps_gso _ _ (by rintro rfl; exact hx (by decide)),
      temps_gso _ _ (by rintro rfl; exact hx (by decide)), hget3 x hx]
  have hc5 := hc.temps hget5
  have hlast := offsets_last G (show I0 + 1 ≤ n by omega)
  have hmono := offsets_le G (show I0 ≤ I0 + 1 by omega) (show I0 + 1 ≤ n by omega)
  have hI' : I0 < n := hI
  have hdep' : s.dist[I0]! ≤ s.head := hdep
  have hdI' : s.dist[I0]! ≠ n := hdI
  have hE : ECtx m' le5 G be eo bD Dofs bQ I0 ((Graph.ofGraph G).degree I0)
      (Graph.ofGraph G).offsets[I0]! :=
    { he := hc5.he, hdist := hc5.hdist, hn := hc5.hn
      hi := by simp only [le5, le4]; rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hi3
      hdi := temps_gss _ _ _
      hvi := by simp only [le5, le4]; rw [temps_gso _ _ (by decide), temps_gss]; rfl
      earr := hc.earr, wptr := hc.wptr
      hVD := by simp only [Graph.degree]; omega
      hI := hI', Dn := degree_lt G hI', n31 := hn31
      bDe := fun h => (hc.sep be (by simp)).1 h.symm
      bQe := fun h => (hc.sep be (by simp)).2 h.symm
      bDQ := hc.bDQ
      bDW := fun h => (hc.sep Block.work4 (by simp)).1 h.symm
      bQW := fun h => (hc.sep Block.work4 (by simp)).2 h.symm }
  refine wp_edges hE hgood hdI' (by omega) (by omega)
    (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide),
          temps_gso _ _ (by decide), temps_gso _ _ (by decide), h1 _ (by decide)]; exact htl)
    hda hqa hqi ?_
  intro le'' m'' qv'' hda'' hqa'' hqi'' htl'' hu'' hout'' hkD'' hkQ'' hg'' ho''
  have hO := Good.outer (rows_ofGraph G) hgood hns
  refine hQ le'' m'' (outer (Graph.ofGraph G) s) qv'' (by rw [hO.2.1]; omega) ⟨hO.1, hO.2.2, ?_, ?_, htl'', hda'', hqa'',
    hqi'', hu.trans hu'', hout.trans hout'', hkD.trans hkD'', hkQ.trans hkQ'', fun z h => hg'' _ (hg _ h), fun x hx => ?_⟩
  · rw [hO.2.1, ← hrun, show n - s.head = (n - (s.head + 1)) + 1 by omega, run_succ hns]
  · rw [hO.2.1, ho'' _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide),
      temps_gso _ _ (by decide), temps_gss]
    push_cast; rfl
  · rw [ho'' _ (fun h => hx (by rcases h with h | h | h | h <;> simp [SearchLocal, h])), hget5 x hx,
      ho x hx]

theorem wp_search {n : Nat} {Q : Post} {le : temp_env} {m : mem} {G : Hex.SparseGraph n}
    {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {bD : block}
    {Dofs : ptrofs} {bQ : block} {v0 : Nat} {qv : Nat → val}
    (hc : SCtx m le G bv vo bd dofs be eo bD Dofs bQ) (hv0 : PTree.get id.v0 le = some (.Vint (ir v0)))
    (hv0n : v0 < n)
    (hdarr : ArrayAt m .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs)) (fun _ => .Vint (ir n)) n)
    (hqarr : ArrayAt m .Mint32 bQ 0 qv n)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bD (intOfZ (Ptrofs.unsigned Dofs))
        (ints (distvals (Graph.ofGraph G) v0)) n →
      (∃ qv', ArrayAt m' .Mint32 bQ 0 qv' n) → Unch m m' (fun z => z = bD ∨ z = bQ) →
      DOut m m' bD Dofs n → Alloc.Keep m m' bD → Alloc.Keep m m' bQ → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, ¬ SearchLocal x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F search Q empty_env le m := by
  have hn31 := hc.n31
  let g := Graph.ofGraph G
  wp_step; wp_step; wp_step
  refine wp_idx_store (pe := .Evar id.work4 (tptr tint)) (ofs := Ptrofs.zero) hqarr hn31
    (eval_work4 hc.wptr) rfl rfl rfl (ci 0 tint) 0 (by omega) rfl rfl
    (tv id.v0) tint rfl _ _ (by simp only [Exec.evalExpr]; exact hv0) rfl rfl ?_
  intro m1 hqa1 hu1 hk1 hg1
  dsimp only
  wp_step; wp_step; wp_step
  have hda1 := hdarr.unch hu1 (fun h => hc.bDQ h)
  refine wp_idx_store_out (pe := .Etempvar id.dist (tptr tint)) hda1 hn31
    (Int.le_refl _) (Int.le_refl _) (by simp only [Exec.evalExpr]; exact hc.hdist) rfl rfl rfl (tv id.v0) v0 hv0n hv0 rfl
    (ci 0 tint) tint rfl (.Vint (ir 0)) (.Vint (ir 0)) rfl rfl rfl ?_
  intro m2 hda2 hout2 hu2 hk2 hg2
  dsimp only
  have hqa2 := hqa1.unch hu2 (fun h => hc.bDQ h.symm)
  let s0 := start n v0
  let le0 := PTree.set id.tail (.Vint (ir 1)) (PTree.set id.head (.Vint (ir 0)) le)
  have hAt0 : At m m2 le le0 G bD Dofs bQ v0 s0 (upd qv 0 (.Vint (ir v0))) := by
    refine ⟨good_start hv0n, by simp [s0, start], by simp [s0, start],
      by simp only [le0, s0, start]; rw [temps_gso _ _ (by decide), temps_gss]; rfl,
      by simp only [le0, s0, start]; rw [temps_gss]; rfl,
      hda2.congr fun p hp => ?_, hqa2, fun p hp => ?_,
      (hu1.mono fun z hz => .inr hz).trans (hu2.mono fun z hz => .inl hz),
      (Outside.of_unch hu1 (fun h => hc.bDQ h) _ _).trans hout2, (Alloc.Keep.unch hu1 hc.bDQ).trans hk2, hk1.trans (Alloc.Keep.unch hu2 (fun h => hc.bDQ h.symm)),
      fun z h => hg2 _ (hg1 _ h), fun x hx => ?_⟩
    · simp only [ints, upd, s0, start]
      rw [get_set (by simp; omega)]
      by_cases hp' : p = v0
      · simp [hp']
      · rw [ite_eq_right hp', ite_eq_right (Ne.symm hp'), getElem!_pos _ p (by simp; omega)]
        simp
    · simp only [s0, start] at hp ⊢
      rw [show p = 0 by omega, get_set (by simp; omega)]
      simp
    · simp only [le0]
      rw [temps_gso _ _ (fun h => hx (.inr (.inr (.inl h)))),
        temps_gso _ _ (fun h => hx (.inr (.inl h)))]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  have hexit : ∀ s qv' le' le'' m', At m m' le le' G bD Dofs bQ v0 s qv' → Stop n s →
      (∀ x, ¬ SearchLocal x → PTree.get x le'' = PTree.get x le') → Q.normal E0 empty_env le'' m' := by
    rintro s qv' le' le'' m' ⟨hgood, hht, hrun, hhd, htl, hda, hqa, hqi, hu, hout, hkD, hkQ, hg, ho⟩ hst ho'
    refine hQ le'' m' (hda.congr fun p _ => ?_) ⟨qv', hqa⟩ hu hout hkD hkQ hg
      (fun x hx => (ho' x hx).trans (ho x hx))
    rw [distvals_eq, ← hrun, run_stop hst]
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ s qv', v = n - s.head ∧ At m m' le le' G bD Dofs bQ v0 s qv'
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ s qv', n - s.head < v ∧ At m m' le le' G bD Dofs bQ v0 s qv'
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0) ⟨rfl, rfl, s0, _, rfl, hAt0⟩
  · rintro v t e' le' m' ⟨rfl, rfl, s, qv', rfl, hgood, hht, hrun, hhd, htl, hda, hqa, hqi, hu, hout, hkD,
      hkQ, hg, ho⟩
    have hA : At m m' le le' G bD Dofs bQ v0 s qv' :=
      ⟨hgood, hht, hrun, hhd, htl, hda, hqa, hqi, hu, hout, hkD, hkQ, hg, ho⟩
    have hc' := (hc.temps ho).mem hu
    have hTn := hgood.tle
    wp_step; wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, htl, hc'.hn, typeof, cop]
    rw [ir_lt (a := (s.tail : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases htn : s.tail < n
    · rw [ite_eq_left (by simpa using htn)]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hhd, htl, typeof, cop, cast_b]
      rw [ir_lt (a := (s.head : Int)) (b := (s.tail : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      by_cases hht' : s.head < s.tail
      · rw [show decide ((s.head : Int) < s.tail) = true by simpa using hht']
        simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
        apply wp_skip
        dsimp only
        refine wp_body hA htn hht' hc' (fun x hx => temps_gso _ _ hx) ?_
        intro le'' m'' s' qv'' hlt hA'
        exact ⟨by simp, rfl, s', qv'', hlt, hA'⟩
      · rw [show decide ((s.head : Int) < s.tail) = false by simpa using hht']
        simp (config := {decide := true}) only [Val.of_bool, cop]
        apply wp_break
        simp only [E0_append]
        exact hexit s qv' le' _ m' hA (.inr (by omega)) (fun x hx => temps_gso _ _ (fun h => hx (.inr
          (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))
    · rw [ite_eq_right (by simpa using htn)]
      apply wp_set_eval
      simp only [Exec.evalExpr]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      rw [show (!Int.eq (Lib.Integers.Int.repr (zOfInt 0)) Int.zero) = false from rfl]
      apply wp_break
      simp only [E0_append]
      exact hexit s qv' le' _ m' hA (.inl (by omega)) (fun x hx => temps_gso _ _ (fun h => hx (.inr
        (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))
  · rintro v t e' le' m' ⟨rfl, rfl, s, qv', hlt, hA⟩
    apply wp_skip
    exact ⟨n - s.head, hlt, by simp, rfl, s, qv', rfl, hA⟩

end NautyVerified.Proofs.Sparse.Distvals

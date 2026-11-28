import NautyVerified.Proofs.Sparse.Isautom.Loops
import NautyVerified.Proofs.Sparse.Isautom.Rows
import NautyVerified.Proofs.Sparse.Prep

/-!
# `isautom_sg` meets its specification

`isautomSpec`: called with `digraph = FALSE` on a sparse graph `G`
(`SparseGraphAt`) and an array `perm` of vertices, nausparse.c's
`isautom_sg` returns HexGraphIso's `Sparse.isautom (ofGraph G) perm` (as 1
or 0), emitting no events and changing only the marks (`MarksAt`), which it
may reallocate through `preparemarks1` (`prep_satisfies`).
-/

namespace NautyVerified.Proofs.Sparse.Isautom

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse
open Hex.GraphIso.Nauty.Sparse (Graph)

variable {xi : ExternalCalls}

/-- The specification of `isautom_sg`. -/
def isautomSpec {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (bp : block) (pofs : ptrofs)
    (perm : Array Nat) (M cap : Nat) (b : block) (st : Nat) (marks : Nat → Int) : FunSpec where
  pre args m := args = [.Vptr bsg sofs, .Vptr bp pofs, .Vint (ir 0), .Vint (ir M), .Vint (ir n)] ∧
    SparseGraphAt m bsg sofs G bv vo bd dofs be eo ∧
    ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n ∧ (∀ x, x < n → perm[x]! < n) ∧
    MarksAt m cap b st marks ∧ 0 < n ∧ n < 2147483648 ∧
    (∀ z, z = bsg ∨ z = bv ∨ z = bd ∨ z = be ∨ z = bp → Mem.valid_block m z ∧
      z ≠ Block.vmark1 ∧ z ≠ Block.vmark1Sz ∧ z ≠ Block.vmark1Val ∧ (0 < cap → z ≠ b))
  post _ m t v m' := t = E0 ∧
    v = .Vint (ir (if Hex.GraphIso.Nauty.Sparse.isautom (Graph.ofGraph G) perm then 1 else 0)) ∧
    ∃ cap' b' st' marks', MarksAt m' cap' b' st' marks' ∧ n ≤ cap' ∧
      ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') ∧ Unch m m' (MarksS m cap b b') ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z)

def entryTemps (bsg : block) (sofs : ptrofs) (bp : block) (pofs : ptrofs) (M n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.digraph (.Vint (ir 0)) (PTree.set id.p (.Vptr bp pofs)
      (PTree.set id.g (.Vptr bsg sofs) (create_undef_temps F.fn_temps)))))

/-! ## Rows -/

theorem rowOk_iff {n : Nat} (G : Hex.SparseGraph n) (perm : Array Nat) {c : Nat} (hc : c < n)
    (hP : perm[c]! < n)
    (hdeg : (Graph.ofGraph G).degree perm[c]! = (Graph.ofGraph G).degree c) :
    RowOk (Graph.ofGraph G) perm c ↔
      ∀ j < (Graph.ofGraph G).degree c, ∃ j' < (Graph.ofGraph G).degree c,
        perm[(Graph.ofGraph G).neighbor ((Graph.ofGraph G).offsets[c]! + j')]! =
          (Graph.ofGraph G).neighbor ((Graph.ofGraph G).offsets[perm[c]!]! + j) := by
  have h1 := offsets_le G (Nat.le_succ c) hc
  have h2 := offsets_le G (Nat.le_succ perm[c]!) hP
  have hd1 : (Graph.ofGraph G).degree c =
      (Graph.ofGraph G).offsets[c + 1]! - (Graph.ofGraph G).offsets[c]! := rfl
  have hd2 : (Graph.ofGraph G).degree perm[c]! =
      (Graph.ofGraph G).offsets[perm[c]! + 1]! - (Graph.ofGraph G).offsets[perm[c]!]! := rfl
  constructor
  · rintro ⟨-, hrow⟩ j hj
    obtain ⟨e, he1, he2, he⟩ := hrow ((Graph.ofGraph G).offsets[perm[c]!]! + j) (by omega) (by omega)
    exact ⟨e - (Graph.ofGraph G).offsets[c]!, by omega, by rw [Nat.add_sub_cancel' he1]; exact he⟩
  · intro h
    refine ⟨hdeg, fun e he1 he2 => ?_⟩
    obtain ⟨j', hj', he⟩ := h (e - (Graph.ofGraph G).offsets[perm[c]!]!) (by omega)
    rw [Nat.add_sub_cancel' he1] at he
    exact ⟨_, by omega, by omega, he⟩

/-! ## The loop over `i` -/

/-- The temporaries a row of the loop changes. -/
def RowLocal (x : ident) : Prop :=
  x = id.pi ∨ x = id.di ∨ x = id.vi ∨ x = id.vpi ∨ x = id.j ∨ x = id.ij ∨ x = id.t1 ∨ x = id.t2

instance (x : ident) : Decidable (RowLocal x) := by unfold RowLocal; infer_instance

/-- The temporaries the loop over `i` changes. -/
def Local (x : ident) : Prop := x = id.i ∨ RowLocal x

instance (x : ident) : Decidable (Local x) := by unfold Local; infer_instance

/-- What the loop over `i` reads. -/
structure Frame {n : Nat} (m : mem) (le : temp_env) (G : Hex.SparseGraph n) (bsg : block)
    (sofs : ptrofs) (bv : block) (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs)
    (bp : block) (pofs : ptrofs) (perm : Array Nat) : Prop where
  hp : PTree.get id.p le = some (.Vptr bp pofs)
  hdig : PTree.get id.digraph le = some (.Vint (ir 0))
  hn : PTree.get id.n le = some (.Vint (ir n))
  hv : PTree.get id.v le = some (.Vptr bv vo)
  hd : PTree.get id.d le = some (.Vptr bd dofs)
  he : PTree.get id.e le = some (.Vptr be eo)
  graph : SparseGraphAt m bsg sofs G bv vo bd dofs be eo
  parr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n
  psmall : ∀ x, x < n → perm[x]! < n
  n31 : n < 2147483648

theorem Frame.temps {n : Nat} {m : mem} {le le' : temp_env} {G : Hex.SparseGraph n} {bsg : block}
    {sofs : ptrofs} {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs}
    {bp : block} {pofs : ptrofs} {perm : Array Nat}
    (h : Frame m le G bsg sofs bv vo bd dofs be eo bp pofs perm)
    (hle : ∀ x, ¬ Local x → PTree.get x le' = PTree.get x le) :
    Frame m le' G bsg sofs bv vo bd dofs be eo bp pofs perm :=
  { h with
    hp := by rw [hle _ (by decide)]; exact h.hp
    hdig := by rw [hle _ (by decide)]; exact h.hdig
    hn := by rw [hle _ (by decide)]; exact h.hn
    hv := by rw [hle _ (by decide)]; exact h.hv
    hd := by rw [hle _ (by decide)]; exact h.hd
    he := by rw [hle _ (by decide)]; exact h.he }

theorem Frame.mem {n : Nat} {m m' : mem} {le : temp_env} {G : Hex.SparseGraph n} {bsg : block}
    {sofs : ptrofs} {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs}
    {bp : block} {pofs : ptrofs} {perm : Array Nat}
    (h : Frame m le G bsg sofs bv vo bd dofs be eo bp pofs perm) {S : block → Prop} (hu : Unch m m' S)
    (hs : ∀ z, z = bsg ∨ z = bv ∨ z = bd ∨ z = be ∨ z = bp → ¬ S z) :
    Frame m' le G bsg sofs bv vo bd dofs be eo bp pofs perm :=
  { h with
    graph := h.graph.unch hu (hs _ (.inl rfl)) (hs _ (.inr (.inl rfl))) (hs _ (.inr (.inr (.inl rfl))))
      (hs _ (.inr (.inr (.inr (.inl rfl)))))
    parr := h.parr.unch hu (hs _ (.inr (.inr (.inr (.inr rfl))))) }

theorem dVals_eq {n : Nat} (G : Hex.SparseGraph n) (i : Nat) :
    dVals G i = .Vint (ir ((Graph.ofGraph G).degree i)) := rfl

/-- One row of the loop over `i`. -/
theorem wp_row {n : Nat} {Q : Post} {le : temp_env} {m : mem} {G : Hex.SparseGraph n} {bsg : block}
    {sofs : ptrofs} {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs}
    {bp : block} {pofs : ptrofs} {perm : Array Nat} {cap : Nat} {b : block} {st : Nat}
    {marks : Nat → Int} {c : Nat}
    (hf : Frame m le G bsg sofs bv vo bd dofs be eo bp pofs perm)
    (hi : PTree.get id.i le = some (.Vint (ir c))) (hc : c < n)
    (hM : MarksAt m cap b st marks) (hnc : n ≤ cap)
    (hsep : ∀ z, z = bsg ∨ z = bv ∨ z = bd ∨ z = be ∨ z = bp → (0 < cap → z ≠ b) ∧
      z ≠ Block.vmark1Val)
    (hQn : (perm[c]! ≠ c → RowOk (Graph.ofGraph G) perm c) → ∀ le' m' st' marks',
      MarksAt m' cap b st' marks' → Unch m m' (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b)) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, ¬ RowLocal x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m')
    (hQr : ¬ RowOk (Graph.ofGraph G) perm c → perm[c]! ≠ c → ∀ m' st' marks',
      MarksAt m' cap b st' marks' → Unch m m' (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b)) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.ret E0 (.Vint (ir 0)) m') :
    Wp xi sge F row Q empty_env le m := by
  have hn31 := hf.n31
  have hP := hf.psmall c hc
  have hpc := eval_idx (ge := sge) (e := empty_env) (le := le) (m := m) (pe := .Etempvar id.p (tptr tint)) hf.parr
    hn31 hf.hp rfl rfl rfl (tv id.i) c hc hi rfl
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, hpc, show Exec.evalExpr sge empty_env le m (tv id.i) = _ from hi]
  simp only [ints, typeof, cop]
  rw [ir_eq (a := (perm[c]! : Int)) (b := (c : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hfix : perm[c]! = c
  · rw [show decide ((perm[c]! : Int) = c) = true from decide_eq_true (by rw [hfix])]
    simp (config := {decide := true}) only [cop, ite_false]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hf.hdig, typeof, cop]
    apply wp_if_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ite_false]
    apply wp_skip
    refine hQn (fun h => absurd hfix h) _ m st marks hM (Unch.refl _ _) (fun _ h => h)
      (fun x hx => temps_gso _ _ (fun h => hx (by subst h; decide)))
  · rw [show decide ((perm[c]! : Int) = c) = false from decide_eq_false (by omega)]
    simp (config := {decide := true}) only [cop, ite_true]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    apply wp_if_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gss, typeof, cop, ite_true]
    let g := Graph.ofGraph G
    let P := perm[c]!
    let le1 := PTree.set id.t2 (.Vint (ir 1)) le
    have hf1 : Frame m le1 G bsg sofs bv vo bd dofs be eo bp pofs perm :=
      hf.temps fun x hx => temps_gso _ _ (fun h => hx (by subst h; decide))
    have hi1 : PTree.get id.i le1 = some (.Vint (ir c)) := by rw [temps_gso _ _ (by decide)]; exact hi
    have hdc : g.degree c ≤ n := degree_lt G hc
    have hdP : g.degree P ≤ n := degree_lt G hP
    have hPn : P < n := hP
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_tidx (ge := sge) hf1.parr hn31 hf1.hp rfl rfl (tv id.i) c hc hi1 rfl]
    simp only [ints]
    let le2 := PTree.set id.pi (.Vint (ir P)) le1
    have hf2 : Frame m le2 G bsg sofs bv vo bd dofs be eo bp pofs perm :=
      hf1.temps fun x hx => temps_gso _ _ (fun h => hx (by subst h; decide))
    have hi2 : PTree.get id.i le2 = some (.Vint (ir c)) := by rw [temps_gso _ _ (by decide)]; exact hi1
    have hpi2 : PTree.get id.pi le2 = some (.Vint (ir P)) := temps_gss _ _ _
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_tidx (ge := sge) hf2.graph.darr hn31 hf2.hd rfl rfl (tv id.i) c hc hi2 rfl, dVals_eq]
    let le3 := PTree.set id.di (.Vint (ir (g.degree c))) le2
    have hf3 : Frame m le3 G bsg sofs bv vo bd dofs be eo bp pofs perm :=
      hf2.temps fun x hx => temps_gso _ _ (fun h => hx (by subst h; decide))
    have hi3 : PTree.get id.i le3 = some (.Vint (ir c)) := by rw [temps_gso _ _ (by decide)]; exact hi2
    have hpi3 : PTree.get id.pi le3 = some (.Vint (ir P)) := by rw [temps_gso _ _ (by decide)]; exact hpi2
    have hdi3 : PTree.get id.di le3 = some (.Vint (ir (g.degree c))) := temps_gss _ _ _
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, eval_tidx (ge := sge) hf3.graph.darr hn31 hf3.hd rfl rfl (tv id.pi) P hP hpi3 rfl,
      dVals_eq, show Exec.evalExpr sge empty_env le3 m (tv id.di) = _ from hdi3]
    simp only [typeof, cop]
    rw [ir_eq (a := (g.degree P : Int)) (b := (g.degree c : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hdeg : g.degree P = g.degree c
    · rw [show decide ((g.degree P : Int) = g.degree c) = true from decide_eq_true (by rw [hdeg])]
      simp (config := {decide := true}) only [cop, ite_false]
      apply wp_skip
      have hc1 : c + 1 ≤ n := hc
      have hP1 : P + 1 ≤ n := hP
      have hoc : g.offsets[c]! ≤ g.offsets[c + 1]! := offsets_le G (Nat.le_succ c) hc1
      have hoP : g.offsets[P]! ≤ g.offsets[P + 1]! := offsets_le G (Nat.le_succ P) hP1
      have hoc' : g.offsets[c + 1]! ≤ G.neighbors.size := offsets_last G hc1
      have hoP' : g.offsets[P + 1]! ≤ G.neighbors.size := offsets_last G hP1
      have hdc' : g.degree c = g.offsets[c + 1]! - g.offsets[c]! := rfl
      have hdP' : g.degree P = g.offsets[P + 1]! - g.offsets[P]! := rfl
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_tidx (ge := sge) hf3.graph.varr hn31 hf3.hv rfl rfl (tv id.i) c hc hi3 rfl]
      simp only [vVals]
      let le4 := PTree.set id.vi (.Vlong (lr g.offsets[c]!)) le3
      have hf4 : Frame m le4 G bsg sofs bv vo bd dofs be eo bp pofs perm :=
        hf3.temps fun x hx => temps_gso _ _ (fun h => hx (by subst h; decide))
      have hpi4 : PTree.get id.pi le4 = some (.Vint (ir P)) := by
        rw [temps_gso _ _ (by decide)]; exact hpi3
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_tidx (ge := sge) hf4.graph.varr hn31 hf4.hv rfl rfl (tv id.pi) P hP hpi4 rfl]
      simp only [vVals]
      let le5 := PTree.set id.vpi (.Vlong (lr g.offsets[P]!)) le4
      have hf5 : Frame m le5 G bsg sofs bv vo bd dofs be eo bp pofs perm :=
        hf4.temps fun x hx => temps_gso _ _ (fun h => hx (by subst h; decide))
      wp_step
      refine wp_resetmarks1 (le := le5) hM ?_
      intro le6 m6 st6 marks6 hM6 hbelow hu6 hg6 ho6
      have hsepS : ∀ z, z = bsg ∨ z = bv ∨ z = bd ∨ z = be ∨ z = bp →
          ¬ (z = Block.vmark1Val ∨ (0 < cap ∧ z = b)) := by
        intro z hz h
        rcases h with h | ⟨h0, h⟩
        · exact (hsep z hz).2 h
        · exact (hsep z hz).1 h0 h
      have hf6 : Frame m6 le6 G bsg sofs bv vo bd dofs be eo bp pofs perm :=
        (hf5.mem hu6 hsepS).temps fun x hx => ho6 x (fun h => hx (by subst h; decide))
          (fun h => hx (by subst h; decide))
      have hdi6 : PTree.get id.di le6 = some (.Vint (ir (g.degree c))) := by
        rw [ho6 _ (by decide) (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]
        exact hdi3
      have hvi6 : PTree.get id.vi le6 = some (.Vlong (lr g.offsets[c]!)) := by
        rw [ho6 _ (by decide) (by decide), temps_gso _ _ (by decide)]; exact temps_gss _ _ _
      have hvpi6 : PTree.get id.vpi le6 = some (.Vlong (lr g.offsets[P]!)) := by
        rw [ho6 _ (by decide) (by decide)]; exact temps_gss _ _ _
      have hL6 : LoopCtx m6 le6 G be eo bp pofs perm (g.degree c) :=
        ⟨hf6.he, hf6.hp, hdi6, hf6.graph.earr, hf6.parr, hf6.psmall, hn31, by omega⟩
      have hsepb : 0 < cap → b ≠ be ∧ b ≠ bp := fun h0 =>
        ⟨fun h => (hsep be (.inr (.inr (.inr (.inl rfl))))).1 h0 h.symm,
         fun h => (hsep bp (.inr (.inr (.inr (.inr rfl))))).1 h0 h.symm⟩
      wp_step
      refine wp_markLoop hL6 hvi6 (by omega) hM6 hnc hbelow hsepb ?_
      intro le7 m7 marks7 hM7 hhit hu7 hg7 ho7
      have hL7 : LoopCtx m7 le7 G be eo bp pofs perm (g.degree c) :=
        (hL6.temps ho7).mem hu7 (fun ⟨h0, h⟩ => (hsepb h0).1 h.symm) (fun ⟨h0, h⟩ => (hsepb h0).2 h.symm)
      have hvpi7 : PTree.get id.vpi le7 = some (.Vlong (lr g.offsets[P]!)) := by
        rw [ho7 _ (by decide)]; exact hvpi6
      have hu : Unch m m7 (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b)) :=
        hu6.trans (hu7.mono fun z hz => .inr hz)
      have hrow : ∀ j < g.degree c, (marks7 (g.neighbor (g.offsets[P]! + j)) = st6 ↔
          ∃ j' < g.degree c, perm[g.neighbor (g.offsets[c]! + j')]! = g.neighbor (g.offsets[P]! + j)) :=
        fun j hj => hhit _ (by
          have : g.neighbor (g.offsets[P]! + j) < n := neighbor_lt G (by omega)
          omega)
      refine wp_checkLoop hL7 hvpi7 (by omega) hM7 hnc ?_ ?_
      · intro hall le8 ho8
        simp only [E0_append]
        refine hQn (fun _ => (rowOk_iff G perm hc hP hdeg).2 fun j hj => (hrow j hj).1 (hall j hj))
          le8 m7 st6 marks7 hM7 hu (fun z h => hg7 _ (hg6 _ h)) fun x hx => ?_
        have hx1 : x ≠ id.j := fun h => hx (by subst h; decide)
        have hx2 : x ≠ id.t1 := fun h => hx (by subst h; decide)
        have hx3 : x ≠ id.ij := fun h => hx (by subst h; decide)
        rw [ho8 x hx1, ho7 x hx1, ho6 x hx2 hx3]
        simp only [le5, le4, le3, le2, le1]
        rw [temps_gso _ _ (fun h => hx (by subst h; decide)), temps_gso _ _ (fun h => hx (by subst h; decide)),
          temps_gso _ _ (fun h => hx (by subst h; decide)), temps_gso _ _ (fun h => hx (by subst h; decide)),
          temps_gso _ _ (fun h => hx (by subst h; decide))]
      · rintro ⟨j, hj, hne⟩
        simp only [E0_append]
        refine hQr (fun hok => hne ((hrow j hj).2 ((rowOk_iff G perm hc hP hdeg).1 hok j hj))) hfix
          m7 st6 marks7 hM7 hu (fun z h => hg7 _ (hg6 _ h))
    · rw [show decide ((g.degree P : Int) = g.degree c) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [cop, ite_true]
      wp_step; wp_step
      apply wp_return_some_eval
      simp only [Exec.evalExpr, typeof, cop, sparse.fn.isautom_sg.fn_return_eq, free_empty]
      exact hQr (fun h => hdeg h.1) hfix m st marks hM (Unch.refl _ _) (fun _ h => h)

/-! ## The whole function -/

theorem type_preparemarks1 :
    type_of_fundef (.Internal sparse.fn.«nausparse:preparemarks1») = tfun [tulong] .Tvoid := rfl

theorem isautom_satisfies {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (bp : block) (pofs : ptrofs)
    (perm : Array Nat) (M cap : Nat) (b : block) (st : Nat) (marks : Nat → Int) :
    Satisfies xi sge (.Internal F)
      (isautomSpec G bsg sofs bv vo bd dofs be eo bp pofs perm M cap b st marks) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bsg sofs bp pofs M n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bsg sofs bp pofs M n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hgr, hparr, hps, hM, hn0, hn31, hsep⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [sparse.fn.isautom_sg.fn_body_eq, body_eq]
    let le0 := entryTemps bsg sofs bp pofs M n
    have hg0 : PTree.get id.g le0 = some (.Vptr bsg sofs) := by
      simp (config := {decide := true}) only [le0, entryTemps, temps_gso, temps_gss]
    let le1 := PTree.set id.e (.Vptr be eo) (PTree.set id.d (.Vptr bd dofs)
      (PTree.set id.v (.Vptr bv vo) le0))
    wp_step
    refine wp_loop (I := fun _ t e' le' m' => t = E0 ∧ e' = empty_env ∧ le' = le0 ∧ m' = m)
      (J := fun _ t e' le' m' => t = E0 ∧ e' = empty_env ∧ le' = le1 ∧ m' = m) ?_ ?_ (n := 0)
      ⟨rfl, rfl, rfl, rfl⟩
    · rintro - t e' le' m' ⟨rfl, rfl, rfl, hm⟩
      subst m'
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_sgField hg0 (lval_v _ _) rfl hgr.v]
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_sgField (by rw [temps_gso _ _ (by decide)]; exact hg0) (lval_d _ _) rfl hgr.d]
      wp_step; wp_step
      apply wp_set_eval
      rw [eval_sgField (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hg0)
        (lval_e _ _) rfl hgr.e]
      exact ⟨rfl, rfl, rfl, rfl⟩
    rintro - t e' le' m' ⟨rfl, rfl, rfl, hm⟩
    subst m'
    wp_step; wp_step
    apply wp_break
    simp only [E0_append]
    have hn1 : PTree.get id.n le1 = some (.Vint (ir n)) := by
      simp (config := {decide := true}) only [le1, le0, entryTemps, temps_gso, temps_gss]
    have hf : Frame m le1 G bsg sofs bv vo bd dofs be eo bp pofs perm :=
      { hp := by simp (config := {decide := true}) only [le1, le0, entryTemps, temps_gso, temps_gss]
        hdig := by simp (config := {decide := true}) only [le1, le0, entryTemps, temps_gso, temps_gss]
        hn := hn1
        hv := by simp (config := {decide := true}) only [le1, temps_gso, temps_gss]
        hd := by simp (config := {decide := true}) only [le1, temps_gso, temps_gss]
        he := by simp (config := {decide := true}) only [le1, temps_gss]
        graph := hgr, parr := hparr, psmall := hps, n31 := hn31 }
    wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr Block.preparemarks1 Ptrofs.zero) (targs := [tulong]) (tres := .Tvoid)
      (cc := Common.AST.cc_default) _ (prepSpec n cap b st marks) (prep_satisfies _ _ _ _ _) rfl
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
        show PTree.get sparse.id.«nausparse:preparemarks1» (empty_env : env) = none from rfl,
        find_preparemarks1, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
      (by simp only [Exec.evalExprlist, Exec.evalExpr, hn1, typeof, cop,
            cast_int_long_ir (a := n) ⟨by omega, by omega⟩])
      (by simp [Common.Globalenvs.Genv.find_funct, funct_preparemarks1]) type_preparemarks1
      ⟨rfl, hM, hn31⟩ ?_
    rintro t - m1 ⟨rfl, cap1, b1, st1, marks1, hM1, hnc1, hor, hu1, hg1⟩
    simp only [set_opttemp, E0_append]
    have hcap1 : 0 < cap1 := by omega
    have hS1 : ∀ z, z = bsg ∨ z = bv ∨ z = bd ∨ z = be ∨ z = bp → ¬ MarksS m cap b b1 z := by
      intro z hz h
      obtain ⟨hv, h1, h2, h3, h4⟩ := hsep z hz
      rcases h with h | h | h | ⟨hc, h⟩ | ⟨hnv, h⟩
      · exact h1 h
      · exact h2 h
      · exact h3 h
      · exact h4 hc h
      · exact hnv (h ▸ hv)
    have hsep1 : ∀ z, z = bsg ∨ z = bv ∨ z = bd ∨ z = be ∨ z = bp → (0 < cap1 → z ≠ b1) ∧
        z ≠ Block.vmark1Val := by
      intro z hz
      obtain ⟨hv, -, -, h3, h4⟩ := hsep z hz
      refine ⟨fun _ h => ?_, h3⟩
      rcases hor with ⟨rfl, rfl⟩ | hnv
      · exact h4 hcap1 h
      · exact hnv (h ▸ hv)
    have hf1 := hf.mem hu1 hS1
    have hpost : ∀ m' st' marks', MarksAt m' cap1 b1 st' marks' →
        Unch m1 m' (fun z => z = Block.vmark1Val ∨ (0 < cap1 ∧ z = b1)) →
        (∀ z, Mem.valid_block m1 z → Mem.valid_block m' z) →
        ∃ cap' b' st' marks', MarksAt m' cap' b' st' marks' ∧ n ≤ cap' ∧
          ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') ∧ Unch m m' (MarksS m cap b b') ∧
          (∀ z, Mem.valid_block m z → Mem.valid_block m' z) := by
      intro m' st' marks' hM' hu' hg'
      refine ⟨cap1, b1, st', marks', hM', hnc1, hor, hu1.trans (hu'.mono fun z hz => ?_),
        fun z h => hg' _ (hg1 _ h)⟩
      rcases hz with rfl | ⟨-, rfl⟩
      · exact .inr (.inr (.inl rfl))
      · rcases hor with ⟨rfl, rfl⟩ | hnv
        · exact .inr (.inr (.inr (.inl ⟨by omega, rfl⟩)))
        · exact .inr (.inr (.inr (.inr ⟨hnv, rfl⟩)))
    let g := Graph.ofGraph G
    have hrows := isautom_rows G perm hps
    let I := fun (k : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
      e' = empty_env ∧ ∃ c st' marks', c ≤ n ∧ k = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
        MarksAt m' cap1 b1 st' marks' ∧
        Unch m1 m' (fun z => z = Block.vmark1Val ∨ (0 < cap1 ∧ z = b1)) ∧
        (∀ z, Mem.valid_block m1 z → Mem.valid_block m' z) ∧
        (∀ v < c, perm[v]! ≠ v → RowOk g perm v) ∧ ∀ x, ¬ Local x → PTree.get x le' = PTree.get x le1
    let J := fun (k : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
      e' = empty_env ∧ ∃ c st' marks', c < n ∧ k = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
        MarksAt m' cap1 b1 st' marks' ∧
        Unch m1 m' (fun z => z = Block.vmark1Val ∨ (0 < cap1 ∧ z = b1)) ∧
        (∀ z, Mem.valid_block m1 z → Mem.valid_block m' z) ∧
        (∀ v < c + 1, perm[v]! ≠ v → RowOk g perm v) ∧ ∀ x, ¬ Local x → PTree.get x le' = PTree.get x le1
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0)
      ⟨rfl, rfl, 0, st1, marks1, Nat.zero_le _, rfl, temps_gss _ _ _, hM1, Unch.refl _ _,
        fun _ h => h, fun v hv => absurd hv (by omega),
        fun x hx => temps_gso _ _ (fun h => hx (by subst h; decide))⟩
    · rintro k t e' le' m' ⟨rfl, rfl, c, st', marks', hc, rfl, hi, hM', hu', hg', hrow, ho⟩
      have hf' := (hf1.mem hu' fun z hz h => by
        rcases h with h | ⟨h0, h⟩
        · exact (hsep1 z hz).2 h
        · exact (hsep1 z hz).1 h0 h).temps ho
      wp_step; wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tv id.i) = _ from hi,
        show Exec.evalExpr sge empty_env le' m' (tv id.n) = _ from hf'.hn]
      simp only [typeof, cop]
      rw [ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hcn : c < n
      · rw [ite_eq_left (by simpa using hcn)]
        apply wp_skip
        refine wp_row hf' hi hcn hM' hnc1 hsep1 ?_ ?_
        · intro hok le'' m'' st'' marks'' hM'' hu'' hg'' ho''
          refine ⟨by simp, rfl, c, st'', marks'', hcn, rfl, ?_, hM'',
            hu'.trans hu'', fun z h => hg'' _ (hg' _ h), fun v hv hmv => ?_, fun x hx => ?_⟩
          · rw [ho'' _ (by decide)]; exact hi
          · rcases Nat.lt_or_ge v c with h | h
            · exact hrow v h hmv
            · rw [show v = c by omega] at hmv ⊢; exact hok hmv
          · rw [ho'' x (fun h => hx (.inr h)), ho x hx]
        · intro hbad hmv m'' st'' marks'' hM'' hu'' hg''
          refine ⟨by simp, ?_, hpost m'' st'' marks'' hM'' (hu'.trans hu'') fun z h => hg'' _ (hg' _ h)⟩
          have : Hex.GraphIso.Nauty.Sparse.isautom (Graph.ofGraph G) perm = false := by
            cases hh : Hex.GraphIso.Nauty.Sparse.isautom (Graph.ofGraph G) perm with
            | false => rfl
            | true => exact absurd ((hrows.1 hh) c hcn hmv) hbad
          rw [this]; rfl
      · rw [ite_eq_right (by simpa using hcn)]
        apply wp_break
        have hall : ∀ v, v < n → perm[v]! ≠ v → RowOk g perm v := fun v hv => hrow v (by omega)
        wp_step; wp_step
        apply wp_return_some_eval
        simp only [Exec.evalExpr, typeof, cop, sparse.fn.isautom_sg.fn_return_eq, free_empty]
        refine ⟨by simp, ?_, hpost m' st' marks' hM' hu' hg'⟩
        rw [hrows.2 hall]; rfl
    · rintro k t e' le' m' ⟨rfl, rfl, c, st', marks', hc, rfl, hi, hM', hu', hg', hrow, ho⟩
      wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tv id.i) = _ from hi]
      simp only [Exec.evalExpr, typeof, cop, ir_add]
      exact ⟨n - (c + 1), by omega, by simp, rfl, c + 1, st', marks', hc, rfl, temps_gss _ _ _, hM', hu',
        hg', hrow, fun x hx => by rw [temps_gso _ _ (fun h => hx (by subst h; decide)), ho x hx]⟩

end NautyVerified.Proofs.Sparse.Isautom

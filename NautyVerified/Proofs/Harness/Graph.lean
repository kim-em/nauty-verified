import NautyVerified.Proofs.Harness.Input
import NautyVerified.Proofs.Set.Clear
import NautyVerified.Proofs.Graph.Rows

/-!
# The graph the harness builds

`wp_emptyG`: `EMPTYGRAPH(g, m, n)` zeroes the `m * n` words of `g` (the loop is
`EMPTYSET`'s, `Set.wp_emptySet'`, over `m * n` words).
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk longs clearedFromV clearedFromV_succ cmplu_ptrTo sub_ptrTo8 sizeof_tulong)
open NautyVerified.Proofs.Graph (add_ptrTo_long)

variable {xi : ExternalCalls}

theorem wp_emptyG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {ba : block}
    {ofs : ptrofs} {vals : Nat → val} {Mw N : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) vals (Mw * N)) (hM : 0 < Mw * N)
    (hM2 : Mw * N < 2147483648) (hMw : Mw < 2147483648) (hN : N < 2147483648)
    (hact : PTree.get dense.id.g le = some (.Vptr ba ofs))
    (hmv : PTree.get dense.id.m le = some (.Vint (ir Mw)))
    (hnv : PTree.get dense.id.n le = some (.Vint (ir N)))
    (hQ : ∀ le' m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs fun _ => lr 0) (Mw * N) →
      Unch m m' (· = ba) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * (Mw * N)) →
      (∀ k, k ≠ dense.id.es_ → k ≠ idOf 712 → PTree.get k le' = PTree.get k le) → Q.normal E0 e le' m') :
    Wp xi ge f emptyG Q e le m := by
  have hf := harr.fits
  have hb := harr.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  simp only [emptyG, sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hact, hmv, hnv, typeof, cop,
    cast_int_long_ir (a := (N : Int)) ⟨by omega, by omega⟩,
    cast_int_long_ir (a := (Mw : Int)) ⟨by omega, by omega⟩]
  rw [show Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir (Mw : Int))) = lr (Mw : Int) from
    cast_int_long_ir ⟨by omega, by omega⟩,
    show (Lib.Integers.Int64.mul (lr (Mw : Int)) (lr (N : Int))) = lr ((Mw * N : Nat) : Int) from
    (Alloc.lr_mul Mw N), add_ptrTo_long]
  simp only [E0_append]
  let base := intOfZ (Ptrofs.unsigned ofs)
  refine wp_loop (I := fun k t e' le' m' => t = E0 ∧ e = e' ∧ k ≤ (Mw * N) ∧
      PTree.get dense.id.es_ le' = some (.Vptr ba (ptrTo base 8 k)) ∧
      ArrayAt m' .Mint64 ba base (clearedFromV vals k) (Mw * N) ∧ Unch m m' (· = ba) ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
      Outside m m' ba base (base + 8 * (Mw * N)) ∧
      ∀ k', k' ≠ dense.id.es_ → k' ≠ idOf 712 → PTree.get k' le' = PTree.get k' le)
    (J := fun k t e' le' m' => ∃ k' < k, t = E0 ∧ e = e' ∧ k' ≤ (Mw * N) ∧
      PTree.get dense.id.es_ le' = some (.Vptr ba (ptrTo base 8 k')) ∧
      ArrayAt m' .Mint64 ba base (clearedFromV vals k') (Mw * N) ∧ Unch m m' (· = ba) ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
      Outside m m' ba base (base + 8 * (Mw * N)) ∧
      ∀ k'', k'' ≠ dense.id.es_ → k'' ≠ idOf 712 → PTree.get k'' le' = PTree.get k'' le) ?_ ?_ (n := (Mw * N))
    ⟨rfl, rfl, Nat.le_refl _, temps_gss _ _ _, by
      refine ⟨hb, by rw [h8]; omega, fun i hi => ?_, fun i hi => harr.writable i hi⟩
      simp only [clearedFromV, ite_eq_left hi]; exact harr.load i hi,
      Unch.refl _ _, fun _ h => h, Outside.refl _ _ _ _, fun k' hk _ => temps_gso _ _ hk⟩
  · rintro k t e' le' m' ⟨rfl, rfl, hk, hes, harr', hu, hgr, hout, hother⟩
    have hact' : PTree.get dense.id.g le' = some (.Vptr ba ofs) := by
      rw [hother _ (by decide) (by decide)]; exact hact
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hes, hact', typeof, cop]
    rw [cmplu_ptrTo harr' hM hk rfl]
    simp only [Option.map, cop]
    rcases k with _ | j
    · rw [ite_eq_right (by decide)]
      apply wp_break
      have h0 : clearedFromV vals 0 = longs fun _ => lr 0 := by funext w; simp [clearedFromV, longs]
      rw [h0] at harr'
      exact hQ le' m' harr' hu hgr hout hother
    · rw [ite_eq_left (by simp)]
      apply wp_skip
      simp only [E0_append]
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hes, typeof, cop, sub_ptrTo8]
      simp only [E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss, E0_append]
      have hj : j < (Mw * N) := by omega
      have hu8 : intOfZ (Ptrofs.unsigned (ptrTo base 8 j)) = base + 8 * j := by
        apply unsigned_ptrTo <;> omega
      obtain ⟨m'', hst, harr'', -⟩ := store_array harr' hj (.Vlong (lr 0)) rfl
      apply wp_assign_eval
      simp (config := {decide := true}) only [Exec.evalLvalue, Exec.evalExpr, temps_gss, temps_gso, typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode,
        cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
      show match Mem.store .Mint64 m' ba (Ptrofs.unsigned _) _ with
        | some m' => _ | none => False
      rw [show Ptrofs.unsigned (ptrTo base 8 j) = elemOfs .Mint64 base j by
        rw [← zOfInt_intOfZ (Ptrofs.unsigned _), hu8]; rfl, hst]
      refine ⟨j, by omega, trivial, trivial, by omega, ?_, ?_, hu.trans (Unch.store hst rfl),
        fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ (hgr _ hz), hout.trans (Outside.store harr' hj hst (Int.le_refl _) (by rw [h8]; exact Int.le_refl _)), ?_⟩
      · rfl
      · rw [← clearedFromV_succ]; exact harr''
      · intro k'' h1 h2
        rw [temps_gso _ _ h1, temps_gso _ _ h2, hother _ h1 h2]
  · rintro k t e' le' m' ⟨k', hk', h⟩
    apply wp_skip
    exact ⟨k', hk', by simpa using h⟩



/-- `g[m * x + (y >> 6)]` (`GRAPHROW(g, x, m)[SETWD(y)]`). -/
abbrev gword (x y : ident) : expr :=
  .Ederef (.Ebinop .Oadd (.Ebinop .Oadd (.Ecast (pl dense.id.g) (tptr tulong))
      (.Ebinop .Omul (tv dense.id.m) (.Ecast (tv x) tulong) tulong) (tptr tulong))
    (.Ebinop .Oshr (tv y) (ci 6 tint) tint) (tptr tulong)) tulong

/-- dense_main.c's `bit[y & 63]`. -/
abbrev dmBit (y : ident) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar dense.id.«dense_main:bit» (tarray tulong 64))
    (.Ebinop .Oand (tv y) (ci 63 tint) tint) (tptr tulong)) tulong

/-- `ADDELEMENT(GRAPHROW(g, x, m), y)`. -/
abbrev addEdgeS (x y : ident) : statement :=
  sk (.Sassign (gword x y) (.Ebinop .Oor (gword x y) (dmBit y) tulong))

/-- The edge loop's body. -/
abbrev edgeBody : statement :=
  .Ssequence (.Ssequence (sk (rd (idOf 713))) (.Sset dense.id.a (.Ecast (.Etempvar (idOf 713) tlong) tint)))
    (.Ssequence (.Ssequence (sk (rd (idOf 714))) (.Sset dense.id.b (.Ecast (.Etempvar (idOf 714) tlong) tint)))
      (.Ssequence (addEdgeS dense.id.a dense.id.b) (addEdgeS dense.id.b dense.id.a)))

theorem edgeLoop_eq :
    .Ssequence (sk (.Sset dense.id.i (ci 0 tint))) edgeLoop = forT dense.id.i (tv dense.id.ne) edgeBody := rfl

/-- The words after setting bit `y` of row `x`. -/
abbrev setEdge (Mw : Nat) (W : Nat → Lib.Integers.int64) (x y : Nat) : Nat → Lib.Integers.int64 :=
  upd W (Mw * x + y / 64) (Lib.Integers.Int64.or (W (Mw * x + y / 64)) (lr ((2 ^ (63 - y % 64) : Nat) : Int)))

/-- The shared address computations of `s[a >> 6]` and `bit[a & 63]`. -/
theorem bit_facts {c : Nat} (hc2 : c < 2147483648) :
    Lib.Integers.Int.ltu (ir 6) Lib.Integers.Int.iwordsize = true ∧
    Lib.Integers.Int.shr (ir c) (ir 6) = ir ((c / 64 : Nat) : Int) ∧
    Lib.Integers.Int.and (ir c) (ir 63) = ir ((c % 64 : Nat) : Int) ∧
    Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int))))) =
      elemOfs .Mint64 0 (c % 64) := by
  have hb : c % 64 < 64 := Nat.mod_lt _ (by decide)
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [ir_shr6 ⟨by omega, by omega⟩]; congr 1
  · rw [ir_and63 (by omega) (by omega)]; congr 1
  · apply addr_elem _ _ .Mint64 rfl (base := 0) (by decide) (by omega)
    have h8 : csize .Mint64 = 8 := rfl
    rw [h8]; omega

theorem wp_addEdgeS {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bg : block}
    {W : Nat → Lib.Integers.int64} {Mw N X Y : Nat} (x y : ident)
    (harr : ArrayAt m .Mint64 bg 0 (longs W) (Mw * N)) (hMN : Mw * N < 2147483648)
    (hX : X < N) (hY : Y < 64 * Mw) (hYs : Y < 2147483648)
    (hg : PTree.get dense.id.g le = some (.Vptr bg Ptrofs.zero))
    (hm : PTree.get dense.id.m le = some (.Vint (ir Mw)))
    (hx : PTree.get x le = some (.Vint (ir X))) (hy : PTree.get y le = some (.Vint (ir Y)))
    (hbit : Set.BitTable m Block.denseMainBit) (he : PTree.get dense.id.«dense_main:bit» e = none)
    (heg : PTree.get dense.id.g e = none)
    (hQ : ∀ m', ArrayAt m' .Mint64 bg 0 (longs (setEdge Mw W X Y)) (Mw * N) → Unch m m' (· = bg) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (addEdgeS x y) Q e le m := by
  have hMw : 0 < Mw := by omega
  have hMwN : Mw ≤ Mw * N := Nat.le_mul_of_pos_right _ (by omega)
  have hNMw : N ≤ Mw * N := Nat.le_mul_of_pos_left _ hMw
  have hidx : Mw * X + Y / 64 < Mw * N := by
    have : Mw * X + Mw ≤ Mw * N := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hX
    omega
  have hb : Y % 64 < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨h6, hshr, hand, hbaddr⟩ := bit_facts (c := Y) hYs
  obtain ⟨m', hst, harr', -⟩ := store_array harr hidx
    (.Vlong (Lib.Integers.Int64.or (W (Mw * X + Y / 64)) (lr ((2 ^ (63 - Y % 64) : Nat) : Int)))) rfl
  simp only [addEdgeS, gword, dmBit, sk]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hg, hm, hx, hy, he, heg, find_denseMainBit]
  simp only [typeof, cop, h6, hshr, hand, ite_true]
  have haddr : Ptrofs.add (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_int64 (Lib.Integers.Int64.mul
        (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir (Mw : Int))))
        (Cfrontend.Cop.cast_int_long .Signed (ir (X : Int)))))))
      (Ptrofs.mul (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong))
        (Ptrofs.of_ints (ir ((Y / 64 : Nat) : Int)))) = ptrTo 0 8 (Mw * X + Y / 64) := by
    rw [show Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir (Mw : Int))) = lr (Mw : Int) from
      cast_int_long_ir ⟨by omega, by omega⟩, cast_int_long_ir ⟨by omega, by omega⟩,
      show (Lib.Integers.Int64.mul (lr (Mw : Int)) (lr (X : Int))) = lr ((Mw * X : Nat) : Int) from
        (Alloc.lr_mul Mw X), add_ptrTo_long, add_ptrTo _ _ _ (by omega)]
    rw [show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl,
      unsigned_ptrTo (by omega) (by omega)]
    simp only [ptrTo, sizeof_tulong]
    congr 2
    push_cast; omega
  have hu : Ptrofs.unsigned (ptrTo 0 8 (Mw * X + Y / 64)) = elemOfs .Mint64 0 (Mw * X + Y / 64) := by
    have := unsigned_ptrTo (base := 0) (sz := 8) (k := Mw * X + Y / 64) (by omega) (by omega)
    rw [← zOfInt_intOfZ (Ptrofs.unsigned _), this]; rfl
  rw [haddr]
  simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Exec.assignLoc]
  simp only [cop]
  have hl1 : Mem.loadv .Mint64 m (.Vptr bg (ptrTo 0 8 (Mw * X + Y / 64))) =
      some (longs W (Mw * X + Y / 64)) := load_array harr hidx hu
  have hl2 : Mem.loadv .Mint64 m (.Vptr Block.denseMainBit (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong))
      (Ptrofs.of_ints (ir ((Y % 64 : Nat) : Int)))))) =
      some (.Vlong (lr ((2 ^ (63 - Y % 64) : Nat) : Int))) := by
    show Mem.load _ _ _ _ = _
    rw [hbaddr]; exact hbit _ hb
  simp only [hl1, hl2, longs, cop, Mem.storev]
  rw [hu, hst]
  rw [Set.longs_upd] at harr'
  exact hQ m' harr' (Unch.store hst rfl) fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz

/-! ## The rows the edges give -/

open Hex.GraphIso Hex.GraphIso.Nauty in
/-- Row `v` after one edge: `ADDONEEDGE(g, a, b)` sets `b` in row `a`, then `a` in row `b`. -/
def edgeStep {n : Nat} (v : Nat) (s : VSet n) (e : Fin n × Fin n) : VSet n :=
  let s := if e.1.val = v then s.insert e.2.val else s
  if e.2.val = v then s.insert e.1.val else s

open Hex.GraphIso Hex.GraphIso.Nauty in
/-- Row `v` after the first `k` edges. -/
def edgeRow {n : Nat} (es : List (Fin n × Fin n)) (k v : Nat) : VSet n :=
  (es.take k).foldl (edgeStep v) .empty

/-- The words after the first `k` edges. -/
def edgeWords {n : Nat} (Mw : Nat) (es : List (Fin n × Fin n)) (k : Nat) :
    Nat → Lib.Integers.int64 :=
  (es.take k).foldl (fun W e => setEdge Mw (setEdge Mw W e.1.val e.2.val) e.2.val e.1.val)
    (fun _ => lr 0)

theorem row_eq {Mw v a w c : Nat} (hw : w < Mw) (hc : c < Mw) (h : Mw * v + w = Mw * a + c) :
    v = a ∧ w = c := by
  have hMw : 0 < Mw := by omega
  have h1 : (Mw * v + w) / Mw = v := by rw [Nat.mul_add_div hMw, Nat.div_eq_of_lt hw]; omega
  have h2 : (Mw * a + c) / Mw = a := by rw [Nat.mul_add_div hMw, Nat.div_eq_of_lt hc]; omega
  rw [h] at h1
  have hva : v = a := by omega
  subst hva
  omega

open Hex.GraphIso.Nauty in
theorem setRep_setEdge {n Mw : Nat} {W : Nat → Lib.Integers.int64} {s : VSet n} {a b v : Nat}
    (h : SetRep (fun w => bv64 (W (Mw * v + w))) Mw s) (hb : b < n) :
    SetRep (fun w => bv64 (setEdge Mw W a b (Mw * v + w))) Mw (if a = v then s.insert b else s) := by
  have hbM : b / 64 < Mw := by have := h.1; omega
  by_cases hav : a = v
  · subst hav
    rw [if_pos rfl]
    refine Graph.setRep_congr (Set.setRep_add h hb) fun w hw => ?_
    simp only [Set.addW, setEdge, upd]
    by_cases hwb : w = b / 64
    · subst hwb; simp
    · rw [ite_eq_right hwb, ite_eq_right (by omega)]
  · rw [if_neg hav]
    refine Graph.setRep_congr h fun w hw => ?_
    simp only [setEdge, upd]
    rw [ite_eq_right fun he => hav (row_eq hw hbM he).1.symm]

open Hex.GraphIso.Nauty in
theorem setRep_edgeWords {n Mw : Nat} (es : List (Fin n × Fin n)) (hn : n ≤ 64 * Mw) :
    ∀ k v, SetRep (fun w => bv64 (edgeWords Mw es k (Mw * v + w))) Mw (edgeRow es k v) := by
  intro k
  induction k with
  | zero =>
    intro v
    simp only [edgeWords, edgeRow, List.take_zero, List.foldl_nil]
    exact ⟨hn, fun u _ => by simp [SetwordsMem, intOfZ_zOfInt]⟩
  | succ k ih =>
    intro v
    rcases Nat.lt_or_ge k es.length with hk | hk
    · simp only [edgeWords, edgeRow, List.take_add_one, List.getElem?_eq_getElem hk,
        Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have h1 := setRep_setEdge (a := es[k].1.val) (b := es[k].2.val) (ih v) es[k].2.isLt
      have h2 := setRep_setEdge (a := es[k].2.val) (b := es[k].1.val) h1 es[k].1.isLt
      exact h2
    · rw [show edgeWords Mw es (k + 1) = edgeWords Mw es k by
          simp only [edgeWords]; rw [List.take_of_length_le (by omega),
            List.take_of_length_le (by omega)],
        show edgeRow es (k + 1) v = edgeRow es k v by
          simp only [edgeRow]; rw [List.take_of_length_le (by omega),
            List.take_of_length_le (by omega)]]
      exact ih v

open Hex.GraphIso.Nauty in
theorem mem_edgeStep {n : Nat} (v u : Nat) (s : VSet n) (e : Fin n × Fin n) :
    (edgeStep v s e).mem u =
      (s.mem u || decide ((e.1.val = v ∧ e.2.val = u) ∨ (e.2.val = v ∧ e.1.val = u))) := by
  have h1 := e.1.isLt
  have h2 := e.2.isLt
  unfold edgeStep
  by_cases ha : e.1.val = v <;> by_cases hb : e.2.val = v
  · simp only [ha, hb, ite_true, VSet.mem_insert_of_lt _ (show v < n by omega)]
    cases s.mem u <;> by_cases hu : v = u <;> simp [hu]
  · simp only [ha, hb, ite_true, ite_false, VSet.mem_insert_of_lt _ h2]
    cases s.mem u <;> by_cases hu : e.2.val = u <;> simp [hu, hb, ha]
  · simp only [ha, hb, ite_true, ite_false, VSet.mem_insert_of_lt _ h1]
    cases s.mem u <;> by_cases hu : e.1.val = u <;> simp [hu, hb, ha]
  · simp only [ha, hb, ite_false]
    cases s.mem u <;> simp [ha, hb]

open Hex.GraphIso.Nauty in
theorem mem_foldl_edgeStep {n : Nat} (v u : Nat) :
    ∀ (l : List (Fin n × Fin n)) (s : VSet n), (l.foldl (edgeStep v) s).mem u =
      (s.mem u || decide (∃ e ∈ l, (e.1.val = v ∧ e.2.val = u) ∨ (e.2.val = v ∧ e.1.val = u)))
  | [], s => by simp
  | e :: l, s => by
    rw [List.foldl_cons, mem_foldl_edgeStep v u l, mem_edgeStep, Bool.or_assoc, ← Bool.decide_or]
    congr 1
    apply decide_eq_decide.2
    constructor
    · rintro (h | ⟨e', he', h⟩)
      · exact ⟨e, List.mem_cons_self, h⟩
      · exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · rintro ⟨e', he', h⟩
      rcases List.mem_cons.1 he' with rfl | he'
      · exact .inl h
      · exact .inr ⟨e', he', h⟩

open Hex.GraphIso Hex.GraphIso.Nauty in
/-- After all edges, the rows are `G`'s. -/
theorem edgeRow_rowsOf {n k : Nat} {G : Colored n k} {es : List (Fin n × Fin n)}
    (hadj : ∀ u v : Fin n, G.graph.adj u v = true ↔ ((u, v) ∈ es ∨ (v, u) ∈ es)) {v : Nat}
    (hv : v < n) : edgeRow es es.length v = (rowsOf G)[v]! := by
  apply VSet.ext
  intro u
  simp only [edgeRow, List.take_length]
  rw [mem_foldl_edgeStep, VSet.mem_empty, Bool.false_or]
  have hrow : (rowsOf G)[v]! = rowOf G v := by
    simp [rowsOf, hv]
  rw [hrow, mem_rowOf]
  by_cases hu : u < n
  · rw [dite_eq_left ⟨hv, hu⟩]
    rcases hA : G.graph.adj ⟨v, hv⟩ ⟨u, hu⟩ with _ | _
    · simp only [decide_eq_false_iff_not]
      rintro ⟨e, he, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
      · have : (⟨v, hv⟩, ⟨u, hu⟩) = e := by ext <;> simp [h1, h2]
        have := (hadj ⟨v, hv⟩ ⟨u, hu⟩).2 (.inl (this ▸ he))
        rw [hA] at this; cases this
      · have : (⟨u, hu⟩, ⟨v, hv⟩) = e := by ext <;> simp [h1, h2]
        have := (hadj ⟨v, hv⟩ ⟨u, hu⟩).2 (.inr (this ▸ he))
        rw [hA] at this; cases this
    · simp only [decide_eq_true_eq]
      rcases (hadj ⟨v, hv⟩ ⟨u, hu⟩).1 hA with h | h
      · exact ⟨_, h, .inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, h, .inr ⟨rfl, rfl⟩⟩
  · rw [dite_eq_right (fun h => hu h.2)]
    simp only [decide_eq_false_iff_not]
    rintro ⟨e, -, (⟨-, h2⟩ | ⟨-, h2⟩)⟩
    · exact hu (h2 ▸ e.2.isLt)
    · exact hu (h2 ▸ e.1.isLt)

/-- The numbers the edge loop reads for the first `k` edges. -/
def edgeIns {n : Nat} (es : List (Fin n × Fin n)) (k : Nat) : List Int :=
  (es.take k).flatMap fun e => [(e.1.val : Int), (e.2.val : Int)]

theorem wp_edges {Q : Post} {e : env} {le : temp_env} {m : mem} {bg : block} {Mw N : Nat}
    (es : List (Fin N × Fin N)) (hne : es.length < 2147483648)
    (hMN : Mw * N < 2147483648) (hNM : N ≤ 64 * Mw)
    (harr : ArrayAt m .Mint64 bg 0 (longs (edgeWords Mw es 0)) (Mw * N))
    (hg : PTree.get dense.id.g le = some (.Vptr bg Ptrofs.zero))
    (hm : PTree.get dense.id.m le = some (.Vint (ir Mw)))
    (hnev : PTree.get dense.id.ne le = some (.Vint (ir es.length)))
    (hbit : Set.BitTable m Block.denseMainBit) (he : PTree.get dense.id.«dense_main:bit» e = none)
    (heg : PTree.get dense.id.g e = none) (her : PTree.get dense.id.nv_read e = none)
    (hbb : bg ≠ Block.denseMainBit)
    (hQ : ∀ t le' m', Reads t (edgeIns es es.length) →
      ArrayAt m' .Mint64 bg 0 (longs (edgeWords Mw es es.length)) (Mw * N) → Unch m m' (· = bg) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.i → x ≠ dense.id.a → x ≠ dense.id.b → x ≠ idOf 713 → x ≠ idOf 714 →
        PTree.get x le' = PTree.get x le) →
      Q.normal t e le' m') :
    Wp Statement.xi ge dense.fn.main (forT dense.id.i (tv dense.id.ne) edgeBody) Q e le m := by
  let Oth := fun le' : temp_env => ∀ x, x ≠ dense.id.i → x ≠ dense.id.a → x ≠ dense.id.b →
    x ≠ idOf 713 → x ≠ idOf 714 → PTree.get x le' = PTree.get x le
  let Inv := fun (k : Nat) (t : trace) (le' : temp_env) (m' : mem) =>
    k ≤ es.length ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧ Reads t (edgeIns es k) ∧
    ArrayAt m' .Mint64 bg 0 (longs (edgeWords Mw es k)) (Mw * N) ∧ Unch m m' (· = bg) ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧ Oth le'
  refine wp_forT (Inv := Inv) dense.id.i (tv dense.id.ne) edgeBody es.length hne ?_ ?_ ?_ ?_
  · rintro k t le' m' ⟨hk, hi, -, -, -, -, ho⟩
    refine ⟨hk, hi, ?_, rfl⟩
    show PTree.get _ _ = _
    rw [ho _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hnev
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, by
      show Reads E0 _
      simp only [edgeIns, List.take_zero, List.flatMap_nil]; exact Reads.nil, harr, Unch.refl _ _,
      fun _ h => h, fun x h1 _ _ _ _ => temps_gso _ _ h1⟩
  · rintro k t le' m' hk ⟨-, hi, hr, ha, hu, hgr, ho⟩
    have hg' : PTree.get dense.id.g le' = some (.Vptr bg Ptrofs.zero) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg
    have hm' : PTree.get dense.id.m le' = some (.Vint (ir Mw)) := by
      rw [ho _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm
    let A := es[k].1.val
    let B := es[k].2.val
    have hA : A < N := es[k].1.isLt
    have hB : B < N := es[k].2.isLt
    have hN : N ≤ Mw * N := Nat.le_mul_of_pos_left _ (by omega)
    wp_step; wp_step; wp_step; wp_step
    refine wp_rd (idOf 713) (lr (A : Int)) her ?_
    dsimp only
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    rw [Refine.repr_unsigned_lr (by omega)]
    wp_step; wp_step; wp_step; wp_step
    refine wp_rd (idOf 714) (lr (B : Int)) her ?_
    dsimp only
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    rw [Refine.repr_unsigned_lr (by omega)]
    have hbit' := hbit.unch hu (Ne.symm hbb)
    wp_step
    refine wp_addEdgeS (X := A) (Y := B) dense.id.a dense.id.b ha hMN hA (by omega) (by omega)
      (by simp (config := {decide := true}) only [temps_gso]; exact hg')
      (by simp (config := {decide := true}) only [temps_gso]; exact hm')
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [temps_gso, temps_gss]) hbit' he heg ?_
    intro m1 ha1 hu1 hg1
    refine wp_addEdgeS (X := B) (Y := A) dense.id.b dense.id.a ha1 hMN hB (by omega) (by omega)
      (by simp (config := {decide := true}) only [temps_gso]; exact hg')
      (by simp (config := {decide := true}) only [temps_gso]; exact hm')
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (hbit'.unch hu1 (Ne.symm hbb)) he heg ?_
    intro m2 ha2 hu2 hg2
    have hrAB : Reads (tr1 (readEv (lr (A : Int))) ++ (tr1 (readEv (lr (B : Int))) ++ E0 ++ (E0 ++ E0)))
        [(A : Int), (B : Int)] := by
      have := Reads.cons (lr (A : Int)) (Reads.cons (lr (B : Int)) Reads.nil)
      rwa [signed_lr (by omega) (by omega), signed_lr (by omega) (by omega)] at this
    refine ⟨by simp (config := {decide := true}) only [temps_gso]; exact hi, by omega, temps_gss _ _ _,
      ?_, ?_, hu.trans (hu1.trans hu2), fun z hz => hg2 _ (hg1 _ (hgr _ hz)), ?_⟩
    · have h := hr.append hrAB
      have he : edgeIns es (k + 1) = edgeIns es k ++ [(A : Int), (B : Int)] := by
        simp only [edgeIns, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rfl
      rw [he]; exact h
    · have hw : edgeWords Mw es (k + 1) = setEdge Mw (setEdge Mw (edgeWords Mw es k) A B) B A := by
        simp only [edgeWords, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      rw [hw]; exact ha2
    · intro x h1 h2 h3 h4 h5
      rw [temps_gso _ _ h1, temps_gso _ _ h3, temps_gso _ _ h5, temps_gso _ _ h2, temps_gso _ _ h4,
        ho x h1 h2 h3 h4 h5]
  · rintro t le' m' ⟨-, -, hr, ha, hu, hgr, ho⟩
    exact hQ t le' m' hr ha hu hgr ho

end NautyVerified.Proofs.Harness

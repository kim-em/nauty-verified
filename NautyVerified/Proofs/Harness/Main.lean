import NautyVerified.Proofs.Harness.Phases
import NautyVerified.Statement.Dense

/-!
# `dense_main`'s `main`, relative to `densenautySpec`

`main_satisfies`: from the program's initial memory, reading the numbers
`ins` that encode `G` (`Statement.Encodes`: each edge once, in one
orientation, so the edge count fits in an `int`), `main` returns 0 with a trace whose reads
are `ins` and whose writes are `Statement.expected G`, given that
`densenauty` satisfies `densenautySpec` for the generators `gens` whose
words are `expected`'s first block, and the facts `ResultFacts G` about
HexGraphIso's result (sizes, and entries that fit in an `int`).
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk longs)
open NautyVerified.Proofs.Search (Writes gensWords)
open NautyVerified.Proofs.Alloc (Fresh zb)
open Hex.GraphIso Hex.GraphIso.Nauty


/-- The pairs `(u, v)` with `u < v < n`. -/
def pairsBelow : Nat → List (Nat × Nat)
  | 0 => []
  | v + 1 => pairsBelow v ++ (List.range v).map (fun u => (u, v))

theorem length_pairsBelow : ∀ n, 2 * (pairsBelow n).length = n * (n - 1)
  | 0 => rfl
  | v + 1 => by
    simp only [pairsBelow, List.length_append, List.length_map, List.length_range]
    have := length_pairsBelow v
    rw [Nat.mul_add, this]
    cases v with
    | zero => rfl
    | succ w =>
      simp only [Nat.add_sub_cancel] at this ⊢
      have e1 : (w + 1 + 1) * (w + 1) = (w + 1) * (w + 1) + (w + 1) := Nat.succ_mul _ _
      have e2 : (w + 1) * (w + 1) = (w + 1) * w + (w + 1) := Nat.mul_succ _ _
      omega

theorem mem_pairsBelow {u v : Nat} : ∀ n, u < v → v < n → (u, v) ∈ pairsBelow n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | w + 1, h1, h2 => by
    simp only [pairsBelow, List.mem_append, List.mem_map, List.mem_range]
    by_cases hv : v = w
    · subst hv; exact .inr ⟨u, h1, rfl⟩
    · exact .inl (mem_pairsBelow w h1 (by omega))

/-- An edge as the pair of its endpoints in increasing order. -/
def normPair {n : Nat} (e : Fin n × Fin n) : Nat × Nat :=
  (min e.1.val e.2.val, max e.1.val e.2.val)

/-- An edge list without repeats, reversals or loops has at most `n (n - 1) / 2`
entries. -/
theorem length_edges_le {n : Nat} (es : List (Fin n × Fin n)) (hnd : es.Nodup)
    (hloop : ∀ e ∈ es, e.1 ≠ e.2) (hrev : ∀ u v, (u, v) ∈ es → (v, u) ∉ es) :
    2 * es.length ≤ n * (n - 1) := by
  have hnd' : (es.map normPair).Nodup := by
    unfold List.Nodup at hnd ⊢
    rw [List.pairwise_map]
    refine hnd.imp_of_mem fun {a b} ha hb hab h => ?_
    simp only [normPair, Prod.mk.injEq] at h
    have la := hloop a ha; have lb := hloop b hb
    have ha1 : a.1.val ≠ a.2.val := fun h => la (Fin.ext h)
    have key : (a.1.val = b.1.val ∧ a.2.val = b.2.val) ∨ (a.1.val = b.2.val ∧ a.2.val = b.1.val) := by
      omega
    rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact hab (Prod.ext (Fin.ext k1) (Fin.ext k2))
    · apply hrev a.1 a.2 ha
      have : (a.2, a.1) = b := Prod.ext (Fin.ext k2) (Fin.ext k1)
      rw [this]; exact hb
  have hsub : es.map normPair ⊆ pairsBelow n := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
    have h1 : e.1.val ≠ e.2.val := fun h => hloop e he (Fin.ext h)
    exact mem_pairsBelow n (by omega) (by have := e.1.isLt; have := e.2.isLt; omega)
  have := hnd'.length_le_of_subset hsub
  rw [List.length_map] at this
  have := length_pairsBelow n
  omega

/-- The edge count of an encoding fits in an `int`. -/
theorem length_edges_lt {n : Nat} (es : List (Fin n × Fin n)) (hnd : es.Nodup)
    (hloop : ∀ e ∈ es, e.1 ≠ e.2) (hrev : ∀ u v, (u, v) ∈ es → (v, u) ∉ es)
    (hmax : n ≤ 65536) : es.length < 2147483648 := by
  have h := length_edges_le es hnd hloop hrev
  have : n * (n - 1) ≤ 65536 * 65535 := Nat.mul_le_mul hmax (by omega)
  omega

/-- Every event of `t` is a call of `nv_read` or `nv_write` (so `t` has no
volatile loads). -/
def IOOnly (t : trace) : Prop :=
  ∀ ev ∈ (show List event from t), ∃ name args res, ev = .Event_syscall name args res

/-- `main` from the initial memory. -/
def mainSpec {n k : Nat} (G : Colored n k) (ins : List Int) : FunSpec where
  pre args m := args = [] ∧ Genv.init_mem Init.prog = some m
  post _ _ t v _ := v = .Vint (ir 0) ∧ Statement.reads t = ins.map some ∧
    Statement.writes t = Statement.expected G ∧ Statement.VloadsZero t

theorem Reads.ioOnly {t : trace} {l : List Int} (h : Reads t l) : IOOnly t := by
  induction h with
  | nil => intro ev hev; exact absurd hev (by simp)
  | cons x _ ih =>
    intro ev hev
    rcases List.mem_cons.1 hev with rfl | h
    · exact ⟨_, _, _, rfl⟩
    · exact ih ev h

theorem Writes.ioOnly {t : trace} {l : List Int} (h : Writes t l) : IOOnly t := by
  induction h with
  | nil => intro ev hev; exact absurd hev (by simp)
  | cons x r _ ih =>
    intro ev hev
    rcases List.mem_cons.1 hev with rfl | h
    · exact ⟨_, _, _, rfl⟩
    · exact ih ev h

theorem IOOnly.append {t s : trace} (ht : IOOnly t) (hs : IOOnly s) : IOOnly (t ++ s) := by
  intro ev hev
  rcases List.mem_append.1 hev with h | h
  · exact ht ev h
  · exact hs ev h

/-- `t = nauty_zalloc(a); x = t;` -/
theorem wp_zaSet {Q : Post} {e : env} {le : temp_env} {m : mem} (t x : ident) {a : expr}
    {s : statement} {sz : Nat}
    (he : PTree.get dense.id.nauty_zalloc e = none)
    (ha : Exec.evalExprlist ge e le m [a] [tulong] = some [.Vlong (lr sz)]) (hsz : sz < 2 ^ 62)
    (hQ : ∀ b m', Fresh m m' b sz →
      Mem.loadbytes m' b (zOfInt 0) (zOfInt sz) = some (List.replicate sz zb) →
      Wp Statement.xi ge dense.fn.main s Q e
        (PTree.set x (.Vptr b Ptrofs.zero) (PTree.set t (.Vptr b Ptrofs.zero) le)) m') :
    Wp Statement.xi ge dense.fn.main
      (.Ssequence (.Ssequence (sk (za t a)) (.Sset x (.Etempvar t (tptr .Tvoid)))) s) Q e le m := by
  apply wp_seq; apply wp_seq; apply wp_seq; apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  refine wp_za t he ha hsz fun b m' hfr hz => ?_
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss]
  simp only [E0_append]
  exact hQ b m' hfr hz

/-- `(size_t)n * sizeof(int)`. -/
theorem eval_size4 {e : env} {le : temp_env} {m : mem} {N : Nat} (hN : N < 2147483648)
    (hn : PTree.get dense.id.n le = some (.Vint (ir N))) :
    Exec.evalExprlist ge e le m
      [.Ebinop .Omul (.Ecast (tv dense.id.n) tulong) (.Esizeof tint tulong) tulong] [tulong] =
      some [.Vlong (lr ((N * 4 : Nat) : Int))] := by
  have h4 : Vptrofs (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tint)) =
      .Vlong (lr ((4 : Nat) : Int)) := by
    rw [show Cfrontend.Ctypes.sizeof ge.genv_cenv tint = zOfInt (4 : Nat) from rfl, Alloc.vptrofs_lr]
  simp only [Exec.evalExprlist, Exec.evalExpr, hn, typeof, cop, h4]
  simp only [cop, cast_int_long_ir (a := N) ⟨by omega, by omega⟩]
  have := Alloc.lr_mul N 4
  push_cast at this
  simpa using this

/-- `(size_t)m * (size_t)n * sizeof(graph)`. -/
theorem eval_size8 {e : env} {le : temp_env} {m : mem} {Mw N : Nat} (hN : N < 2147483648)
    (hM : Mw < 2147483648)
    (hn : PTree.get dense.id.n le = some (.Vint (ir N)))
    (hm : PTree.get dense.id.m le = some (.Vint (ir Mw))) :
    Exec.evalExprlist ge e le m
      [.Ebinop .Omul (.Ebinop .Omul (.Ecast (tv dense.id.m) tulong) (.Ecast (tv dense.id.n) tulong) tulong)
        (.Esizeof tulong tulong) tulong] [tulong] =
      some [.Vlong (lr ((Mw * N * 8 : Nat) : Int))] := by
  have h8 : Vptrofs (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) =
      .Vlong (lr ((8 : Nat) : Int)) := by
    rw [show Cfrontend.Ctypes.sizeof ge.genv_cenv tulong = zOfInt (8 : Nat) from rfl, Alloc.vptrofs_lr]
  simp only [Exec.evalExprlist, Exec.evalExpr, hn, hm, typeof, cop, h8]
  simp only [cop, cast_int_long_ir (a := N) ⟨by omega, by omega⟩,
    cast_int_long_ir (a := Mw) ⟨by omega, by omega⟩]
  have h1 := Alloc.lr_mul Mw N
  have h2 := Alloc.lr_mul (Mw * N) 8
  push_cast at h1 h2
  rw [h1]; simpa using h2

/-- The frame since the initial memory: only fresh blocks changed, and
valid blocks stay valid. -/
abbrev Since (m₀ m : mem) : Prop :=
  Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z) ∧ ∀ z, Mem.valid_block m₀ z → Mem.valid_block m z

theorem Since.fresh {m₀ m m' : mem} {b : block} {sz : Nat} (h : Since m₀ m) (hfr : Fresh m m' b sz) :
    Since m₀ m' ∧ ¬ Mem.valid_block m₀ b :=
  have hb : ¬ Mem.valid_block m₀ b := fun hv => hfr.new (h.2 _ hv)
  ⟨⟨h.1.trans (hfr.unch.mono fun _ hz => hz ▸ hb), fun _ hz => hfr.grow _ (h.2 _ hz)⟩, hb⟩

theorem _root_.NautyVerified.Proofs.Alloc.Fresh.valid {m m' : mem} {b : block} {sz : Nat} (hfr : Fresh m m' b sz) (h0 : 0 < sz) :
    Mem.valid_block m' b :=
  Mem.perm_valid_block m' b (zOfInt 0) .Cur .Freeable (hfr.perm 0 (by omega) (by omega))

theorem _root_.NautyVerified.Proofs.Alloc.Fresh.ne {m m' : mem} {b z : block} {sz : Nat} (hfr : Fresh m m' b sz)
    (hz : Mem.valid_block m z) : z ≠ b := fun h => hfr.new (h ▸ hz)

theorem _root_.NautyVerified.Proofs.Alloc.Fresh.ints {m m' : mem} {b : block} {N : Nat} (hfr : Fresh m m' b (N * 4))
    (hz : Mem.loadbytes m' b (zOfInt 0) (zOfInt (N * 4 : Nat)) = some (List.replicate (N * 4) zb))
    (hN : N * 4 < 2 ^ 62) : ArrayAt m' .Mint32 b 0 (fun _ => .Vint (ir 0)) N :=
  Alloc.zero_ints hz (fun ofs h0 h1 => hfr.perm ofs (by omega) h1) hN N (by omega)

theorem _root_.NautyVerified.Proofs.Alloc.Fresh.longs {m m' : mem} {b : block} {N : Nat} (hfr : Fresh m m' b (N * 8))
    (hz : Mem.loadbytes m' b (zOfInt 0) (zOfInt (N * 8 : Nat)) = some (List.replicate (N * 8) zb))
    (hN : N * 8 < 2 ^ 62) : ArrayAt m' .Mint64 b 0 (fun _ => .Vlong (lr 0)) N :=
  Alloc.zero_longs hz (fun ofs h0 h1 => hfr.perm ofs (by omega) h1) hN N (by omega)

/-- `expected`'s first block: the words of HexGraphIso's generators. -/
def autosWords {n k : Nat} (G : Colored n k) : List Int :=
  (runColoredTraced G).autos.toList.flatMap (fun p => 1 :: p.toList.map (fun (i : Nat) => (i : Int)))

theorem expected_eq {n k : Nat} (G : Colored n k) :
    Statement.expected G = autosWords G ++ outWords G := by
  simp only [Statement.expected, autosWords, outWords, List.append_assoc]

set_option maxRecDepth 100000 in
theorem main_satisfies {n k : Nat} (G : Colored n k) (gens : List (Array Nat)) (ins : List Int)
    (hins : Statement.Encodes G ins) (hn0 : 0 < n) (hmax : n ≤ Statement.maxN)
    (hkmax : k ≤ Statement.maxN)
    (hfacts : ResultFacts G) (hgens : gensWords gens n = autosWords G)
    (hdn : ∀ bg bl bp bo bst bc, Satisfies Statement.xi ge (.Internal dense.fn.densenauty)
      (densenautySpec G gens bg bl bp bo bst bc)) :
    Satisfies Statement.xi ge (.Internal dense.fn.main) (mainSpec G ins) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m => ∃ bst, e = envOf bst ∧
    le = create_undef_temps dense.fn.main.fn_temps ∧ Genv.init_mem Init.prog = some m₀ ∧
    Since m₀ m ∧ ¬ Mem.valid_block m₀ bst ∧ Mem.valid_block m bst ∧
    Mem.range_perm m bst (zOfInt 0) (zOfInt 88) .Cur .Freeable) ?_ ?_
  · rintro args m ⟨rfl, hm⟩
    have hsz : Cfrontend.Ctypes.sizeof ge.genv_cenv (Cfrontend.Ctypes.Tstruct dense.id.«_1024» Cfrontend.Ctypes.noattr) =
        zOfInt 88 := rfl
    have hal : Mem.alloc m (zOfInt 0) (zOfInt 88) =
        ((Mem.alloc m (zOfInt 0) (zOfInt 88)).1, (Mem.alloc m (zOfInt 0) (zOfInt 88)).2) := rfl
    generalize (Mem.alloc m (zOfInt 0) (zOfInt 88)).1 = m1 at hal
    generalize (Mem.alloc m (zOfInt 0) (zOfInt 88)).2 = b at hal
    have hfresh : ¬ Mem.valid_block m b := Mem.fresh_block_alloc _ _ _ _ _ hal
    refine ⟨envOf b, _, m1, ⟨?_, ?_, ?_, .cons _ _ _ _ _ _ _ _ _ hal (.nil _ _), rfl⟩,
      b, rfl, rfl, hm, ⟨(Alloc.Unch.alloc hal).mono fun z hz => hz ▸ hfresh,
        fun z hz => Mem.valid_block_alloc _ _ _ _ _ hal _ hz⟩, hfresh,
      Mem.valid_new_block _ _ _ _ _ hal, fun o ho => Mem.perm_alloc_2 _ _ _ _ _ hal o .Cur ho⟩
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact .nil _
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hm⟩
    rw [triple_iff_wp]
    rintro e le m ⟨bst, rfl, rfl, hm₀, hS, hnb, hvb, hfree⟩
    rw [dense.fn.main.fn_body_eq, body_eq]
    obtain ⟨es, rfl, hnd, hrev, hloop, hadj⟩ := hins
    have hmax : n ≤ 65536 := hmax
    have hk : k < 2147483648 := by have : k ≤ 65536 := hkmax; omega
    have hne := length_edges_lt es hnd hloop hrev hmax
    have hN : n < 2147483648 := by omega
    have hE : ∀ x, x ≠ dense.id.stats → PTree.get x (envOf bst) = none := fun x hx => by
      rw [PTree.gso _ _ hx]; rfl
    apply wp_seq; apply wp_seq; apply wp_seq; apply wp_seq; apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    refine wp_rd (idOf 703) (lr (n : Int)) (hE _ (by decide)) ?_
    apply wp_set_eval
    rw [show Exec.evalExpr ge (envOf bst) (PTree.set (idOf 703) (.Vlong (lr (n : Int)))
        (create_undef_temps dense.fn.main.fn_temps)) m
        (.Ecast (.Etempvar (idOf 703) tlong) tint) = some (.Vint (ir (n : Int))) by
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      rw [Refine.repr_unsigned_lr hN]]
    apply wp_seq; apply wp_seq; apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl,
      ir_lt (a := 0) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    rw [ite_eq_right (by simp; omega)]
    apply wp_skip
    simp only [E0_append]
    let le0 := PTree.set dense.id.n (.Vint (ir (n : Int))) (PTree.set (idOf 703) (.Vlong (lr (n : Int)))
      (create_undef_temps dense.fn.main.fn_temps))
    have hn : PTree.get dense.id.n le0 = some (.Vint (ir (n : Int))) := temps_gss _ _ _
    apply wp_seq; apply wp_seq; apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    apply wp_set_eval
    rw [show Exec.evalExpr ge (envOf bst) le0 m
      (.Ebinop .Oadd (.Ebinop .Oshr (.Ebinop .Osub (tv dense.id.n) (ci 1 tint) tint) (ci 6 tint) tint)
        (ci 1 tint) tint) = some (.Vint (ir (wordsOf n : Int))) by
      simp only [Exec.evalExpr, hn, typeof, cop]
      rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl,
        show Lib.Integers.Int.repr (zOfInt 6) = ir 6 from rfl,
        show Int.ltu (ir 6) Int.iwordsize = true from rfl, ite_eq_left (rfl : true = true), ir_sub,
        ir_shr6 ⟨by omega, by omega⟩]
      simp only [cop, ir_add]
      congr 3
      simp only [wordsOf, Statement.setwordsNeeded]
      omega]
    simp only [E0_append]
    have hMw : wordsOf n < 2147483648 := by simp only [wordsOf, Statement.setwordsNeeded]; omega
    have hMN := wordsOf_mul hmax
    have hza : PTree.get dense.id.nauty_zalloc (envOf bst) = none := hE _ (by decide)
    have h4 : n * 4 < 2 ^ 62 := by omega
    have h8 : wordsOf n * n * 8 < 2 ^ 62 := by omega
    have hp4 : 0 < n * 4 := by omega
    have hM0 : 0 < wordsOf n := by simp only [wordsOf, Statement.setwordsNeeded]; omega
    have hp8 : 0 < wordsOf n * n * 8 := Nat.mul_pos (Nat.mul_pos hM0 hn0) (by decide)
    refine wp_zaSet (idOf 704) dense.id.colour hza
      (eval_size4 hN (by rw [temps_gso _ _ (by decide)]; exact hn)) h4 fun b1 m1 f1 z1 => ?_
    refine wp_zaSet (idOf 705) dense.id.lab hza
      (eval_size4 hN (by simp (config := {decide := true}) only [temps_gso]; exact hn)) h4
      fun b2 m2 f2 z2 => ?_
    refine wp_zaSet (idOf 706) dense.id.ptn hza
      (eval_size4 hN (by simp (config := {decide := true}) only [temps_gso]; exact hn)) h4
      fun b3 m3 f3 z3 => ?_
    refine wp_zaSet (idOf 707) dense.id.orbits hza
      (eval_size4 hN (by simp (config := {decide := true}) only [temps_gso]; exact hn)) h4
      fun b4 m4 f4 z4 => ?_
    refine wp_zaSet (idOf 708) dense.id.g hza
      (eval_size8 hN hMw (by simp (config := {decide := true}) only [temps_gso]; exact hn)
        (by simp (config := {decide := true}) only [temps_gso, temps_gss])) h8
      fun b5 m5 f5 z5 => ?_
    refine wp_zaSet (idOf 709) dense.id.canong hza
      (eval_size8 hN hMw (by simp (config := {decide := true}) only [temps_gso]; exact hn)
        (by simp (config := {decide := true}) only [temps_gso, temps_gss])) h8
      fun b6 m6 f6 z6 => ?_
    obtain ⟨S1, n1⟩ := hS.fresh f1
    obtain ⟨S2, n2⟩ := S1.fresh f2
    obtain ⟨S3, n3⟩ := S2.fresh f3
    obtain ⟨S4, n4⟩ := S3.fresh f4
    obtain ⟨S5, n5⟩ := S4.fresh f5
    obtain ⟨S6, n6⟩ := S5.fresh f6
    have v1 := f1.valid hp4
    have v2 := f2.valid hp4
    have v3 := f3.valid hp4
    have v4 := f4.valid hp4
    have v5 := f5.valid hp8
    have v6 := f6.valid hp8
    have g2 := f2.grow
    have g3 := f3.grow
    have g4 := f4.grow
    have g5 := f5.grow
    have g6 := f6.grow
    have vs0 := f1.grow _ hvb
    have d01 := f1.ne hvb
    have d02 := f2.ne vs0
    have d03 := f3.ne (g2 _ vs0)
    have d04 := f4.ne (g3 _ (g2 _ vs0))
    have d05 := f5.ne (g4 _ (g3 _ (g2 _ vs0)))
    have d06 := f6.ne (g5 _ (g4 _ (g3 _ (g2 _ vs0))))
    have d12 := f2.ne v1
    have d13 := f3.ne (g2 _ v1)
    have d14 := f4.ne (g3 _ (g2 _ v1))
    have d15 := f5.ne (g4 _ (g3 _ (g2 _ v1)))
    have d16 := f6.ne (g5 _ (g4 _ (g3 _ (g2 _ v1))))
    have d23 := f3.ne v2
    have d24 := f4.ne (g3 _ v2)
    have d25 := f5.ne (g4 _ (g3 _ v2))
    have d26 := f6.ne (g5 _ (g4 _ (g3 _ v2)))
    have d34 := f4.ne v3
    have d35 := f5.ne (g4 _ v3)
    have d36 := f6.ne (g5 _ (g4 _ v3))
    have d45 := f5.ne v4
    have d46 := f6.ne (g5 _ v4)
    have d56 := f6.ne v5
    have a1 := ((((f1.ints z1 h4).unch f2.unch d12).unch f3.unch d13).unch f4.unch d14).unch f5.unch d15
      |>.unch f6.unch d16
    have a2 := (((f2.ints z2 h4).unch f3.unch d23).unch f4.unch d24).unch f5.unch d25
      |>.unch f6.unch d26
    have a3 := ((f3.ints z3 h4).unch f4.unch d34).unch f5.unch d35 |>.unch f6.unch d36
    have a4 := ((f4.ints z4 h4).unch f5.unch d45).unch f6.unch d46
    have a5 := (f5.longs (N := wordsOf n * n) z5 h8).unch f6.unch d56
    have a6 := f6.longs (N := wordsOf n * n) z6 h8
    have hfree6 := Unch.range_perm f6.unch d06 <| Unch.range_perm f5.unch d05 <|
      Unch.range_perm f4.unch d04 <| Unch.range_perm f3.unch d03 <| Unch.range_perm f2.unch d02 <|
      Unch.range_perm f1.unch d01 hfree
    refine wp_phases G gens es hne hadj hn0 hmax hk hfacts (hdn _ _ _ _ _ _) hm₀ S6.1 S6.2 ?_ ?_ hfree6
      (by simp (config := {decide := true}) only [temps_gso]; exact hn)
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [temps_gso, temps_gss])
      (by simp (config := {decide := true}) only [temps_gss])
      a1 a2 a3 a4 a5 a6 ?_
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨hnb, g6 _ (g5 _ (g4 _ (g3 _ (g2 _ vs0))))⟩, ⟨n1, g6 _ (g5 _ (g4 _ (g3 _ (g2 _ v1))))⟩,
        ⟨n2, g6 _ (g5 _ (g4 _ (g3 _ v2)))⟩, ⟨n3, g6 _ (g5 _ (g4 _ v3))⟩, ⟨n4, g6 _ (g5 _ v4)⟩,
        ⟨n5, g6 _ v5⟩, ⟨n6, v6⟩⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      exact ⟨⟨d01, d02, d03, d04, d05, d06⟩, ⟨d12, d13, d14, d15, d16⟩, ⟨d23, d24, d25, d26⟩,
        ⟨d34, d35, d36⟩, ⟨d45, d46⟩, d56, fun _ h => h.elim⟩
    · intro t1 t2 m' hr hw
      show (mainSpec G _).post [] m₀ (tr1 (readEv (lr (n : Int))) ++ E0 ++ (t1 ++ t2)) _ m'
      have hrd : Reads (tr1 (readEv (lr (n : Int)))) [(n : Int)] := by
        have := Reads.one (lr (n : Int))
        rwa [signed_lr (by omega) (by omega)] at this
      have hR := hrd.append hr
      have eT : tr1 (readEv (lr (n : Int))) ++ E0 ++ (t1 ++ t2) =
          (tr1 (readEv (lr (n : Int))) ++ t1) ++ (t2 ++ E0) := by
        rw [append_E0, append_E0, trace_append_assoc]
      obtain ⟨hw1, hw2, hw3⟩ := hw
      refine ⟨rfl, ?_, ?_, ?_⟩
      · rw [eT, hR.reads, append_E0, hw2]
        show _ ++ ([] : List (Option Int)) = _
        simp [colours, edgeIns, List.map_map, Function.comp_def]
      · rw [eT, hR.writes, append_E0, hw1, hgens, expected_eq]
      · rw [eT, append_E0]
        intro c i o ev hm
        rcases List.mem_append.1 hm with hm | hm
        · obtain ⟨_, _, _, h⟩ := (hrd.ioOnly.append hr.ioOnly) _ hm
          cases h
        · exact hw3 c i o ev hm

end NautyVerified.Proofs.Harness

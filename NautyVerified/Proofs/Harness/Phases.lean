import NautyVerified.Proofs.Harness.InputMain
import NautyVerified.Proofs.Init.Tables

/-!
# `main` after its allocations

`wp_phases`: once `main` has allocated `stats` and its six arrays (all fresh
since the initial memory, zero-filled), the input, partition, option and
`densenauty` phases and the output read the rest of the input and write
`gensWords gens n ++ outWords G`, given `densenautySpec` for the call.
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
open Hex.GraphIso Hex.GraphIso.Nauty

theorem Unch.range_perm {m m' : mem} {S : block → Prop} {b : block} {lo hi : Z} (hu : Unch m m' S)
    (hb : ¬ S b) (h : Mem.range_perm m b lo hi .Cur .Freeable) :
    Mem.range_perm m' b lo hi .Cur .Freeable := by
  intro ofs ⟨hl, hh⟩
  change intOfZ _ ≤ intOfZ _ at hl
  change intOfZ _ < intOfZ _ at hh
  have h1 : intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 := rfl
  have hva : Mem.valid_access m .Mint8unsigned b ofs .Freeable := by
    refine ⟨fun o ⟨ho1, ho2⟩ => h o ⟨?_, ?_⟩, ZArith.BinInt.Z.divide_1_l ofs⟩
    · change intOfZ _ ≤ intOfZ _ at ho1 ⊢; omega
    · change intOfZ _ < intOfZ (ZArith.BinInt.Z.add _ _) at ho2
      change intOfZ _ < intOfZ _
      simp only [intOfZ_add, h1] at ho2; omega
  refine (hu.access _ _ _ _ hb hva).1 ofs ⟨?_, ?_⟩
  · change intOfZ _ ≤ intOfZ _; omega
  · change intOfZ _ < intOfZ (ZArith.BinInt.Z.add _ _); simp only [intOfZ_add, h1]; omega

theorem valid_of_access {m : mem} {c : memory_chunk} {b : block} {ofs : Z} {p : Common.Memtype.permission}
    (h : Mem.valid_access m c b ofs p) : Mem.valid_block m b := by
  have : 0 < intOfZ (Common.Memdata.size_chunk c) := csize_pos c
  refine Mem.perm_valid_block m b ofs .Cur p (h.1 ofs ⟨?_, ?_⟩)
  · change intOfZ _ ≤ intOfZ _; omega
  · change intOfZ _ < intOfZ (ZArith.BinInt.Z.add _ _); simp only [intOfZ_add]; omega

theorem wordsOf_mul {n : Nat} (h : n ≤ 65536) : wordsOf n * n < 2147483648 := by
  have : wordsOf n ≤ 1024 := by simp only [wordsOf, Statement.setwordsNeeded]; omega
  have := Nat.mul_le_mul this h
  omega

/-- The blocks `main` allocates: fresh since `m₀`, valid in `m`. -/
abbrev NewIn (m₀ m : mem) (b : block) : Prop := ¬ Mem.valid_block m₀ b ∧ Mem.valid_block m b

set_option maxRecDepth 100000 in
theorem wp_phases {n k : Nat} (G : Colored n k) (gens : List (Array Nat))
    (es : List (Fin n × Fin n)) (hne : es.length < 2147483648)
    (hadj : ∀ u v : Fin n, G.graph.adj u v = true ↔ ((u, v) ∈ es ∨ (v, u) ∈ es))
    (hn0 : 0 < n) (hmax : n ≤ 65536) (hk : k < 2147483648) (hfacts : ResultFacts G)
    {Q : Post} {le : temp_env} {m₀ m : mem} {bst bcol bl bp bo bg bc : block}
    (hdn : Satisfies Statement.xi ge (.Internal dense.fn.densenauty)
      (densenautySpec G gens bg bl bp bo bst bc))
    (hm₀ : Genv.init_mem Init.prog = some m₀)
    (hu : Unch m₀ m (fun z => ¬ Mem.valid_block m₀ z))
    (hgrow : ∀ z, Mem.valid_block m₀ z → Mem.valid_block m z)
    (hnew : ∀ z ∈ [bst, bcol, bl, bp, bo, bg, bc], NewIn m₀ m z)
    (hdist : [bst, bcol, bl, bp, bo, bg, bc].Pairwise (· ≠ ·))
    (hfree : Mem.range_perm m bst (zOfInt 0) (zOfInt 88) .Cur .Freeable)
    (hn : PTree.get dense.id.n le = some (.Vint (ir n)))
    (hm : PTree.get dense.id.m le = some (.Vint (ir (wordsOf n))))
    (hcol : PTree.get dense.id.colour le = some (.Vptr bcol Ptrofs.zero))
    (hlab : PTree.get dense.id.lab le = some (.Vptr bl Ptrofs.zero))
    (hptn : PTree.get dense.id.ptn le = some (.Vptr bp Ptrofs.zero))
    (horb : PTree.get dense.id.orbits le = some (.Vptr bo Ptrofs.zero))
    (hg : PTree.get dense.id.g le = some (.Vptr bg Ptrofs.zero))
    (hcg : PTree.get dense.id.canong le = some (.Vptr bc Ptrofs.zero))
    (hcz : ArrayAt m .Mint32 bcol 0 (fun _ => .Vint (ir 0)) n)
    (hlz : ArrayAt m .Mint32 bl 0 (fun _ => .Vint (ir 0)) n)
    (hpz : ArrayAt m .Mint32 bp 0 (fun _ => .Vint (ir 0)) n)
    (hoz : ArrayAt m .Mint32 bo 0 (fun _ => .Vint (ir 0)) n)
    (hgz : ArrayAt m .Mint64 bg 0 (fun _ => .Vlong (lr 0)) (wordsOf n * n))
    (hcgz : ArrayAt m .Mint64 bc 0 (fun _ => .Vlong (lr 0)) (wordsOf n * n))
    (hQ : ∀ t1 t2 m', Reads t1 ((colours G).map (fun c : Nat => (c : Int)) ++ [(es.length : Int)] ++
        edgeIns es es.length) →
      NautyVerified.Proofs.Search.Emits t2 (gensWords gens n ++ outWords G) →
      Q.ret (t1 ++ t2) (.Vint (ir 0)) m') :
    Wp Statement.xi ge dense.fn.main tInput Q (envOf bst) le m := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hnew
  obtain ⟨nst, ncol, nl, np, no, ng, nc⟩ := hnew
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at hdist
  obtain ⟨⟨d01, d02, d03, d04, d05, d06⟩, ⟨d12, d13, d14, d15, d16⟩, ⟨d23, d24, d25, d26⟩,
    ⟨d34, d35, d36⟩, ⟨d45, d46⟩, d56, -⟩ := hdist
  have hN : n < 2147483648 := by omega
  have hMN := wordsOf_mul hmax
  have hNM : n ≤ 64 * wordsOf n := by simp only [wordsOf, Statement.setwordsNeeded]; omega
  have hMw : wordsOf n < 2147483648 := by simp only [wordsOf, Statement.setwordsNeeded]; omega
  have hvo : Mem.valid_block m₀ Block.options := Init.valid_global hm₀ find_options
  have hvb : Mem.valid_block m₀ Block.denseMainBit := Init.valid_global hm₀ find_denseMainBit
  have hne₀ : ∀ {z}, NewIn m₀ m z → ∀ {y}, Mem.valid_block m₀ y → z ≠ y :=
    fun hz _ hy h => hz.1 (h ▸ hy)
  have hbit : Set.BitTable m Block.denseMainBit :=
    (Init.globals hm₀).denseMainBit.unch hu (fun h => h hvb)
  have hcs : ∀ j < n, (colours G)[j]! < 2147483648 := fun j hj => by
    have := keyOf_bound G hj; simp only [keyOf] at this; omega
  have her := envOf_read bst
  have heb : PTree.get dense.id.«dense_main:bit» (envOf bst) = none := by
    rw [PTree.gso _ _ (by decide)]; rfl
  have heg : PTree.get dense.id.g (envOf bst) = none := by
    rw [PTree.gso _ _ (by decide)]; rfl
  refine wp_tInput (colours G) (colours_length G) hcs es hne hn0 hN hMN hNM hMw her heb heg hcol hg
    hn hm hcz hgz hbit (hne₀ ng hvb) (hne₀ ncol hvb) d15 fun t1 le1 m1 hr1 hca1 hga1 hu1 hg1 hmx1 ho1 => ?_
  have hle1 : ∀ x, InputTemp x → PTree.get x le1 = PTree.get x le := ho1
  have hu1' : ∀ {z}, z ≠ bcol → z ≠ bg → ¬ (z = bcol ∨ z = bg) := fun h1 h2 h => h.elim h1 h2
  refine wp_tPart G hn0 hN hk (by rw [hle1 _ (by decide)]; exact hcol)
    (by rw [hle1 _ (by decide)]; exact hlab) (by rw [hle1 _ (by decide)]; exact hptn)
    (by rw [hle1 _ (by decide)]; exact hn) hmx1 hca1 (hlz.unch hu1 (hu1' (Ne.symm d12) d25))
    (hpz.unch hu1 (hu1' (Ne.symm d13) d35)) d12.symm d13.symm d23
    fun le2 m2 hla2 hpa2 hu2 hg2 ho2 => ?_
  have hle2 : ∀ x, InputTemp x → x ≠ dense.id.c → x ≠ dense.id.j → x ≠ dense.id.pos → x ≠ idOf 715 →
      PTree.get x le2 = PTree.get x le := fun x hx h1 h2 h3 h4 => by
    rw [ho2 x h1 h2 h3 hx.1 h4, hle1 x hx]
  have hu01 : Unch m₀ m1 (fun z => ¬ Mem.valid_block m₀ z) :=
    hu.trans (hu1.mono fun z hz => hz.elim (fun h => h ▸ ncol.1) (fun h => h ▸ ng.1))
  have hu02 : Unch m₀ m2 (fun z => ¬ Mem.valid_block m₀ z) :=
    hu01.trans (hu2.mono fun z hz => hz.elim (fun h => h ▸ nl.1) (fun h => h ▸ np.1))
  refine wp_tOpts (optionsInit_of hm₀) hu02 hvo fun m3 hopt hu3 hg3 => ?_
  have hnot : ∀ {z}, NewIn m₀ m z → ¬ z = Block.options := fun hz h => hz.1 (h ▸ hvo)
  have hu13 : ∀ {z}, NewIn m₀ m z → z ≠ bcol → z ≠ bg → z ≠ bl → z ≠ bp →
      Unch m m3 (fun y => y = bcol ∨ y = bg ∨ y = bl ∨ y = bp ∨ y = Block.options) ∧
      ¬ (z = bcol ∨ z = bg ∨ z = bl ∨ z = bp ∨ z = Block.options) := fun hz h1 h2 h3 h4 =>
    ⟨(hu1.mono fun y hy => hy.elim .inl (fun h => .inr (.inl h))).trans
      ((hu2.mono fun y hy => hy.elim (fun h => .inr (.inr (.inl h))) (fun h => .inr (.inr (.inr (.inl h))))).trans
        (hu3.mono fun y hy => .inr (.inr (.inr (.inr hy))))),
     fun h => h.elim h1 fun h => h.elim h2 fun h => h.elim h3 fun h => h.elim h4 (hnot hz)⟩
  have hla3 := hla2.unch hu3 (hnot nl)
  have hpa3 := hpa2.unch hu3 (hnot np)
  have hga3 := (hga1.unch hu2 (fun h => h.elim (fun h => d25 h.symm) (fun h => d35 h.symm))).unch hu3 (hnot ng)
  obtain ⟨hU, hS⟩ := hu13 no (Ne.symm d14) d45 (Ne.symm d24) (Ne.symm d34)
  have hoa3 := hoz.unch hU hS
  obtain ⟨hU', hS'⟩ := hu13 nc (Ne.symm d16) (Ne.symm d56) (Ne.symm d26) (Ne.symm d36)
  have hca3 := hcgz.unch hU' hS'
  obtain ⟨hU'', hS''⟩ := hu13 nst d01 d05 d02 d03
  have hfree3 := Unch.range_perm hU'' hS'' hfree
  have hv : ∀ {b c} {base : Int} {vals : Nat → val} {N : Nat}, 0 < N → ArrayAt m3 c b base vals N →
      Mem.valid_block m3 b := fun hN h => valid_of_access (h.writable 0 hN)
  have hMN0 : 0 < wordsOf n * n := Nat.mul_pos (by simp only [wordsOf, Statement.setwordsNeeded]; omega) hn0
  have hz0 : intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 := rfl
  have hl3 : ∀ x, InputTemp x → x ≠ dense.id.c → x ≠ dense.id.j → x ≠ dense.id.pos → x ≠ idOf 715 →
      PTree.get x le2 = PTree.get x le := hle2
  refine wp_tCall G gens hdn hfacts hN hMN
    (by rw [hl3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hn)
    (by rw [hl3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm)
    (by rw [hl3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg)
    (by rw [hl3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlab)
    (by rw [hl3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hptn)
    (by rw [hl3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact horb)
    (by rw [hl3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcg)
    ⟨rfl, ⟨m₀, hm₀, hu02.mono (fun z hz => .inr hz) |>.trans (hu3.mono fun z hz => .inl hz),
      fun z hz => hg3 _ (hg2 _ (hg1 _ (hgrow _ hz))), ?_⟩,
      hopt, ⟨edgeWords (wordsOf n) es es.length, ⟨hz0 ▸ hga3, fun v hv => by
        rw [← edgeRow_rowsOf hadj hv]; exact setRep_edgeWords es hNM es.length v⟩⟩,
      hla3, hpa3, ⟨_, hoa3⟩, ⟨_, hca3⟩, hfree3, ?_, hn0, hmax⟩
    fun t2 m' hw => hQ t1 t2 m' hr1 hw
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨⟨ng.1, hv hMN0 hga3⟩, ⟨nl.1, hv hn0 hla3⟩, ⟨np.1, hv hn0 hpa3⟩, ⟨no.1, hv hn0 hoa3⟩,
      ⟨nst.1, ?_⟩, ⟨nc.1, hv hMN0 hca3⟩⟩
    exact Mem.perm_valid_block m3 bst (zOfInt 0) .Cur .Freeable (hfree3 (zOfInt 0) ⟨by
      change intOfZ _ ≤ intOfZ _; omega, by change intOfZ _ < intOfZ _; rw [intOfZ_zOfInt, intOfZ_zOfInt]; omega⟩)
  · simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨Ne.symm d25, Ne.symm d35, Ne.symm d45, Ne.symm d05, d56⟩, ⟨d23, d24, Ne.symm d02, d26⟩,
      ⟨d34, Ne.symm d03, d36⟩, ⟨Ne.symm d04, d46⟩, d06, fun _ h => h.elim⟩

end NautyVerified.Proofs.Harness

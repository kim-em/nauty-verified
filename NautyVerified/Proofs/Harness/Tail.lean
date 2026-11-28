import NautyVerified.Proofs.Harness.Output
import NautyVerified.Proofs.Harness.Words
import NautyVerified.Proofs.Harness.Spec

/-!
# After `densenauty`

`wp_tOut`: from what `densenautySpec` leaves in memory, the output loops and
the statistics write `outWords G`, the part of `Statement.expected G` after
the generators, and `main` returns 0.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk longs)
open NautyVerified.Proofs.Search (Writes FieldAt)
open Hex.GraphIso Hex.GraphIso.Nauty

/-- `main`'s environment: the local `stats` in block `bst`. -/
abbrev envOf (bst : block) : env := PTree.set dense.id.stats (bst, Tstruct dense.id.«_1024» noattr) empty_env

theorem envOf_write (bst : block) : PTree.get dense.id.nv_write (envOf bst) = none := by
  rw [PTree.gso _ _ (by decide)]; rfl

theorem envOf_read (bst : block) : PTree.get dense.id.nv_read (envOf bst) = none := by
  rw [PTree.gso _ _ (by decide)]; rfl

/-- What `main` writes after the generators. -/
def outWords {n k : Nat} (G : Colored n k) : List Int :=
  let r := runColoredTraced G
  (2 :: r.result.canonlab.toList.map (fun (i : Nat) => (i : Int))) ++
  (3 :: (Statement.finalState G).orbits.toList.map (fun (i : Nat) => (i : Int))) ++
  (4 :: r.result.canong.toList.flatMap (Statement.rowWords (Statement.setwordsNeeded n))) ++
  [5, Statement.asInt r.result.numorbits, Statement.asInt r.result.numgenerators,
    Statement.asLong r.result.numnodes, Statement.asLong r.result.numbadleaves,
    Statement.asInt r.result.maxlevel, Statement.asLong r.result.tctotal,
    Statement.asLong r.result.canupdates, 0]

/-- `List.range n` read off an array of size `n`. -/
theorem range_map_get {a : Array Nat} {n : Nat} (h : a.size = n) :
    (List.range n).map (fun j => ((a[j]! : Nat) : Int)) = a.toList.map (fun (i : Nat) => (i : Int)) := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  rw [getElem!_pos a i (by simp at h1; omega)]

theorem eval_ci (bst : block) (le : temp_env) (m : mem) (v : Nat) :
    Exec.evalExprlist ge (envOf bst) le m [ci v tint] [tlong] =
      some [.Vlong (Cfrontend.Cop.cast_int_long .Signed (ir v))] := rfl

theorem write_ci (v : Nat) (h : v < 2147483648) :
    intOfZ (Lib.Integers.Int64.signed (Cfrontend.Cop.cast_int_long .Signed (ir v))) = v := by
  rw [cast_int_long_ir ⟨by omega, by omega⟩, signed_lr (by omega) (by omega)]

set_option maxRecDepth 100000 in
/-- The output loops and the statistics. -/
theorem wp_tOut {n k : Nat} (G : Colored n k) {Q : Post} {le : temp_env} {m : mem}
    {bst bl bo bc : block} (hfacts : (runColoredTraced G).result.canonlab.size = n ∧
      (∀ i < n, (runColoredTraced G).result.canonlab[i]! < 2147483648) ∧
      (Statement.finalState G).orbits.size = n ∧
      (∀ i < n, (Statement.finalState G).orbits[i]! < 2147483648) ∧
      (runColoredTraced G).result.canong.size = n)
    (hN : n < 2147483648) (hMN : wordsOf n * n < 2147483648)
    (hn : PTree.get dense.id.n le = some (.Vint (ir n)))
    (hm : PTree.get dense.id.m le = some (.Vint (ir (wordsOf n))))
    (hl : PTree.get dense.id.lab le = some (.Vptr bl Ptrofs.zero))
    (ho : PTree.get dense.id.orbits le = some (.Vptr bo Ptrofs.zero))
    (hc : PTree.get dense.id.canong le = some (.Vptr bc Ptrofs.zero))
    (hlab : ArrayAt m .Mint32 bl 0 (ints (runColoredTraced G).result.canonlab) n)
    (horb : ArrayAt m .Mint32 bo 0 (ints (Statement.finalState G).orbits) n)
    (hcg : ∃ cw, ArrayAt m .Mint64 bc 0 (longs cw) (wordsOf n * n) ∧
      ∀ v < n, SetRep (fun w => bv64 (cw (wordsOf n * v + w))) (wordsOf n)
        (runColoredTraced G).result.canong[v]!)
    (hst : let r := runColoredTraced G
      FieldAt m .Mint32 bst 12 (.Vint (ir r.result.numorbits)) ∧
      FieldAt m .Mint32 bst 16 (.Vint (ir r.result.numgenerators)) ∧
      FieldAt m .Mint32 bst 20 (.Vint (ir 0)) ∧
      FieldAt m .Mint64 bst 24 (.Vlong (lr r.result.numnodes)) ∧
      FieldAt m .Mint64 bst 32 (.Vlong (lr r.result.numbadleaves)) ∧
      FieldAt m .Mint32 bst 40 (.Vint (ir r.result.maxlevel)) ∧
      FieldAt m .Mint64 bst 48 (.Vlong (lr r.result.tctotal)) ∧
      FieldAt m .Mint64 bst 56 (.Vlong (lr r.result.canupdates)) ∧
      Mem.range_perm m bst (zOfInt 0) (zOfInt 88) .Cur .Freeable)
    (hQ : ∀ t m', Writes t (outWords G) → Q.ret t (.Vint (ir 0)) m') :
    Wp Statement.xi ge dense.fn.main tOut Q (envOf bst) le m := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hfacts
  obtain ⟨cw, hcw, hrep⟩ := hcg
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hfree⟩ := hst
  have hw := envOf_write bst
  refine wp_wrSeq hw (eval_ci bst le m 2) fun t1 w1 => ?_
  apply wp_seq
  refine wp_intsOut dense.id.lab (by decide) _ hN hs2 hl hn hlab hw fun t2 le2 w2 hle2 => ?_
  simp only [seqPost, Post.after]
  refine wp_wrSeq hw (eval_ci bst le2 m 3) fun t3 w3 => ?_
  apply wp_seq
  refine wp_intsOut dense.id.orbits (by decide) _ hN hs4 (by rw [hle2 _ (by decide)]; exact ho)
    (by rw [hle2 _ (by decide)]; exact hn) horb hw fun t4 le4 w4 hle4 => ?_
  simp only [seqPost, Post.after]
  refine wp_wrSeq hw (eval_ci bst le4 m 4) fun t5 w5 => ?_
  apply wp_seq
  refine wp_wordsOut cw hMN (by rw [hle4 _ (by decide), hle2 _ (by decide)]; exact hc)
    (by rw [hle4 _ (by decide), hle2 _ (by decide)]; exact hm)
    (by rw [hle4 _ (by decide), hle2 _ (by decide)]; exact hn) hcw hw fun t6 le6 w6 _ => ?_
  simp only [seqPost, Post.after]
  refine wp_stats h1 h2 h3 h4 h5 h6 h7 h8 hfree fun t7 m7 w7 => ?_
  refine hQ _ m7 ?_
  have h := w1.append (w2.append (w3.append (w4.append (w5.append (w6.append w7)))))
  rw [write_ci 2 (by decide), write_ci 3 (by decide), write_ci 4 (by decide),
    range_map_get hs1, range_map_get hs3,
    words_eq_rowWords (fun j => bv64 (cw j)) _ hs5 hrep] at h
  simpa [outWords, List.append_assoc] using h

/-- HexGraphIso's result has `n` entries where the harness reads `n`, each
fitting in an `int`. -/
abbrev ResultFacts {n k : Nat} (G : Colored n k) : Prop :=
  (runColoredTraced G).result.canonlab.size = n ∧
  (∀ i < n, (runColoredTraced G).result.canonlab[i]! < 2147483648) ∧
  (Statement.finalState G).orbits.size = n ∧
  (∀ i < n, (Statement.finalState G).orbits[i]! < 2147483648) ∧
  (runColoredTraced G).result.canong.size = n

set_option maxRecDepth 100000 in
/-- The `densenauty` call and everything after it. -/
theorem wp_tCall {n k : Nat} (G : Colored n k) (gens : List (Array Nat)) {Q : Post}
    {le : temp_env} {m : mem} {bg bl bp bo bst bc : block}
    (hdn : Satisfies Statement.xi ge (.Internal dense.fn.densenauty)
      (densenautySpec G gens bg bl bp bo bst bc))
    (hfacts : ResultFacts G) (hN : n < 2147483648) (hMN : wordsOf n * n < 2147483648)
    (hn : PTree.get dense.id.n le = some (.Vint (ir n)))
    (hm : PTree.get dense.id.m le = some (.Vint (ir (wordsOf n))))
    (hg : PTree.get dense.id.g le = some (.Vptr bg Ptrofs.zero))
    (hl : PTree.get dense.id.lab le = some (.Vptr bl Ptrofs.zero))
    (hp : PTree.get dense.id.ptn le = some (.Vptr bp Ptrofs.zero))
    (ho : PTree.get dense.id.orbits le = some (.Vptr bo Ptrofs.zero))
    (hc : PTree.get dense.id.canong le = some (.Vptr bc Ptrofs.zero))
    (hpre : (densenautySpec G gens bg bl bp bo bst bc).pre [.Vptr bg Ptrofs.zero,
      .Vptr bl Ptrofs.zero, .Vptr bp Ptrofs.zero, .Vptr bo Ptrofs.zero,
      .Vptr Block.options Ptrofs.zero, .Vptr bst Ptrofs.zero,
      .Vint (ir (wordsOf n)), .Vint (ir n), .Vptr bc Ptrofs.zero] m)
    (hQ : ∀ t m', NautyVerified.Proofs.Search.Emits t
      (NautyVerified.Proofs.Search.gensWords gens n ++ outWords G) → Q.ret t (.Vint (ir 0)) m') :
    Wp Statement.xi ge dense.fn.main tCall Q (envOf bst) le m := by
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.densenauty Ptrofs.zero) (cc := cc_default)
    (targs := [tptr tulong, tptr tint, tptr tint, tptr tint,
      tptr (Tstruct dense.id.optionstruct noattr), tptr (Tstruct dense.id.«_1024» noattr), tint, tint,
      tptr tulong]) (tres := .Tvoid) _ _ hdn ?_ ?_ ?_
    (by simp [Genv.find_funct, funct_densenauty]) ?_ hpre ?_
  · rfl
  · simp only [Exec.evalExpr, Exec.lvalOfVar]
    rw [PTree.gso _ _ (by decide)]
    simp only [find_densenauty]
    rfl
  · have h1 : PTree.get dense.id.stats (envOf bst) = some (bst, Tstruct dense.id.«_1024» noattr) :=
      PTree.gss _ _ _
    have h2 : PTree.get dense.id.«dense_main:options» (envOf bst) = none := by
      rw [PTree.gso _ _ (by decide)]; rfl
    simp only [Exec.evalExprlist, Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, hg, hl, hp, ho, hc,
      hm, hn, h1, h2, find_options]
    rfl
  · rfl
  rintro t v m' ⟨hw, hlab, horb, hcg, h1, h2, h3, h4, h5, h6, h7, h8, hfree, -⟩
  exact wp_tOut G hfacts hN hMN hn hm hl ho hc hlab horb hcg
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, hfree⟩ fun t' m'' hw' => hQ _ m'' (hw.append hw'.emits)

end NautyVerified.Proofs.Harness

import NautyVerified.Proofs.Harness.PartC

/-!
# The harness's output

`wp_intsOut`: `for (i = 0; i < n; ++i) nv_write(p[i]);` writes the `int`
array `p`. `wp_wordsOut`: the loop over the `m * n` words of `canong` writes
them as signed `long`s. `wp_stats`: the statistics block writes the
counters as their C types hold them (`Statement.asInt`, `Statement.asLong`)
and `main` returns 0, freeing `stats`.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk longs)
open NautyVerified.Proofs.Search (Writes)

theorem labOut_eq :
    .Ssequence (sk (.Sset dense.id.i (ci 0 tint))) labOut =
      forT dense.id.i (tv dense.id.n) (sk (wr (ix dense.id.lab (tv dense.id.i)))) := rfl

theorem orbOut_eq :
    .Ssequence (sk (.Sset dense.id.i (ci 0 tint))) orbOut =
      forT dense.id.i (tv dense.id.n) (sk (wr (ix dense.id.orbits (tv dense.id.i)))) := rfl

theorem wp_intsOut {Q : Post} {e : env} {le : temp_env} {m : mem} {b : block} {N : Nat}
    (p : ident) (hpi : p ≠ dense.id.i) (o : Array Nat) (hN : N < 2147483648)
    (hos : ∀ j < N, o[j]! < 2147483648)
    (hp : PTree.get p le = some (.Vptr b Ptrofs.zero))
    (hn : PTree.get dense.id.n le = some (.Vint (ir N)))
    (harr : ArrayAt m .Mint32 b 0 (ints o) N) (hw : PTree.get dense.id.nv_write e = none)
    (hQ : ∀ t le', Writes t ((List.range N).map fun j => ((o[j]! : Nat) : Int)) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal t e le' m) :
    Wp Statement.xi ge dense.fn.main
      (forT dense.id.i (tv dense.id.n) (sk (wr (ix p (tv dense.id.i))))) Q e le m := by
  let Inv := fun (k : Nat) (t : trace) (le' : temp_env) (m' : mem) =>
    k ≤ N ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧ m' = m ∧
    Writes t ((List.range k).map fun j => ((o[j]! : Nat) : Int)) ∧
    ∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le
  refine wp_forT (Inv := Inv) dense.id.i (tv dense.id.n) _ N hN ?_ ?_ ?_ ?_
  · rintro k t le' m' ⟨hk, hi, -, -, ho⟩
    refine ⟨hk, hi, ?_, rfl⟩
    show PTree.get _ _ = _
    rw [ho _ (by decide)]; exact hn
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, rfl, Writes.nil, fun x h1 => temps_gso _ _ h1⟩
  · rintro k t le' m' hk ⟨-, hi, rfl, hwr, ho⟩
    have hok := hos k hk
    wp_step; wp_step
    refine wp_wr (x := lr (o[k]! : Int)) hw ?_ ?_
    · simp only [Exec.evalExprlist, typeof]
      rw [eval_at harr hN p (by rw [ho _ hpi]; exact hp) (tv dense.id.i) k hk hi rfl]
      simp only [ints, cop, cast_int_long_ir (a := (o[k]! : Int)) ⟨by omega, by omega⟩]
    · intro t' hw'
      refine ⟨hi, by omega, temps_gss _ _ _, rfl, ?_, fun x h1 => by rw [temps_gso _ _ h1, ho x h1]⟩
      rw [List.range_succ, List.map_append]
      have h := hwr.append hw'
      rw [signed_lr (by omega) (by omega)] at h
      exact h
  · rintro t le' m' ⟨-, -, rfl, hwr, ho⟩
    exact hQ t le' hwr ho

/-- The body of `cgOut`. -/
abbrev cgBody : statement :=
  sk (wr (.Ecast (.Ederef (.Ebinop .Oadd (pl dense.id.canong) (tv dense.id.i) (tptr tulong)) tulong) tlong))

theorem cgOut_eq :
    .Ssequence (sk (.Sset dense.id.i (ci 0 tint))) cgOut =
      forT dense.id.i (.Ebinop .Omul (tv dense.id.m) (tv dense.id.n) tint) cgBody := rfl

theorem wp_wordsOut {Q : Post} {e : env} {le : temp_env} {m : mem} {b : block} {Mw N : Nat}
    (cw : Nat → Lib.Integers.int64) (hT : Mw * N < 2147483648)
    (hp : PTree.get dense.id.canong le = some (.Vptr b Ptrofs.zero))
    (hmv : PTree.get dense.id.m le = some (.Vint (ir Mw)))
    (hn : PTree.get dense.id.n le = some (.Vint (ir N)))
    (harr : ArrayAt m .Mint64 b 0 (longs cw) (Mw * N)) (hw : PTree.get dense.id.nv_write e = none)
    (hQ : ∀ t le', Writes t ((List.range (Mw * N)).map fun j => (bv64 (cw j)).toInt) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal t e le' m) :
    Wp Statement.xi ge dense.fn.main
      (forT dense.id.i (.Ebinop .Omul (tv dense.id.m) (tv dense.id.n) tint) cgBody) Q e le m := by
  let Inv := fun (k : Nat) (t : trace) (le' : temp_env) (m' : mem) =>
    k ≤ Mw * N ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧ m' = m ∧
    Writes t ((List.range k).map fun j => (bv64 (cw j)).toInt) ∧
    ∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le
  refine wp_forT (Inv := Inv) dense.id.i _ _ (Mw * N) hT ?_ ?_ ?_ ?_
  · rintro k t le' m' ⟨hk, hi, -, -, ho⟩
    refine ⟨hk, hi, ?_, rfl⟩
    simp only [Exec.evalExpr, tv]
    rw [ho _ (by decide), ho _ (by decide), hmv, hn]
    simp only [typeof, cop, ir_mul]
    push_cast; rfl
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, rfl, Writes.nil, fun x h1 => temps_gso _ _ h1⟩
  · rintro k t le' m' hk ⟨-, hi, rfl, hwr, ho⟩
    wp_step; wp_step
    refine wp_wr (x := cw k) hw ?_ ?_
    · have hpk := Set.eval_word (e := e) harr (by omega) dense.id.canong (by rw [ho _ (by decide)]; exact hp)
        (tv dense.id.i) k hk hi rfl
      simp only [Exec.evalExprlist]
      rw [show Exec.evalExpr ge e le' m'
        (.Ecast (.Ederef (.Ebinop .Oadd (pl dense.id.canong) (tv dense.id.i) (tptr tulong)) tulong) tlong) =
          some (.Vlong (cw k)) by
        rw [Exec.evalExpr, hpk]; rfl]
      rfl
    · intro t' hw'
      refine ⟨hi, by omega, temps_gss _ _ _, rfl, ?_, fun x h1 => by rw [temps_gso _ _ h1, ho x h1]⟩
      rw [List.range_succ, List.map_append]
      have h := hwr.append hw'
      rw [intOfZ_Int64_signed] at h
      exact h
  · rintro t le' m' ⟨-, -, rfl, hwr, ho⟩
    exact hQ t le' hwr ho

end NautyVerified.Proofs.Harness
namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Source NautyVerified.Word NautyVerified.Spec
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.AST
open NautyVerified.Proofs.Set (sk longs)

set_option maxRecDepth 100000 in
theorem lval_numorbits (b : block) :
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.numorbits (.Vptr b Ptrofs.zero) =
    some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 12)), .Full) := rfl
kernel_rfl ofs_numorbits : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 12))) = zOfInt 12
set_option maxRecDepth 100000 in
theorem lval_numgenerators (b : block) :
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.numgenerators (.Vptr b Ptrofs.zero) =
    some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 16)), .Full) := rfl
kernel_rfl ofs_numgenerators : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 16))) = zOfInt 16
set_option maxRecDepth 100000 in
theorem lval_errstatus (b : block) :
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.errstatus (.Vptr b Ptrofs.zero) =
    some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 20)), .Full) := rfl
kernel_rfl ofs_errstatus : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 20))) = zOfInt 20
set_option maxRecDepth 100000 in
theorem lval_numnodes (b : block) :
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.numnodes (.Vptr b Ptrofs.zero) =
    some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 24)), .Full) := rfl
kernel_rfl ofs_numnodes : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 24))) = zOfInt 24
set_option maxRecDepth 100000 in
theorem lval_numbadleaves (b : block) :
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.numbadleaves (.Vptr b Ptrofs.zero) =
    some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 32)), .Full) := rfl
kernel_rfl ofs_numbadleaves : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 32))) = zOfInt 32
set_option maxRecDepth 100000 in
theorem lval_maxlevel (b : block) :
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.maxlevel (.Vptr b Ptrofs.zero) =
    some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 40)), .Full) := rfl
kernel_rfl ofs_maxlevel : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 40))) = zOfInt 40
set_option maxRecDepth 100000 in
theorem lval_tctotal (b : block) :
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.tctotal (.Vptr b Ptrofs.zero) =
    some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 48)), .Full) := rfl
kernel_rfl ofs_tctotal : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 48))) = zOfInt 48
set_option maxRecDepth 100000 in
theorem lval_canupdates (b : block) :
  Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) dense.id.canupdates (.Vptr b Ptrofs.zero) =
    some (b, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 56)), .Full) := rfl
kernel_rfl ofs_canupdates : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 56))) = zOfInt 56

/-- Reading a member of the local `stats`. -/
theorem eval_stats {e : env} {le : temp_env} {m : mem} {bst : block} {f : Common.AST.ident} {ty : type}
    {chunk : Common.AST.memory_chunk} {o : Int} {v : val}
    (he : PTree.get dense.id.stats e = some (bst, Tstruct dense.id.«_1024» noattr))
    (hl : Exec.lvalOfField ge (Tstruct dense.id.«_1024» noattr) f (.Vptr bst Ptrofs.zero) =
      some (bst, Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt o)), .Full))
    (ho : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt o))) = zOfInt o)
    (hmode : access_mode ty = .By_value chunk)
    (hv : Mem.load chunk m bst (zOfInt o) = some v) :
    Exec.evalExpr ge e le m (.Efield (.Evar dense.id.stats (Tstruct dense.id.«_1024» noattr)) f ty) =
      some v := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, he, ite_true]
  simp only [Exec.derefLoc, typeof,
    show access_mode (Tstruct dense.id.«_1024» noattr) = .By_copy from rfl, hl]
  rw [hmode]
  show Mem.load _ _ _ _ = _
  rw [ho, hv]

/-- An `int` member of `statsblk`, cast to `long`, is written as `asInt`. -/
theorem write_ir (v : Nat) :
    intOfZ (Lib.Integers.Int64.signed (Cfrontend.Cop.cast_int_long .Signed (ir v))) =
      Statement.asInt v := by
  show intOfZ (Lib.Integers.Int64.signed (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir v)))) = _
  rw [intOfZ_Int64_signed, bv64_repr, intOfZ_Int_signed, bv32_ir, BitVec.toInt_ofInt,
    Statement.asInt, BitVec.ofInt_natCast]
  have h1 := BitVec.toInt_lt (x := BitVec.ofNat 32 v)
  have h2 := BitVec.le_toInt (x := BitVec.ofNat 32 v)
  apply Int.bmod_eq_of_le <;> simp at h1 h2 <;> omega

/-- An `unsigned long` member of `statsblk`, cast to `long`, is written as `asLong`. -/
theorem write_lr (v : Nat) :
    intOfZ (Lib.Integers.Int64.signed (lr v)) = Statement.asLong v := by
  rw [intOfZ_Int64_signed, bv64_repr, intOfZ_zOfInt, Statement.asLong, BitVec.ofInt_natCast]

open NautyVerified.Proofs.Search (Writes) in
/-- `nv_write(a); s`. -/
theorem wp_wrSeq {Q : Post} {e : env} {le : temp_env} {m : mem} {a : expr} {s : statement}
    {x : Lib.Integers.int64}
    (he : PTree.get dense.id.nv_write e = none)
    (ha : Exec.evalExprlist ge e le m [a] [tlong] = some [.Vlong x])
    (h : ∀ t, Writes t [intOfZ (Lib.Integers.Int64.signed x)] →
      Wp Statement.xi ge dense.fn.main s (Q.after t) e le m) :
    Wp Statement.xi ge dense.fn.main (.Ssequence (sk (wr a)) s) Q e le m := by
  apply wp_seq; apply wp_seq; apply wp_skip
  refine wp_wr he ha fun t ht => ?_
  simp only [seqPost, Post.after]
  exact h t ht

set_option maxRecDepth 100000 in
open NautyVerified.Proofs.Search (FieldAt Writes) in
/-- The statistics block and `return 0`. -/
theorem wp_stats {Q : Post} {le : temp_env} {m : mem} {bst : block}
    {no ng nn nb ml tc cu : Nat}
    (hno : FieldAt m .Mint32 bst 12 (.Vint (ir no))) (hng : FieldAt m .Mint32 bst 16 (.Vint (ir ng)))
    (her : FieldAt m .Mint32 bst 20 (.Vint (ir 0)))
    (hnn : FieldAt m .Mint64 bst 24 (.Vlong (lr nn))) (hnb : FieldAt m .Mint64 bst 32 (.Vlong (lr nb)))
    (hml : FieldAt m .Mint32 bst 40 (.Vint (ir ml)))
    (htc : FieldAt m .Mint64 bst 48 (.Vlong (lr tc))) (hcu : FieldAt m .Mint64 bst 56 (.Vlong (lr cu)))
    (hfree : Mem.range_perm m bst (zOfInt 0) (zOfInt 88) .Cur .Freeable)
    (hQ : ∀ t m', Writes t [5, Statement.asInt no, Statement.asInt ng, Statement.asLong nn,
      Statement.asLong nb, Statement.asInt ml, Statement.asLong tc, Statement.asLong cu, 0] →
      Q.ret t (.Vint (ir 0)) m') :
    Wp Statement.xi ge dense.fn.main tStats Q
      (PTree.set dense.id.stats (bst, Tstruct dense.id.«_1024» noattr) empty_env) le m := by
  have he : PTree.get dense.id.stats (PTree.set dense.id.stats (bst, Tstruct dense.id.«_1024» noattr)
      empty_env) = some (bst, Tstruct dense.id.«_1024» noattr) := PTree.gss _ _ _
  have hw : PTree.get dense.id.nv_write (PTree.set dense.id.stats
      (bst, Tstruct dense.id.«_1024» noattr) empty_env) = none := by
    rw [PTree.gso _ _ (by decide)]; rfl
  have hbl : blocks_of_env ge (PTree.set dense.id.stats (bst, Tstruct dense.id.«_1024» noattr)
      empty_env) = [(bst, zOfInt 0, zOfInt 88)] := rfl
  have hc : ∀ v : Nat, Exec.evalExprlist ge (PTree.set dense.id.stats
      (bst, Tstruct dense.id.«_1024» noattr) empty_env) le m [ci v tint] [tlong] =
      some [.Vlong (Cfrontend.Cop.cast_int_long .Signed (ir v))] := fun v => rfl
  refine wp_wrSeq hw (hc 5) fun t1 h1 => ?_
  refine wp_wrSeq (x := Cfrontend.Cop.cast_int_long .Signed (ir no)) hw ?_ fun t2 h2 => ?_
  · simp only [Exec.evalExprlist]
    rw [eval_stats he (lval_numorbits bst) ofs_numorbits rfl hno.load]
    rfl
  refine wp_wrSeq (x := Cfrontend.Cop.cast_int_long .Signed (ir ng)) hw ?_ fun t3 h3 => ?_
  · simp only [Exec.evalExprlist]
    rw [eval_stats he (lval_numgenerators bst) ofs_numgenerators rfl hng.load]
    rfl
  refine wp_wrSeq (x := lr nn) hw ?_ fun t4 h4 => ?_
  · simp only [Exec.evalExprlist]
    rw [Exec.evalExpr, eval_stats he (lval_numnodes bst) ofs_numnodes rfl hnn.load]
    rfl
  refine wp_wrSeq (x := lr nb) hw ?_ fun t5 h5 => ?_
  · simp only [Exec.evalExprlist]
    rw [Exec.evalExpr, eval_stats he (lval_numbadleaves bst) ofs_numbadleaves rfl hnb.load]
    rfl
  refine wp_wrSeq (x := Cfrontend.Cop.cast_int_long .Signed (ir ml)) hw ?_ fun t6 h6 => ?_
  · simp only [Exec.evalExprlist]
    rw [eval_stats he (lval_maxlevel bst) ofs_maxlevel rfl hml.load]
    rfl
  refine wp_wrSeq (x := lr tc) hw ?_ fun t7 h7 => ?_
  · simp only [Exec.evalExprlist]
    rw [Exec.evalExpr, eval_stats he (lval_tctotal bst) ofs_tctotal rfl htc.load]
    rfl
  refine wp_wrSeq (x := lr cu) hw ?_ fun t8 h8 => ?_
  · simp only [Exec.evalExprlist]
    rw [Exec.evalExpr, eval_stats he (lval_canupdates bst) ofs_canupdates rfl hcu.load]
    rfl
  apply wp_seq; apply wp_seq; apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  refine wp_wr (x := Cfrontend.Cop.cast_int_long .Signed (ir 0)) hw ?_ fun t9 h9 => ?_
  · simp only [Exec.evalExprlist]
    rw [eval_stats he (lval_errstatus bst) ofs_errstatus rfl her.load]
    rfl
  obtain ⟨m', hf⟩ := Mem.range_perm_free m bst (zOfInt 0) (zOfInt 88) hfree
  apply wp_seq; apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  apply wp_return_some_eval
  simp only [Exec.evalExpr]
  rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) (typeof (ci 0 tint))
    dense.fn.main.fn_return m = some (.Vint (ir 0)) from rfl]
  simp only [hbl, Mem.free_list, hf]
  refine hQ _ _ ?_
  have h := h1.append (h2.append (h3.append (h4.append (h5.append (h6.append (h7.append
    (h8.append (h9.append Writes.nil))))))))
  rw [show (ir 0 : Lib.Integers.int) = ir ((0 : Nat) : Int) from rfl] at h
  simp only [write_ir, write_lr, List.cons_append, List.nil_append] at h
  exact h
end NautyVerified.Proofs.Harness

import NautyVerified.Proofs.Set.GlobalDel
import NautyVerified.Proofs.Top.Opts

/-!
# `nauty()`'s partition and active set

`emptySetGE g mE es t`: `EMPTYSET(g, mE)` for a pointer global `g` and any
`int` expression `mE` for the number of words (nauty.c's global `m`).
-/

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Alloc (Keep)

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- `EMPTYSET(g, mE)`. -/
abbrev emptySetGE (g : Common.AST.ident) (mE : expr) (es t : Common.AST.ident) : statement :=
  .Ssequence
    (sk (.Sset es (.Ebinop .Oadd (gpvC g) mE (tptr tulong))))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Ogt (pv es) (gpvC g) tint) .Sskip .Sbreak))
        (.Ssequence
          (.Ssequence
            (sk (.Sset t (.Ecast (.Ebinop .Osub (pv es) (ci 1 tint) (tptr tulong)) (tptr tulong))))
            (.Sset es (pv t)))
          (.Sassign (.Ederef (pv t) tulong) (ci 0 tint))))
      .Sskip)

theorem wp_emptySetGE {g es tmp : Common.AST.ident} {mE : expr} (het : es ≠ tmp) {f : function} {Q : Post}
    {e : env} {le : temp_env} {m : mem} {bg ba : block} {ofs : ptrofs} {vals : Nat → val} {M : Nat}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr ba ofs)) (hbg : bg ≠ ba)
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) vals M) (hM : 0 < M)
    (hM2 : M < 2147483648) (hm : Exec.evalExpr ge e le m mE = some (.Vint (ir M)))
    (hmt : typeof mE = tint)
    (hQ : ∀ le' m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs fun _ => lr 0) M →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * M) →
      Keep m m' ba → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ k, k ≠ es → k ≠ tmp → PTree.get k le' = PTree.get k le) → Q.normal E0 e le' m') :
    Wp xi ge f (emptySetGE g mE es tmp) Q e le m := by
  have hf := harr.fits
  have hb := harr.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  simp only [emptySetGE, sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, hm, hmt]
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg, Exec.derefLoc, Cfrontend.Ctypes.access_mode,
    Mem.loadv, Alloc.Mptr_eq, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp,
    typeof, cop]
  rw [add_ptrTo ofs _ M (by omega), sizeof_tulong]
  simp only [E0_append]
  let base := intOfZ (Ptrofs.unsigned ofs)
  refine wp_loop (I := fun k t e' le' m' => t = E0 ∧ e = e' ∧ k ≤ M ∧
      PTree.get es le' = some (.Vptr ba (ptrTo base 8 k)) ∧
      ArrayAt m' .Mint64 ba base (clearedFromV vals k) M ∧ Unch m m' (· = ba) ∧
      Outside m m' ba base (base + 8 * M) ∧ Keep m m' ba ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
      ∀ k', k' ≠ es → k' ≠ tmp → PTree.get k' le' = PTree.get k' le)
    (J := fun k t e' le' m' => ∃ k' < k, t = E0 ∧ e = e' ∧ k' ≤ M ∧
      PTree.get es le' = some (.Vptr ba (ptrTo base 8 k')) ∧
      ArrayAt m' .Mint64 ba base (clearedFromV vals k') M ∧ Unch m m' (· = ba) ∧
      Outside m m' ba base (base + 8 * M) ∧ Keep m m' ba ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
      ∀ k'', k'' ≠ es → k'' ≠ tmp → PTree.get k'' le' = PTree.get k'' le) ?_ ?_ (n := M)
    ⟨rfl, rfl, Nat.le_refl _, temps_gss _ _ _, by
      refine ⟨hb, by rw [h8]; omega, fun i hi => ?_, fun i hi => harr.writable i hi⟩
      simp only [clearedFromV, ite_eq_left hi]; exact harr.load i hi,
      Unch.refl _ _, Outside.refl _ _ _ _, Alloc.Keep.refl _ _, fun _ h => h, fun k' hk _ => temps_gso _ _ hk⟩
  · rintro k t e' le' m' ⟨rfl, rfl, hk, hes, harr', hu, hout, hkp, hvd, hother⟩
    have hp' : Mem.load .Mint64 m' bg (zOfInt 0) = some (.Vptr ba ofs) := by
      rw [hu.load _ _ _ hbg]; exact hp
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg, Exec.derefLoc, Cfrontend.Ctypes.access_mode,
      Mem.loadv, Alloc.Mptr_eq, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp', hes,
      typeof, cop]
    rw [cmplu_ptrTo harr' hM hk rfl]
    simp only [Option.map, cop]
    rcases k with _ | j
    · rw [ite_eq_right (by decide)]
      apply wp_break
      have h0 : clearedFromV vals 0 = longs fun _ => lr 0 := by funext w; simp [clearedFromV, longs]
      rw [h0] at harr'
      exact hQ le' m' harr' hu hout hkp hvd hother
    · rw [ite_eq_left (by simp)]
      apply wp_skip
      simp only [E0_append]
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hes, typeof, cop, sub_ptrTo8]
      simp only [E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss, E0_append]
      have hj : j < M := by omega
      have hu8 : intOfZ (Ptrofs.unsigned (ptrTo base 8 j)) = base + 8 * j := by
        apply unsigned_ptrTo <;> omega
      obtain ⟨m'', hst, harr'', -⟩ := store_array harr' hj (.Vlong (lr 0)) rfl
      apply wp_assign_eval
      simp only [Exec.evalLvalue, Exec.evalExpr, temps_gss, temps_gso _ _ het.symm, typeof, cop,
        Exec.assignLoc, Cfrontend.Ctypes.access_mode,
        cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
      show match Mem.store .Mint64 m' ba (Ptrofs.unsigned _) _ with
        | some m' => _ | none => False
      rw [show Ptrofs.unsigned (ptrTo base 8 j) = elemOfs .Mint64 base j by
        rw [← zOfInt_intOfZ (Ptrofs.unsigned _), hu8]; rfl, hst]
      refine ⟨j, by omega, trivial, trivial, by omega, ?_, ?_, hu.trans (Unch.store hst rfl),
        hout.trans (Outside.store harr' hj hst (Int.le_refl _) (by rw [h8]; exact Int.le_refl _)),
        hkp.trans (Alloc.Keep.store hst (by simp only [elemOfs, intOfZ_zOfInt, h8]; omega)),
        fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst z (hvd z hz), ?_⟩
      · rfl
      · rw [← clearedFromV_succ]; exact harr''
      · intro k'' h1 h2
        rw [temps_gso _ _ h1, temps_gso _ _ h2, hother _ h1 h2]
  · rintro k t e' le' m' ⟨k', hk', h⟩
    apply wp_skip
    exact ⟨k', hk', by simpa using h⟩


end NautyVerified.Proofs.Set

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (FieldAt IntAt PtrAt)

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- `ptn` after the first `k` steps of `if (ptn[i] != 0) ptn[i] = NAUTY_INFINITY`. -/
def normP (h : Array Nat) (k : Nat) : Array Nat :=
  (List.range k).foldl (fun a j => if h[j]! ≠ 0 then a.set! j Search.nautyInf else a) h

/-- The zeros among the first `k` entries. -/
def zeros (h : Array Nat) (k : Nat) : Nat := (List.range k).countP fun j => h[j]! = 0

theorem normP_succ (h : Array Nat) (k : Nat) :
    normP h (k + 1) = if h[k]! ≠ 0 then (normP h k).set! k Search.nautyInf else normP h k := by
  simp [normP, List.range_succ, List.foldl_append]

theorem zeros_succ (h : Array Nat) (k : Nat) :
    zeros h (k + 1) = zeros h k + if h[k]! = 0 then 1 else 0 := by
  simp [zeros, List.range_succ, List.countP_append]

theorem normP_size (h : Array Nat) : ∀ k, (normP h k).size = h.size
  | 0 => rfl
  | k + 1 => by
    rw [normP_succ]; split
    · simp [normP_size h k]
    · exact normP_size h k

theorem normP_get (h : Array Nat) : ∀ k j, j < h.size →
    (normP h k)[j]! = if j < k ∧ h[j]! ≠ 0 then Search.nautyInf else h[j]!
  | 0, j, _ => by simp [normP]
  | k + 1, j, hj => by
    rw [normP_succ]
    have ih := normP_get h k j hj
    by_cases hk : h[k]! ≠ 0
    · rw [if_pos hk]
      by_cases hjk : j = k
      · subst hjk
        rw [Array.getElem!_set!_self _ _ _ (by rw [normP_size]; exact hj)]
        simp [hk]
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjk), ih]
        by_cases hjk' : j < k
        · simp [hjk', show j < k + 1 by omega]
        · simp [hjk', show ¬ j < k + 1 by omega]
    · rw [if_neg hk, ih]
      by_cases hjk : j = k
      · subst hjk; simp at hk; simp [hk]
      · by_cases hjk' : j < k
        · simp [hjk', show j < k + 1 by omega]
        · simp [hjk', show ¬ j < k + 1 by omega]

/-- The body of the normalisation loop. -/
abbrev normBody : statement :=
  Set.sk (.Sifthenelse
    (.Ebinop .One (Refine.ix dense.id.«ptn» (Refine.tv dense.id.«i»)) (ci 0 tint) tint)
    (Set.sk (.Sassign (Refine.ix dense.id.«ptn» (Refine.tv dense.id.«i»)) (ci 2000000002 tint)))
    (Set.sk (.Sset dense.id.«numcells»
      (.Ebinop .Oadd (Refine.tv dense.id.«numcells») (ci 1 tint) tint))))

theorem zeros_le (h : Array Nat) : ∀ k, zeros h k ≤ k
  | 0 => by simp [zeros]
  | k + 1 => by rw [zeros_succ]; have := zeros_le h k; split <;> omega

/-- `for (i = 0; i < n; ++i) if (ptn[i] != 0) ptn[i] = NAUTY_INFINITY; else ++numcells;` -/
theorem wp_normLoop {Q : Post} {le : temp_env} {m : mem} {bp : block} {n : Nat} (h : Array Nat)
    (hsz : h.size = n) (hn : n < 1073741824) (hh : ∀ j < n, h[j]! < 2147483648)
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr bp Ptrofs.zero))
    (hN : IntAt m Search.Block.n n)
    (hnc : PTree.get dense.id.«numcells» le = some (.Vint (ir 0)))
    (harr : ArrayAt m .Mint32 bp 0 (ints h) n) (hbp : bp ≠ Search.Block.n)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bp 0 (ints (normP h n)) n →
      PTree.get dense.id.«numcells» le' = some (.Vint (ir (zeros h n))) →
      Unch m m' (· = bp) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.«i» → x ≠ dense.id.«numcells» → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge dense.fn.nauty (forLoopC dense.id.«i»
      (.Ebinop .Olt (Refine.tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint) normBody)
      Q empty_env le m := by
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k ≤ n ∧ PTree.get dense.id.«i» le' = some (.Vint (ir k)) ∧
    PTree.get dense.id.«numcells» le' = some (.Vint (ir (zeros h k))) ∧
    ArrayAt m' .Mint32 bp 0 (ints (normP h k)) n ∧ Unch m m' (· = bp) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    (∀ x, x ≠ dense.id.«i» → x ≠ dense.id.«numcells» → PTree.get x le' = PTree.get x le)
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) => k < n ∧
    PTree.get dense.id.«i» le' = some (.Vint (ir k)) ∧
    PTree.get dense.id.«numcells» le' = some (.Vint (ir (zeros h (k + 1)))) ∧
    ArrayAt m' .Mint32 bp 0 (ints (normP h (k + 1))) n ∧ Unch m m' (· = bp) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    (∀ x, x ≠ dense.id.«i» → x ≠ dense.id.«numcells» → PTree.get x le' = PTree.get x le)
  refine wp_forLoopC (Inv := Inv) (Mid := Mid) dense.id.«i» _ rfl normBody n (by omega) ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, -, -, hu, -, -⟩
    refine ⟨hk, hi, ?_⟩
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' (Refine.tv dense.id.«i») = _ from hi,
      Search.eval_gint (e := empty_env) rfl Search.find_n (hN.unch hu (Ne.symm hbp))]
    simp only [typeof, cop]
    rw [ir_lt (a := k) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, ?_, harr, Unch.refl _ _, fun _ h => h,
      fun x hx _ => temps_gso _ _ hx⟩
    rw [temps_gso _ _ (by decide)]; exact hnc
  · rintro k le' m' hk ⟨-, hi, hnck, harr', hu, hg, ho⟩
    have hp' : PTree.get dense.id.«ptn» le' = some (.Vptr bp Ptrofs.zero) := by
      rw [ho _ (by decide) (by decide)]; exact hptn
    have hsz' : (normP h k).size = n := by rw [normP_size, hsz]
    have hget := normP_get h k k (by omega)
    rw [if_neg (by omega)] at hget
    have hhk := hh k hk
    have hrd := eval_at (ge := ge) (e := empty_env) harr' (by omega) dense.id.«ptn» hp'
      (Refine.tv dense.id.«i») k hk hi rfl
    simp only [normBody, Set.sk]
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hrd]
    simp only [Exec.evalExpr, ints, hget, typeof, cop]
    rw [ir_eq (a := (h[k]! : Int)) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    by_cases hz : h[k]! = 0
    · rw [ite_eq_right (by simp [hz])]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hnck, typeof, cop, ir_add]
      refine ⟨trivial, hk, temps_gso _ _ (by decide) |>.trans hi, ?_, ?_, hu, hg, fun x h1 h2 => ?_⟩
      · rw [temps_gss, zeros_succ, if_pos hz]; push_cast; rfl
      · rw [normP_succ, if_neg (by simpa using hz)]; exact harr'
      · rw [temps_gso _ _ h2, ho x h1 h2]
    · rw [ite_eq_left (by simp; omega)]
      wp_step; wp_step
      refine Search.wp_storeV (ofs := Ptrofs.zero) harr' (by omega) dense.id.«ptn» hp'
        (Refine.tv dense.id.«i») k hk hi rfl (ci 2000000002 tint) 2000000002 rfl rfl ?_
      intro m'' harr'' hu'' hg''
      refine ⟨rfl, hk, hi, ?_, ?_, hu.trans hu'', fun z hz => hg'' _ (hg z hz), ho⟩
      · rw [zeros_succ, if_neg hz]; simpa using hnck
      · rw [normP_succ, if_pos hz, ints_set (by rw [normP_size, hsz]; exact hk)]
        exact harr''
  · rintro k le' m' ⟨hk, hi, hnck, harr', hu, hg, ho⟩
    refine ⟨hi, by omega, temps_gss _ _ _, ?_, harr', hu, hg, fun x h1 h2 => ?_⟩
    · rw [temps_gso _ _ (by decide)]; exact hnck
    · rw [temps_gso _ _ h1, ho x h1 h2]
  · rintro le' m' ⟨-, -, hnck, harr', hu, hg, ho⟩
    exact hQ le' m' harr' hnck hu hg ho

/-- `while (ptn[i]) ++i;` -/
abbrev toEnd : statement :=
  .Sloop
    (.Ssequence
      (Set.sk (.Sifthenelse (Refine.ix dense.id.«ptn» (Refine.tv dense.id.«i»)) .Sskip .Sbreak))
      (Set.sk (.Sset dense.id.«i» (.Ebinop .Oadd (Refine.tv dense.id.«i») (ci 1 tint) tint))))
    .Sskip

theorem wp_toEnd {Q : Post} {le : temp_env} {m : mem} {bp : block} {n : Nat} {p : Array Nat}
    {s e : Nat} (harr : ArrayAt m .Mint32 bp 0 (ints p) n) (hn : n < 2147483648)
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr bp Ptrofs.zero))
    (hi : PTree.get dense.id.«i» le = some (.Vint (ir s))) (hse : s ≤ e) (hen : e < n)
    (hz : p[e]! = 0) (hnz : ∀ q, s ≤ q → q < e → p[q]! ≠ 0)
    (hsm : ∀ q < n, p[q]! < 2147483648)
    (hQ : ∀ le', PTree.get dense.id.«i» le' = some (.Vint (ir e)) →
      (∀ x, x ≠ dense.id.«i» → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m) :
    Wp xi ge dense.fn.nauty toEnd Q empty_env le m := by
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ q, s ≤ q ∧ q ≤ e ∧ v = e - q ∧
      PTree.get dense.id.«i» le' = some (.Vint (ir q)) ∧
      ∀ x, x ≠ dense.id.«i» → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := e - s) ⟨rfl, rfl, rfl, s, Nat.le_refl _, hse, rfl, hi, fun _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, q, hq1, hq2, rfl, hiq, ho⟩
    have hp' : PTree.get dense.id.«ptn» le' = some (.Vptr bp Ptrofs.zero) := by
      rw [ho _ (by decide)]; exact hptn
    have hrd := eval_at (ge := ge) (e := empty_env) harr hn dense.id.«ptn» hp'
      (Refine.tv dense.id.«i») q (by omega) hiq rfl
    have hsq := hsm q (by omega)
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [hrd]
    simp only [ints, typeof, cop]
    by_cases hqe : q = e
    · subst hqe
      rw [hz]
      rw [ite_eq_right (by decide)]
      apply wp_break
      exact hQ le' hiq ho
    · have hne := hnz q hq1 (by omega)
      rw [ite_eq_left (by
        rw [show Lib.Integers.Int.zero = ir 0 from rfl,
          ir_eq (a := (p[q]! : Int)) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
        simp; omega)]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hiq, typeof, cop, ir_add]
      refine ⟨e - (q + 1), by omega, by simp, rfl, rfl, q + 1, by omega, by omega, rfl, ?_,
        fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩
      rw [temps_gss]; push_cast; rfl
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

open Hex.GraphIso.Nauty in
/-- One step of `initActive`'s fold. -/
def actStep {n : Nat} (p : VSet n × Nat) (e : Nat) : VSet n × Nat := (p.1.insert p.2, e + 1)

open Hex.GraphIso.Nauty in
/-- `initActive`'s fold over the first `j` cell ends. -/
def actPre {n : Nat} (ends : List Nat) (j : Nat) : VSet n × Nat :=
  (ends.take j).foldl actStep (.empty, 0)

open Hex.GraphIso.Nauty in
theorem actPre_succ {n : Nat} (ends : List Nat) {j : Nat} (hj : j < ends.length) :
    (actPre (n := n) ends (j + 1)) = actStep (actPre ends j) ends[j] := by
  simp only [actPre]
  rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
  rfl

open Hex.GraphIso.Nauty in
theorem actPre_all {n : Nat} (ends : List Nat) :
    (actPre (n := n) ends ends.length).1 = initActive n ends := by
  simp only [actPre, List.take_length, initActive]
  rfl

open Hex.GraphIso.Nauty in
theorem actPre_start {n : Nat} (ends : List Nat) :
    ∀ j, (actPre (n := n) ends (j + 1)).2 = (ends[j]?.getD 0) + 1 ∨ ends.length ≤ j := by
  intro j
  by_cases hj : j < ends.length
  · left
    rw [actPre_succ ends hj]
    simp [actStep, List.getElem?_eq_getElem hj]
  · right; omega

/-- `for (i = 0; i < n; ++i) { ADDELEMENT(active, i); while (ptn[i]) ++i; }` -/
abbrev actLoop : statement :=
  .Ssequence (Set.sk (.Sset dense.id.«i» (ci 0 tint)))
    (.Sloop
      (.Ssequence
        (Set.sk (.Sifthenelse (.Ebinop .Olt (Refine.tv dense.id.«i») (.Evar dense.id.«nauty:n» tint) tint)
          .Sskip .Sbreak))
        (.Ssequence (Set.addElementG dense.id.«nauty:active» dense.id.«nauty:bit» (Refine.tv dense.id.«i»))
          toEnd))
      (Set.sk (.Sset dense.id.«i» (.Ebinop .Oadd (Refine.tv dense.id.«i») (ci 1 tint) tint))))

theorem sorted_le_last {ends : List Nat} (hs : ends.Pairwise (· < ·)) {i : Nat}
    (hi : i < ends.length) : ends[i] ≤ ends[ends.length - 1]'(by omega) := by
  by_cases h : i = ends.length - 1
  · subst h; exact Nat.le_refl _
  · exact Nat.le_of_lt (List.pairwise_iff_getElem.1 hs i _ hi (by omega) (by omega))

open Hex.GraphIso.Nauty in
theorem wp_actLoop {Q : Post} {le : temp_env} {m : mem} {bp bA : block} {n M : Nat}
    {ends : List Nat} {aw : Nat → Lib.Integers.int64}
    (hsort : ends.Pairwise (· < ·)) (hlt : ∀ e ∈ ends, e < n) (hlast : n - 1 ∈ ends)
    (hn0 : 0 < n) (hn : n < 1073741824) (hnM : n ≤ 64 * M) (hM : M < 33554432)
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr bp Ptrofs.zero))
    (harr : ArrayAt m .Mint32 bp 0 (ints (initPtn n Search.nautyInf ends)) n)
    (hN : IntAt m Search.Block.n n)
    (hA : Mem.load .Mint64 m Block.nautyActive (zOfInt 0) = some (.Vptr bA Ptrofs.zero))
    (haw : ArrayAt m .Mint64 bA 0 (Set.longs aw) M)
    (hrep : SetRep (fun w => bv64 (aw w)) M (VSet.empty : VSet n))
    (hbit : Set.BitTable m Block.nautyBit)
    (hsep : bA ≠ bp ∧ bA ≠ Search.Block.n ∧ bA ≠ Block.nautyActive ∧ bA ≠ Block.nautyBit)
    (hQ : ∀ le' m' (aw' : Nat → Lib.Integers.int64), ArrayAt m' .Mint64 bA 0 (Set.longs aw') M →
      SetRep (fun w => bv64 (aw' w)) M (initActive n ends) → Unch m m' (· = bA) →
      Alloc.Keep m m' bA → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.«i» → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi ge dense.fn.nauty actLoop Q empty_env le m := by
  have hne : ends ≠ [] := fun h => by simp [h] at hlast
  have hlen : 0 < ends.length := List.length_pos_iff.2 hne
  -- the last end is `n - 1`
  have hlastv : ends[ends.length - 1]'(by omega) = n - 1 := by
    obtain ⟨t, ht, hte⟩ := List.getElem_of_mem hlast
    have h1 := sorted_le_last hsort ht
    have h2 := hlt _ (List.getElem_mem (l := ends) (by omega : ends.length - 1 < ends.length))
    omega
  -- `ptn` entries
  have hpget : ∀ q < n, (initPtn n Search.nautyInf ends)[q]! = if q ∈ ends then 0 else Search.nautyInf :=
    fun q hq => by
      rw [getElem!_initPtn]
      by_cases hm : q ∈ ends
      · simp [hm, hq]
      · simp [hm, hq]
  have hsm : ∀ q < n, (initPtn n Search.nautyInf ends)[q]! < 2147483648 := fun q hq => by
    rw [hpget q hq]; split <;> decide
  -- the start of cell `j`
  let st : Nat → Nat := fun j => (actPre (n := n) ends j).2
  have hst0 : st 0 = 0 := rfl
  have hstS : ∀ j (hj : j < ends.length), st (j + 1) = ends[j] + 1 := fun j hj => by
    show (actPre ends (j + 1)).2 = _
    rw [actPre_succ ends hj]; rfl
  have hstLe : ∀ j (hj : j < ends.length), st j ≤ ends[j] := fun j hj => by
    rcases j with _ | j
    · rw [hst0]; exact Nat.zero_le _
    · rw [hstS j (by omega)]
      exact List.pairwise_iff_getElem.1 hsort j (j + 1) (by omega) hj (by omega)
  have hgap : ∀ j (hj : j < ends.length) q, st j ≤ q → q < ends[j] → q ∉ ends := by
    intro j hj q h1 h2 hq
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hq
    rcases Nat.lt_trichotomy t j with htj | rfl | htj
    · rcases j with _ | j
      · omega
      · rw [hstS j (by omega)] at h1
        have := List.pairwise_iff_getElem.1 hsort t j ht (by omega)
        rcases Nat.lt_or_ge t j with h | h
        · have := this h; omega
        · have : t = j := by omega
          subst this; omega
    · omega
    · have := List.pairwise_iff_getElem.1 hsort j t hj ht htj; omega
  have hstLen : st ends.length = n := by
    have := hstS (ends.length - 1) (by omega)
    rw [show ends.length - 1 + 1 = ends.length by omega] at this
    rw [this, hlastv]; omega
  have hstLt : ∀ j < ends.length, st j < n := fun j hj => by
    have := hstLe j hj; have := hlt _ (List.getElem_mem (l := ends) hj); omega
  let Fr := fun (le' : temp_env) (m' : mem) (s : VSet n) =>
    ∃ aw' : Nat → Lib.Integers.int64, ArrayAt m' .Mint64 bA 0 (Set.longs aw') M ∧
      SetRep (fun w => bv64 (aw' w)) M s ∧ Unch m m' (· = bA) ∧ Alloc.Keep m m' bA ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
      (∀ x, x ≠ dense.id.«i» → PTree.get x le' = PTree.get x le)
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ j, j ≤ ends.length ∧ v = n - st j ∧
      PTree.get dense.id.«i» le' = some (.Vint (ir (st j))) ∧ Fr le' m' (actPre ends j).1
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ j, ∃ hj : j < ends.length, v = n - st j ∧
      PTree.get dense.id.«i» le' = some (.Vint (ir (ends[j]'hj))) ∧ Fr le' m' (actPre ends (j + 1)).1
  simp only [actLoop, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - st 0)
    ⟨rfl, rfl, 0, Nat.zero_le _, rfl, temps_gss _ _ _,
      aw, haw, hrep, Unch.refl _ _, Alloc.Keep.refl _ _, fun _ h => h,
      fun x hx => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, j, hj, rfl, hi, aw', haw', hrep', hu, hk, hg, ho⟩
    have hN' := hN.unch hu (Ne.symm hsep.2.1)
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge empty_env le' m' (Refine.tv dense.id.«i») = _ from hi,
      Search.eval_gint (e := empty_env) rfl Search.find_n hN']
    simp only [typeof, cop]
    have hstn : st j ≤ n := by
      rcases Nat.lt_or_ge j ends.length with h | h
      · exact Nat.le_of_lt (hstLt j h)
      · have : j = ends.length := by omega
        subst this; omega
    rw [ir_lt (a := st j) (b := n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hje : j = ends.length
    · subst hje
      rw [hstLen, ite_eq_right (by simp)]
      apply wp_break
      simp only [E0_append]
      rw [actPre_all] at hrep'
      exact hQ le' m' aw' haw' hrep' hu hk hg ho
    · have hjl : j < ends.length := by omega
      have hsj := hstLt j hjl
      rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      wp_step
      have hA' : Mem.load .Mint64 m' Block.nautyActive (zOfInt 0) = some (.Vptr bA Ptrofs.zero) := by
        rw [hu.load _ _ _ (Ne.symm hsep.2.2.1)]; exact hA
      refine Set.wp_addElementGV (ofs := Ptrofs.zero) (c := st j) rfl find_nautyActive hA' haw'
        (by omega) hi rfl (by omega) (by omega) rfl find_nautyBit
        (hbit.unch hu (Ne.symm hsep.2.2.2)) ?_
      intro m'' haw'' hu'' _ hk'' hg''
      simp only [seqPost, Post.after, E0_append]
      have harr'' : ArrayAt m'' .Mint32 bp 0 (ints (initPtn n Search.nautyInf ends)) n :=
        (harr.unch hu (Ne.symm hsep.1)).unch hu'' (Ne.symm hsep.1)
      have hp'' : PTree.get dense.id.«ptn» le' = some (.Vptr bp Ptrofs.zero) := by
        rw [ho _ (by decide)]; exact hptn
      have hej := hlt _ (List.getElem_mem (l := ends) hjl)
      refine wp_toEnd harr'' (by omega) hp'' hi (hstLe j hjl) hej ?_ ?_ hsm ?_
      · rw [hpget _ hej, if_pos (List.getElem_mem hjl)]
      · intro q h1 h2
        rw [hpget q (by omega), if_neg (hgap j hjl q h1 h2)]; decide
      · intro le'' hi'' ho''
        refine ⟨rfl, rfl, j, hjl, rfl, hi'', Set.addW aw' (st j), haw'', ?_, hu.trans hu'',
          hk.trans hk'', fun z hz => hg'' _ (hg z hz), fun x hx => by rw [ho'' x hx, ho x hx]⟩
        rw [actPre_succ ends hjl]
        exact Set.setRep_add hrep' hsj
  · rintro v t e' le' m' ⟨rfl, rfl, j, hjl, rfl, hi, aw', haw', hrep', hu, hk, hg, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hi, typeof, cop, ir_add]
    refine ⟨n - st (j + 1), ?_, by simp, rfl, j + 1, hjl, rfl, ?_, aw', haw', hrep', hu, hk, hg,
      fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩
    · rw [hstS j hjl]; have := hstLe j hjl; have := hlt _ (List.getElem_mem (l := ends) hjl); omega
    · rw [temps_gss, hstS j hjl]; push_cast; rfl

/-- The harness's `ptn` with `ptn[n-1] = 0` written. -/
abbrev ptn1 (n : Nat) (ends : List Nat) : Array Nat := (Harness.harnessPtn n ends).set! (n - 1) 0

theorem ptn1_size (n : Nat) (ends : List Nat) : (ptn1 n ends).size = n := by
  simp [ptn1, Harness.harnessPtn]

theorem ptn1_get {n : Nat} {ends : List Nat} (hlast : n - 1 ∈ ends) {q : Nat} (hq : q < n) :
    (ptn1 n ends)[q]! = if q ∈ ends then 0 else 1 := by
  by_cases hqe : q = n - 1
  · subst hqe
    rw [Array.getElem!_set!_self _ _ _ (by simp [Harness.harnessPtn]; omega), if_pos hlast]
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hqe),
      getElem!_pos (Harness.harnessPtn n ends) q (by simp [Harness.harnessPtn]; omega)]
    simp [Harness.harnessPtn]

open Hex.GraphIso.Nauty in
theorem normP_ptn1 {n : Nat} {ends : List Nat} (hlast : n - 1 ∈ ends) :
    normP (ptn1 n ends) n = initPtn n Search.nautyInf ends := by
  have hs1 : (normP (ptn1 n ends) n).size = n := by rw [normP_size, ptn1_size]
  have hs2 := size_initPtn n Search.nautyInf ends
  apply Array.ext (by rw [hs1, hs2])
  intro i h1 h2
  rw [← getElem!_pos (normP (ptn1 n ends) n) i h1, ← getElem!_pos (initPtn n Search.nautyInf ends) i h2,
    normP_get _ n i (by rw [ptn1_size]; omega), ptn1_get hlast (by omega), getElem!_initPtn]
  rw [hs1] at h1
  by_cases hm : i ∈ ends
  · simp [hm, h1]
  · simp [hm, h1]

theorem countP_mem_range {n : Nat} {ends : List Nat} (hsort : ends.Pairwise (· < ·))
    (hlt : ∀ e ∈ ends, e < n) :
    (List.range n).countP (fun j => decide (j ∈ ends)) = ends.length := by
  rw [List.countP_eq_length_filter]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (List.nodup_range.sublist (List.filter_sublist))
    (hsort.imp (fun h => Nat.ne_of_lt h))]
  intro a
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hlt a h, h⟩⟩

theorem zeros_ptn1 {n : Nat} {ends : List Nat} (hsort : ends.Pairwise (· < ·))
    (hlt : ∀ e ∈ ends, e < n) (hlast : n - 1 ∈ ends) :
    zeros (ptn1 n ends) n = ends.length := by
  rw [zeros, ← countP_mem_range hsort hlt]
  apply List.countP_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [ptn1_get hlast hj]
  by_cases hm : j ∈ ends <;> simp [hm]

open Hex.GraphIso.Nauty in
/-- The `ptn` normalisation and the initial active set (`tPtn`), with
`defaultptn = FALSE` and `active_arg = NULL`. -/
theorem wp_tPtn {Q : Post} {le : temp_env} {m : mem} {bp bA : block} {n M : Nat}
    {ends : List Nat} {aw : Nat → val}
    (hsort : ends.Pairwise (· < ·)) (hlt : ∀ e ∈ ends, e < n) (hlast : n - 1 ∈ ends)
    (hn0 : 0 < n) (hn : n < 1073741824) (hnM : n ≤ 64 * M) (hM0 : 0 < M) (hM : M < 33554432)
    (hopt : PTree.get dense.id.«options» le = some (.Vptr Harness.Block.options Ptrofs.zero))
    (hO : Harness.OptionsAt m)
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr bp Ptrofs.zero))
    (hact : PTree.get dense.id.«active_arg» le = some nullArg)
    (harr : ArrayAt m .Mint32 bp 0 (ints (Harness.harnessPtn n ends)) n)
    (hN : IntAt m Search.Block.n n) (hMm : IntAt m Search.Block.m M)
    (hA : Mem.load .Mint64 m Block.nautyActive (zOfInt 0) = some (.Vptr bA Ptrofs.zero))
    (haw : ArrayAt m .Mint64 bA 0 aw M)
    (hbit : Set.BitTable m Block.nautyBit)
    (hsep : ∀ z ∈ [Search.Block.n, Search.Block.m, Block.nautyActive, Block.nautyBit],
      bp ≠ z ∧ bA ≠ z) (hpA : bp ≠ bA)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bp 0 (ints (initPtn n Search.nautyInf ends)) n →
      PTree.get dense.id.«numcells» le' = some (.Vint (ir ends.length)) →
      (∃ aw' : Nat → Lib.Integers.int64, ArrayAt m' .Mint64 bA 0 (Set.longs aw') M ∧
        SetRep (fun w => bv64 (aw' w)) M (initActive n ends)) →
      Unch m m' (fun z => z = bp ∨ z = bA) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.«i» → x ≠ dense.id.«numcells» → x ≠ dense.id.«es___1» → x ≠ idOf 731 →
        PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tInit Q empty_env le' m') :
    Wp xi ge dense.fn.nauty Nauty.tPtn Q empty_env le m := by
  have hS := fun z hz => hsep z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS
  obtain ⟨⟨hpn, hAn⟩, ⟨hpm, hAm⟩, ⟨hpa, hAa⟩, ⟨hpb, hAb⟩⟩ := hS
  have hhs : (Harness.harnessPtn n ends).size = n := by simp [Harness.harnessPtn]
  simp only [Nauty.tPtn, Nauty.ptnIf, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [eval_optF hopt field_oDefaultptn rfl (by decide) (by decide) hO.defaultptn]
  simp only [typeof]
  rw [show Cfrontend.Cop.bool_val (.Vint (ir 0)) tint m = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  wp_step; wp_step; wp_step
  have hsub : Exec.evalExpr ge empty_env le m
      (.Ebinop .Osub (.Evar dense.id.«nauty:n» tint) (ci 1 tint) tint) = some (.Vint (ir (n - 1 : Nat))) := by
    rw [Exec.evalExpr, Search.eval_gint (e := empty_env) rfl Search.find_n hN]
    simp only [Exec.evalExpr, typeof, cop, ir_sub]
    congr 3; omega
  refine Search.wp_storeV (ofs := Ptrofs.zero) harr (by omega) dense.id.«ptn» hptn _ (n - 1) (by omega)
    hsub rfl (ci 0 tint) 0 rfl rfl ?_
  intro m1 harr1 hu1 hg1
  rw [show upd (ints (Harness.harnessPtn n ends)) (n - 1) (.Vint (ir 0)) = ints (ptn1 n ends) by
    rw [ints_set (by rw [hhs]; omega)]; rfl] at harr1
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
  wp_step
  have hh1 : ∀ j < n, (ptn1 n ends)[j]! < 2147483648 := fun j hj => by
    rw [ptn1_get hlast hj]; split <;> decide
  refine wp_normLoop (ptn1 n ends) (ptn1_size n ends) hn hh1
    (by rw [temps_gso _ _ (by decide)]; exact hptn) (hN.unch hu1 (Ne.symm hpn)) (temps_gss _ _ _)
    harr1 hpn ?_
  intro le2 m2 harr2 hnc2 hu2 hg2 ho2
  rw [normP_ptn1 hlast] at harr2
  rw [zeros_ptn1 hsort hlt hlast] at hnc2
  simp only [seqPost, Post.after, E0_append]
  have hact2 : PTree.get dense.id.«active_arg» le2 = some nullArg := by
    rw [ho2 _ (by decide) (by decide), temps_gso _ _ (by decide)]; exact hact
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Set.pv, hact2, typeof, nullArg]
  rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
      (tptr Cfrontend.Ctypes.Tvoid) m2 = some (.Vlong (Int64.repr (Lib.Integers.Int.signed (ir 0)))) from rfl]
  simp only []
  rw [show Cfrontend.Cop.sem_binary_operation ge.genv_cenv Cfrontend.Cop.Oeq
      (.Vlong (Int64.repr (Lib.Integers.Int.signed (ir 0)))) (tptr tulong)
      (.Vlong (Int64.repr (Lib.Integers.Int.signed (ir 0)))) (tptr Cfrontend.Ctypes.Tvoid) m2 =
      some Vtrue from rfl]
  simp only []
  rw [show Cfrontend.Cop.bool_val Vtrue tint m2 = some true from rfl]
  simp only [ite_true]
  have hu12 : Unch m m2 (· = bp) := hu1.trans hu2
  have hA2 : Mem.load .Mint64 m2 Block.nautyActive (zOfInt 0) = some (.Vptr bA Ptrofs.zero) := by
    rw [hu12.load _ _ _ (Ne.symm hpa)]; exact hA
  have haw2 : ArrayAt m2 .Mint64 bA 0 aw M := haw.unch hu12 (Ne.symm hpA)
  wp_step
  refine Set.wp_emptySetGE (by decide) rfl find_nautyActive hA2 (Ne.symm hAa) haw2 hM0 (by omega)
    (Search.eval_gint (e := empty_env) rfl Search.find_m (hMm.unch hu12 (Ne.symm hpm))) rfl ?_
  intro le3 m3 haw3 hu3 _ _ hg3 ho3
  simp only [seqPost, Post.after, E0_append]
  have hu23 : Unch m m3 (fun z => z = bp ∨ z = bA) :=
    (hu12.mono fun _ h => .inl h).trans (hu3.mono fun _ h => .inr h)
  have hptn3 : PTree.get dense.id.«ptn» le3 = some (.Vptr bp Ptrofs.zero) := by
    rw [ho3 _ (by decide) (by decide), ho2 _ (by decide) (by decide), temps_gso _ _ (by decide)]
    exact hptn
  refine wp_actLoop hsort hlt hlast hn0 hn hnM hM hptn3 (harr2.unch hu3 hpA)
    (hN.unch hu23 (by simp; exact ⟨Ne.symm hpn, Ne.symm hAn⟩)) ?_ haw3 (Set.setRep_zero hnM)
    (hbit.unch hu23 (by simp; exact ⟨Ne.symm hpb, Ne.symm hAb⟩))
    ⟨Ne.symm hpA, hAn, hAa, hAb⟩ ?_
  · rw [hu23.load _ _ _ (by simp; exact ⟨Ne.symm hpa, Ne.symm hAa⟩)]; exact hA
  intro le4 m4 aw4 haw4 hrep4 hu4 hk4 hg4 ho4
  simp only [E0_append]
  refine hQ le4 m4 ((harr2.unch hu3 hpA).unch hu4 hpA) ?_ ⟨aw4, haw4, hrep4⟩
    (hu23.trans (hu4.mono fun _ h => .inr h)) (fun z hz => hg4 _ (hg3 z (hg2 z (hg1 z hz)))) ?_
  · rw [ho4 _ (by decide), ho3 _ (by decide) (by decide)]; exact hnc2
  · intro x h1 h2 h3 h4
    rw [ho4 _ h1, ho3 _ h3 h4, ho2 _ h1 h2, temps_gso _ _ h2]

end NautyVerified.Proofs.Top

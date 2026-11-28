import NautyVerified.Proofs.Set.Global
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
      Keep m m' ba →
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
      ∀ k', k' ≠ es → k' ≠ tmp → PTree.get k' le' = PTree.get k' le)
    (J := fun k t e' le' m' => ∃ k' < k, t = E0 ∧ e = e' ∧ k' ≤ M ∧
      PTree.get es le' = some (.Vptr ba (ptrTo base 8 k')) ∧
      ArrayAt m' .Mint64 ba base (clearedFromV vals k') M ∧ Unch m m' (· = ba) ∧
      Outside m m' ba base (base + 8 * M) ∧ Keep m m' ba ∧
      ∀ k'', k'' ≠ es → k'' ≠ tmp → PTree.get k'' le' = PTree.get k'' le) ?_ ?_ (n := M)
    ⟨rfl, rfl, Nat.le_refl _, temps_gss _ _ _, by
      refine ⟨hb, by rw [h8]; omega, fun i hi => ?_, fun i hi => harr.writable i hi⟩
      simp only [clearedFromV, ite_eq_left hi]; exact harr.load i hi,
      Unch.refl _ _, Outside.refl _ _ _ _, Alloc.Keep.refl _ _, fun k' hk _ => temps_gso _ _ hk⟩
  · rintro k t e' le' m' ⟨rfl, rfl, hk, hes, harr', hu, hout, hkp, hother⟩
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
      exact hQ le' m' harr' hu hout hkp hother
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
        hkp.trans (Alloc.Keep.store hst (by simp only [elemOfs, intOfZ_zOfInt, h8]; omega)), ?_⟩
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

end NautyVerified.Proofs.Top

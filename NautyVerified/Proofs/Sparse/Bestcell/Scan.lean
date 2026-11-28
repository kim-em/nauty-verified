import NautyVerified.Proofs.Sparse.Bestcell.Frame

/-!
# `bestcell_sg`'s cell scan

`wp_cellLoop`: `while (i < n) …` writes the nontrivial cells' starts to
`START = work1`, their sizes to `SIZE = work1 + n/2` and every vertex's
cell index (or `n`) to `NNTCELL = work2`, as `cells` computes them; `run
(n - i)` of the scan is the invariant. `wp_markLoop` is the inner
`do NNTCELL[lab[j]] = nnt; while (ptn[j++] > level);` with `size_t j`.
-/

namespace NautyVerified.Proofs.Sparse.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse NautyVerified.Program
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat cast_l_i)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty (cellEnd)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

theorem lr_sub {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 63) :
    Lib.Integers.Int64.sub (lr a) (lr b) = lr ((a - b : Nat) : Int) := by
  apply bv64_inj.1
  rw [bv64_sub]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, Alloc.toNat_lr ha, Alloc.toNat_lr (by omega), Alloc.toNat_lr (by omega)]
  omega

theorem ir_lr {k : Nat} (hk : k < 2147483648) :
    Lib.Integers.Int.repr (Lib.Integers.Int64.unsigned (lr k)) = ir k := by
  apply bv32_inj.1
  rw [bv32_repr, intOfZ_Int64_unsigned, Alloc.toNat_lr (by omega), bv32_repr, intOfZ_zOfInt]

theorem sub_li (ce : composite_env) (m : mem) (a b : attr) (u : Lib.Integers.int64)
    (y : Lib.Integers.int) :
    Cfrontend.Cop.sem_binary_operation ce .Osub (.Vlong u) (Tlong .Unsigned a) (.Vint y)
      (Tint .I32 .Signed b) m =
      some (.Vlong (Lib.Integers.Int64.sub u (Cfrontend.Cop.cast_int_long .Signed y))) := rfl

/-- The temporaries the scan sets. -/
def ScanLocal (x : ident) : Prop := x = id.i ∨ x = id.j ∨ x = id.nnt ∨ x = id.tj

instance (x : ident) : Decidable (ScanLocal x) := by unfold ScanLocal; infer_instance

theorem args_not_scan : ∀ x, Args x → ¬ ScanLocal x := by
  intro x hx hs
  rcases hs with rfl | rfl | rfl | rfl <;> revert hx <;> decide

/-- `NNTCELL` after the do-while has marked positions `first .. j-1` with `idx`. -/
def marked (lab : Array Nat) (first idx : Nat) (W : Nat → val) (j : Nat) (v : Nat) : val :=
  if ∃ p < j, first ≤ p ∧ lab[p]! = v then .Vint (ir (idx : Int)) else W v

theorem marked_succ (lab : Array Nat) (first idx : Nat) (W : Nat → val) (j : Nat) (hj : first ≤ j) :
    upd (marked lab first idx W j) lab[j]! (.Vint (ir (idx : Int))) = marked lab first idx W (j + 1) := by
  funext v
  simp only [upd, marked]
  by_cases hv : v = lab[j]!
  · rw [ite_eq_left hv, ite_eq_left ⟨j, by omega, hj, hv.symm⟩]
  · rw [ite_eq_right hv]
    have : (∃ p < j + 1, first ≤ p ∧ lab[p]! = v) ↔ (∃ p < j, first ≤ p ∧ lab[p]! = v) :=
      ⟨fun ⟨p, h2, h1, h3⟩ => ⟨p, by
        rcases Nat.lt_or_ge p j with h | h
        · exact h
        · exact absurd (show p = j by omega ▸ h3).symm hv, h1, h3⟩,
       fun ⟨p, h2, h1, h3⟩ => ⟨p, by omega, h1, h3⟩⟩
    by_cases hex : ∃ p < j, first ≤ p ∧ lab[p]! = v
    · rw [ite_eq_left (this.2 hex), ite_eq_left hex]
    · rw [ite_eq_right (fun h => hex (this.1 h)), ite_eq_right hex]

section
variable {n : Nat} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {bv : block} {vo : ptrofs}
  {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {bl : block} {lofs : ptrofs}
  {lab : Array Nat} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {level : Nat}
  {w : Fin 4 → block} {o1b : ptrofs}

/-- `ptn[a] > level` for an `int` index. -/
theorem eval_ptnGt (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (c : Nat) (hc : c < n) (hi : PTree.get id.i le = some (.Vint (ir c))) :
    Exec.evalExpr sge empty_env le m (.Ebinop .Ogt (iat id.ptn (tv id.i)) (tv id.level) tint) =
      some (Val.of_bool (decide (level < ptn[c]!))) := by
  have hpe := eval_tidx (ge := sge) (e := empty_env) (ty := tint) h.parr (by have := h.nlt; omega) h.hptn rfl rfl
    (tv id.i) c hc hi rfl
  have := h.psmall c hc
  have := h.levlt
  rw [Exec.evalExpr, hpe, show Exec.evalExpr sge empty_env le m (tv id.level) = _ from h.hlev]
  simp only [ints, typeof, cop]
  rw [ir_lt (a := (level : Int)) (b := (ptn[c]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  congr 2
  apply decide_eq_decide.2; omega

/-- `ptn[a] > level` for an `unsigned long` index. -/
theorem eval_ptnGtL (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (c : Nat) (hc : c < n) (hi : PTree.get id.tj le = some (.Vlong (lr c))) :
    Exec.evalExpr sge empty_env le m (.Ebinop .Ogt (.Ederef (.Ebinop .Oadd
      (.Etempvar id.ptn (tptr tint)) (tl id.tj) (tptr tint)) tint) (tv id.level) tint) =
      some (Val.of_bool (decide (level < ptn[c]!))) := by
  have hpe := eval_idx_l (ge := sge) (e := empty_env) (pe := .Etempvar id.ptn (tptr tint)) h.parr
    (by have := h.nlt; omega) (by simp only [Exec.evalExpr]; exact h.hptn) rfl rfl rfl
    (tl id.tj) c hc hi rfl
  have := h.psmall c hc
  have := h.levlt
  rw [Exec.evalExpr, hpe, show Exec.evalExpr sge empty_env le m (tv id.level) = _ from h.hlev]
  simp only [ints, typeof, cop]
  rw [ir_lt (a := (level : Int)) (b := (ptn[c]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  congr 2
  apply decide_eq_decide.2; omega

/-- `do NNTCELL[lab[j]] = nnt; while (ptn[j++] > level);` -/
abbrev markLoop : statement :=
  .Sloop
    (sk (.Sassign (gat id.work2 (.Ederef (.Ebinop .Oadd (.Etempvar id.lab (tptr tint)) (tl id.j)
      (tptr tint)) tint)) (tv id.nnt)))
    (.Ssequence
      (.Ssequence
        (sk (.Sset id.tj (tl id.j)))
        (.Sset id.j (.Ebinop .Oadd (tl id.tj) (ci 1 tint) tulong)))
      (.Sifthenelse (.Ebinop .Ogt (.Ederef (.Ebinop .Oadd (.Etempvar id.ptn (tptr tint)) (tl id.tj)
        (tptr tint)) tint) (tv id.level) tint) .Sskip .Sbreak))

theorem args_ne_j : ∀ x, Args x → x ≠ id.j ∧ x ≠ id.tj := by
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem wp_markLoop {Q : Logic.Post} {W : Nat → val} {first idx : Nat}
    (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (hW : ArrayAt m .Mint32 (w 1) 0 W n) (hf : first < n) (hj : PTree.get id.j le = some (.Vlong (lr first)))
    (hnnt : PTree.get id.nnt le = some (.Vint (ir idx)))
    (hQ : ∀ le' m', PTree.get id.j le' = some (.Vlong (lr ((cellEnd ptn level first + 1 : Nat) : Int))) →
      PTree.get id.tj le' = some (.Vlong (lr ((cellEnd ptn level first : Nat) : Int))) →
      ArrayAt m' .Mint32 (w 1) 0 (marked lab first idx W (cellEnd ptn level first + 1)) n →
      Unch m m' (· = w 1) → Keep m m' (w 1) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ id.j → x ≠ id.tj → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F markLoop Q empty_env le m := by
  have sp := Spec.cellEnd_spec h.psize hf h.plast
  have hnlt := h.nlt
  obtain ⟨ce, hce⟩ : ∃ ce, ce = cellEnd ptn level first := ⟨_, rfl⟩
  rw [← hce] at sp hQ
  let A := fun (k jv : Nat) (le' : temp_env) (m' : mem) =>
    PTree.get id.j le' = some (.Vlong (lr jv)) ∧
    ArrayAt m' .Mint32 (w 1) 0 (marked lab first idx W k) n ∧ Unch m m' (· = w 1) ∧
    Keep m m' (w 1) ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    ∀ x, x ≠ id.j → x ≠ id.tj → PTree.get x le' = PTree.get x le
  refine wp_loop (I := fun v t e' le' m' => t = E0 ∧ e' = empty_env ∧ ∃ j', first ≤ j' ∧ j' ≤ ce ∧
      v = ce - j' ∧ A j' j' le' m')
    (J := fun v t e' le' m' => t = E0 ∧ e' = empty_env ∧ ∃ j', first ≤ j' ∧ j' ≤ ce ∧
      v = ce - j' ∧ A (j' + 1) j' le' m') ?_ ?_ (n := ce - first)
    ⟨rfl, rfl, first, Nat.le_refl _, sp.1, rfl, hj, hW.congr fun v _ => by
      simp only [marked]
      rw [ite_eq_right]
      rintro ⟨p, h1, h2, -⟩
      omega, Unch.refl _ _, Keep.refl _ _, fun _ h => h, fun _ _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, j', hj1, hj2, rfl, hjv, harr', hu, hk, hg, ho⟩
    have hf' := (h.unch (hu.mono fun _ hz => ⟨1, hz⟩)).temps (le' := le')
      fun x hx => ho x (args_ne_j x hx).1 (args_ne_j x hx).2
    have hnnt' : PTree.get id.nnt le' = some (.Vint (ir idx)) := by
      rw [ho _ (by decide) (by decide)]; exact hnnt
    wp_step; wp_step
    refine wp_idx_store (pe := .Evar id.work2 (tptr tint)) (ofs := Ptrofs.zero) harr' (by omega)
      (eval_gvar (k := 1) find_work2 (hf'.wptr 1)) rfl rfl rfl _ lab[j']! (h.lsmall j' (by omega))
      (eval_idx_l (pe := .Etempvar id.lab (tptr tint)) hf'.larr (by omega)
        (by simp only [Exec.evalExpr]; exact hf'.hlab) rfl rfl rfl (tl id.j) j' (by omega) hjv rfl)
      rfl (tv id.nnt) tint rfl (.Vint (ir idx)) (.Vint (ir idx))
      (by simp only [Exec.evalExpr]; exact hnnt') rfl rfl ?_
    intro m'' harr'' hu' hk' hg'
    refine ⟨by simp, rfl, j', hj1, hj2, rfl, hjv, ?_, hu.trans hu', hk.trans hk',
      fun z hz => hg' _ (hg _ hz), ho⟩
    rw [← marked_succ _ _ _ _ _ hj1]
    exact harr''
  · rintro v t e' le' m' ⟨rfl, rfl, j', hj1, hj2, rfl, hjv, harr', hu, hk, hg, ho⟩
    have hf' := (h.unch (hu.mono fun _ hz => ⟨1, hz⟩)).temps (le' := le')
      fun x hx => ho x (args_ne_j x hx).1 (args_ne_j x hx).2
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hjv]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop, Alloc.add_lr_one, E0_append]
    let le2 := PTree.set id.j (.Vlong (lr ((j' : Int) + 1))) (PTree.set id.tj (.Vlong (lr j')) le')
    have ho2 : ∀ x, x ≠ id.j → x ≠ id.tj → PTree.get x le2 = PTree.get x le' := fun x a b => by
      simp only [le2]; rw [temps_gso _ _ a, temps_gso _ _ b]
    have hf2 := hf'.temps (le' := le2) fun x hx => ho2 x (args_ne_j x hx).1 (args_ne_j x hx).2
    have htj : PTree.get id.tj le2 = some (.Vlong (lr j')) := by
      simp only [le2]; rw [temps_gso _ _ (by decide), temps_gss]
    apply wp_if_eval
    rw [eval_ptnGtL hf2 j' (by omega) htj]
    simp only [typeof, cop]
    by_cases hlt : level < ptn[j']!
    · have hjc : j' < ce := by
        rcases Nat.lt_or_ge j' ce with h' | h'
        · exact h'
        · have : j' = ce := by omega
          subst this; have := sp.2.2.1; omega
      rw [ite_eq_left (by simpa using hlt)]
      apply wp_skip
      refine ⟨ce - (j' + 1), by omega, by simp, rfl, j' + 1, by omega, by omega, rfl, ?_, harr', hu, hk,
        hg, fun x a b => by rw [ho2 x a b, ho x a b]⟩
      simp only [le2, temps_gss]; push_cast; rfl
    · have hjc : j' = ce := by
        rcases Nat.lt_or_ge j' ce with h' | h'
        · exact absurd (sp.2.2.2 j' hj1 h') hlt
        · omega
      subst hjc
      rw [ite_eq_right (by simpa using hlt)]
      apply wp_break
      simp only [E0_append]
      refine hQ le2 m' ?_ htj harr' hu hk hg fun x a b => by rw [ho2 x a b, ho x a b]
      simp only [le2, temps_gss]; push_cast; rfl

/-- The C state of the scan at `s`: `START`, `SIZE` and `NNTCELL` of the scanned positions. -/
def ScanAt (n : Nat) (lab : Array Nat) (s : Cells) (W1 W2 : Nat → val) : Prop :=
  (∀ k < s.starts.size, W1 k = .Vint (ir (s.starts[k]! : Int)) ∧
    W1 (n / 2 + k) = .Vint (ir (s.sizes[k]! : Int))) ∧
  ∀ p < s.first, W2 lab[p]! = .Vint (ir (s.nntcell[lab[p]!]! : Int))

/-- The scan's state at `s`, from memory `m` and temporaries `le` at its start. -/
def StAt (m m' : mem) (le le' : temp_env) (n : Nat) (lab ptn : Array Nat) (level : Nat)
    (w : Fin 4 → block) (s : Cells) : Prop :=
  ∃ W1 W2, PTree.get id.i le' = some (.Vint (ir (s.first : Int))) ∧
    PTree.get id.nnt le' = some (.Vint (ir (s.starts.size : Int))) ∧
    ArrayAt m' .Mint32 (w 0) 0 W1 n ∧ ArrayAt m' .Mint32 (w 1) 0 W2 n ∧ ScanAt n lab s W1 W2 ∧
    Mod m m' w ∧ (∀ z, Mem.valid_block m z → Mem.valid_block m' z) ∧
    (∀ x, ¬ ScanLocal x → PTree.get x le' = PTree.get x le) ∧ Good n lab s ∧
    cellRun n lab ptn level (n - s.first) s = cells n lab ptn level

theorem run_step (hs : ptn.size = n) (hlast : ptn[n - 1]! ≤ level) {s : Cells} (hf : s.first < n)
    (hr : cellRun n lab ptn level (n - s.first) s = cells n lab ptn level) :
    cellRun n lab ptn level (n - (cellStep lab ptn level s).first) (cellStep lab ptn level s) =
      cells n lab ptn level := by
  have h1 := cellStep_first lab hs hlast hf
  rw [← hr, show n - s.first = (n - s.first - 1) + 1 by omega, cellRun_succ _ hf]
  exact cellRun_fuel hs hlast _ _ _ (Nat.le_refl _) (by omega)

theorem StAt.frame (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    {m' : mem} {le' : temp_env} {s : Cells} (hs : StAt m m' le le' n lab ptn level w s) :
    Frame m' le' G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b := by
  obtain ⟨-, -, -, -, -, -, -, hmod, -, ho, -⟩ := hs
  exact (h.unch hmod.1).temps fun x hx => ho x (args_not_scan x hx)

/-- `NNTCELL[lab[i]] = n; ++i;` at a singleton. -/
theorem wp_single {Q : Logic.Post} {m' : mem} {le' : temp_env} {s : Cells}
    (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (hs : StAt m m' le le' n lab ptn level w s) (hf : s.first < n) (hp : ptn[s.first]! ≤ level)
    (hQ : ∀ le'' m'', StAt m m'' le le'' n lab ptn level w (cellStep lab ptn level s) →
      Q.normal E0 empty_env le'' m'') :
    Wp xi sge F single Q empty_env le' m' := by
  have hf' := hs.frame h
  obtain ⟨W1, W2, hi, hnnt, hw1, hw2, ⟨hS1, hS2⟩, hmod, hg, ho, hgood, hrun⟩ := hs
  have hnlt := h.nlt
  have hlf := h.lsmall _ hf
  wp_step; wp_step; wp_step
  refine wp_idx_store (pe := .Evar id.work2 (tptr tint)) (ofs := Ptrofs.zero) hw2 (by omega)
    (eval_gvar (k := 1) find_work2 (hf'.wptr 1)) rfl rfl rfl _ lab[s.first]! hlf
    (eval_tidx (ty := tint) hf'.larr (by omega) hf'.hlab rfl rfl (tv id.i) s.first hf hi rfl)
    rfl (tv id.n) tint rfl (.Vint (ir n)) (.Vint (ir n)) (by simp only [Exec.evalExpr]; exact hf'.hn)
    rfl rfl ?_
  intro m'' hw2' hu' hk' hg'
  wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hi, typeof, cop, ir_add]
  refine hQ _ m'' ⟨W1, _, ?_, ?_, hw1.unch hu' (hf'.wdist 0 1 (by decide)), hw2', ⟨?_, ?_⟩,
    hmod.trans (hf'.mod 1 hu' hk'), fun z hz => hg' _ (hg _ hz), ?_,
    good_single hgood h.psize hf h.plast hp, run_step h.psize h.plast hf hrun⟩
  · rw [cellStep_single h.psize hf h.plast hp, temps_gss]; push_cast; rfl
  · rw [cellStep_single h.psize hf h.plast hp, temps_gso _ _ (by decide)]; exact hnnt
  · rw [cellStep_single h.psize hf h.plast hp]; exact hS1
  · rw [cellStep_single h.psize hf h.plast hp]
    intro p hp'
    simp only at hp' ⊢
    by_cases hpf : p = s.first
    · subst hpf
      rw [upd_same, hgood.rest _ (Nat.le_refl _) hf]
    · rw [upd_ne _ _ (fun he => hpf (h.linj _ _ (by omega) hf he))]
      exact hS2 p (by omega)
  · intro x hx
    rw [temps_gso _ _ (fun he => hx (.inl he)), ho x hx]

/-- The nontrivial cell at `i`. -/
theorem wp_nontriv {Q : Logic.Post} {m' : mem} {le' : temp_env} {s : Cells}
    (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (hs : StAt m m' le le' n lab ptn level w s) (hf : s.first < n) (hp : level < ptn[s.first]!)
    (hQ : ∀ le'' m'', StAt m m'' le le'' n lab ptn level w (cellStep lab ptn level s) →
      Q.normal E0 empty_env le'' m'') :
    Wp xi sge F nontriv Q empty_env le' m' := by
  have hf' := hs.frame h
  obtain ⟨W1, W2, hi, hnnt, hw1, hw2, ⟨hS1, hS2⟩, hmod, hg, ho, hgood, hrun⟩ := hs
  have hnlt := h.nlt
  have sp := Spec.cellEnd_spec h.psize hf h.plast
  have hgt := cellEnd_gt h.psize hf h.plast hp
  obtain ⟨ce, hce⟩ : ∃ ce, ce = cellEnd ptn level s.first := ⟨_, rfl⟩
  rw [← hce] at sp hgt
  have hhalf := hgood.half
  have hsz : s.starts.size + 1 ≤ n / 2 := by omega
  -- `START[nnt] = i;`
  wp_step; wp_step; wp_step
  refine wp_idx_store (pe := .Evar id.work1 (tptr tint)) (ofs := Ptrofs.zero) hw1 (by omega)
    (eval_gvar (k := 0) find_work1 (hf'.wptr 0)) rfl rfl rfl (tv id.nnt) s.starts.size (by omega)
    (by simp only [Exec.evalExpr]; exact hnnt) rfl (tv id.i) tint rfl (.Vint (ir s.first)) (.Vint (ir s.first))
    (by simp only [Exec.evalExpr]; exact hi) rfl rfl ?_
  intro m1 hw1a hu1 hk1 hg1
  -- `j = i;`
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hi, typeof, cop, E0_append]
  rw [cast_int_long_ir (a := (s.first : Int)) ⟨by omega, by omega⟩]
  have hf1 := (hf'.unch (hu1.mono fun _ hz => ⟨0, hz⟩)).temps (le' := PTree.set id.j (.Vlong (lr s.first)) le')
    fun x hx => temps_gso _ _ (args_ne_j x hx).1
  wp_step
  refine wp_markLoop (idx := s.starts.size) hf1 (hw2.unch hu1 (hf'.wdist 1 0 (by decide))) hf
    (temps_gss _ _ _) (by rw [temps_gso _ _ (by decide)]; exact hnnt) ?_
  rw [← hce]
  intro le2 m2 hj2 htj2 hw2a hu2 hk2 hg2 ho2
  have hf2 := (hf1.unch (hu2.mono fun _ hz => ⟨1, hz⟩)).temps (le' := le2)
    fun x hx => ho2 x (args_ne_j x hx).1 (args_ne_j x hx).2
  have hi2 : PTree.get id.i le2 = some (.Vint (ir s.first)) := by
    rw [ho2 _ (by decide) (by decide), temps_gso _ _ (by decide)]; exact hi
  have hnnt2 : PTree.get id.nnt le2 = some (.Vint (ir s.starts.size)) := by
    rw [ho2 _ (by decide) (by decide), temps_gso _ _ (by decide)]; exact hnnt
  -- `SIZE[nnt] = j - i;`
  simp only [E0_append]
  wp_step; wp_step; wp_step
  refine wp_store_off (pe := .Etempvar id.work1b (tptr tint)) (off := n / 2)
    (hw1a.unch hu2 (hf'.wdist 0 1 (by decide))) (by omega)
    (by simp only [Exec.evalExpr]; exact hf2.h1b) rfl h.o1b (tv id.nnt) s.starts.size (by omega)
    (by simp only [Exec.evalExpr]; exact hnnt2) rfl _ tulong rfl
    (.Vlong (lr ((ce + 1 - s.first : Nat) : Int))) (.Vint (ir ((ce + 1 - s.first : Nat) : Int)))
    (by
      simp only [Exec.evalExpr, hj2, hi2, typeof]
      rw [sub_li, cast_int_long_ir (a := (s.first : Int)) ⟨by omega, by omega⟩, lr_sub (by omega) (by omega)])
    (by simp only [cop]; rw [ir_lr (by omega)]) rfl ?_
  intro m3 hw1b hu3 hk3 hg3
  -- `++nnt; i = j;`
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hnnt2, typeof, cop, ir_add]
  wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gso _ _ (show id.j ≠ id.nnt by decide), hj2, typeof, cop]
  rw [ir_lr (by omega)]
  have hstep := cellStep_nontriv (lab := lab) h.psize hf h.plast hp
  rw [← hce] at hstep
  have hsizes := hgood.sizes
  have hnsz := hgood.nsize
  refine hQ _ m3 ⟨_, _, ?_, ?_, hw1b, hw2a.unch hu3 (hf'.wdist 1 0 (by decide)), ⟨?_, ?_⟩,
    hmod.trans (((hf'.mod 0 hu1 hk1).trans (hf1.mod 1 hu2 hk2)).trans (hf2.mod 0 hu3 hk3)),
    fun z hz => hg3 _ (hg2 _ (hg1 _ (hg _ hz))), ?_,
    good_nontriv hgood h.psize hf h.plast hp h.lsmall h.linj, run_step h.psize h.plast hf hrun⟩
  · rw [hstep, temps_gss]
  · rw [hstep, temps_gso _ _ (by decide), temps_gss]; simp only [Array.size_push]; push_cast; rfl
  · rw [hstep]
    intro k hk
    simp only [Array.size_push] at hk ⊢
    rw [push_get, push_get, hsizes]
    by_cases hks : k < s.starts.size
    · rw [ite_eq_left hks, ite_eq_left hks]
      obtain ⟨a, b⟩ := hS1 k hks
      exact ⟨by rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]; exact a,
        by rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]; exact b⟩
    · have hk' : k = s.starts.size := by omega
      subst hk'
      rw [ite_eq_right hks, ite_eq_right hks, ite_eq_left rfl, ite_eq_left rfl]
      refine ⟨by rw [upd_ne _ _ (by omega), upd_same], ?_⟩
      rw [upd_same, show ce + 1 - s.first = ce - s.first + 1 by omega]
  · rw [hstep]
    intro p hp'
    simp only at hp' ⊢
    simp only [marked]
    rw [mark_get _ _ _ _ _ (by rw [hnsz]; exact h.lsmall p (by omega))]
    have hne : ∀ p', p' < n → lab[p']! = lab[p]! → p' = p := fun p' hp'n he =>
      h.linj _ _ hp'n (by omega) he
    by_cases hpf : s.first ≤ p
    · rw [ite_eq_left ⟨p, hp', hpf, rfl⟩, ite_eq_left ⟨p, List.mem_range'_1.2 ⟨hpf, by omega⟩, rfl⟩]
    · rw [ite_eq_right (by rintro ⟨p', h1, h2, h3⟩; have := hne p' (by omega) h3; omega),
        ite_eq_right (by
          rintro ⟨j, hj, he⟩
          rw [List.mem_range'_1] at hj
          have := hne j (by omega) he
          omega)]
      exact hS2 p (by omega)
  · intro x hx
    rw [temps_gso _ _ (fun he => hx (.inl he)), temps_gso _ _ (fun he => hx (.inr (.inr (.inl he)))),
      ho2 x (fun he => hx (.inr (.inl he))) (fun he => hx (.inr (.inr (.inr he)))),
      temps_gso _ _ (fun he => hx (.inr (.inl he))), ho x hx]

/-- The cell scan from `i = nnt = 0`. -/
theorem wp_cellLoop {Q : Logic.Post} {W1 W2 : Nat → val}
    (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (hw1 : ArrayAt m .Mint32 (w 0) 0 W1 n) (hw2 : ArrayAt m .Mint32 (w 1) 0 W2 n)
    (hi : PTree.get id.i le = some (.Vint (ir 0))) (hnnt : PTree.get id.nnt le = some (.Vint (ir 0)))
    (hQ : ∀ le' m' W1' W2', ArrayAt m' .Mint32 (w 0) 0 W1' n → ArrayAt m' .Mint32 (w 1) 0 W2' n →
      (∀ k < (cells n lab ptn level).starts.size,
        W1' k = .Vint (ir ((cells n lab ptn level).starts[k]! : Int)) ∧
        W1' (n / 2 + k) = .Vint (ir ((cells n lab ptn level).sizes[k]! : Int))) →
      (∀ v < n, W2' v = .Vint (ir ((cells n lab ptn level).nntcell[v]! : Int))) →
      PTree.get id.nnt le' = some (.Vint (ir ((cells n lab ptn level).starts.size : Int))) →
      Good n lab (cells n lab ptn level) → Mod m m' w →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, ¬ ScanLocal x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F cellLoop Q empty_env le m := by
  have hnlt := h.nlt
  refine wp_loop (I := fun v t e' le' m' => t = E0 ∧ e' = empty_env ∧ ∃ s, v = n - s.first ∧
      StAt m m' le le' n lab ptn level w s)
    (J := fun v t e' le' m' => t = E0 ∧ e' = empty_env ∧ ∃ s, n - s.first < v ∧
      StAt m m' le le' n lab ptn level w s) ?_ ?_ (n := n - 0)
    ⟨rfl, rfl, ⟨#[], #[], Array.replicate n n, 0⟩, rfl, W1, W2, hi, hnnt, hw1, hw2,
      ⟨fun k hk => by simp at hk, fun p hp => by simp at hp⟩, Mod.refl _ _, fun _ h => h,
      fun _ _ => rfl, good_start h.lsmall, by rw [Nat.sub_zero]; rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, s, rfl, hs⟩
    have hf' := hs.frame h
    have hi' : PTree.get id.i le' = some (.Vint (ir (s.first : Int))) := hs.choose_spec.choose_spec.1
    have hfle := hs.choose_spec.choose_spec.2.2.2.2.2.2.2.2.1.fle
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hi', hf'.hn, typeof, cop]
    rw [ir_lt (a := (s.first : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hfn : s.first < n
    · rw [ite_eq_left (by simpa using hfn)]
      apply wp_skip
      wp_step; wp_step
      apply wp_if_eval
      rw [eval_ptnGt hf' s.first hfn hi']
      simp only [typeof, cop]
      have hlt := cellStep_first lab h.psize h.plast hfn
      by_cases hp : level < ptn[s.first]!
      · rw [ite_eq_left (by simpa using hp)]
        exact wp_nontriv h hs hfn hp fun le'' m'' hs' => ⟨by simp, rfl, _, by omega, hs'⟩
      · rw [ite_eq_right (by simpa using hp)]
        exact wp_single h hs hfn (by omega) fun le'' m'' hs' => ⟨by simp, rfl, _, by omega, hs'⟩
    · rw [ite_eq_right (by simpa using hfn)]
      apply wp_break
      simp only [E0_append]
      obtain ⟨W1', W2', -, hnnt', hw1', hw2', ⟨hS1, hS2⟩, hmod, hg, ho, hgood, hrun⟩ := hs
      have hsc : s = cells n lab ptn level := by rw [← hrun, show n - s.first = 0 by omega]; rfl
      subst hsc
      exact hQ le' m' W1' W2' hw1' hw2' hS1 (fun v hv => by
        obtain ⟨p, hp, rfl⟩ := h.lonto v hv
        exact hS2 p (by omega)) hnnt' hgood hmod hg ho
  · rintro v t e' le' m' ⟨rfl, rfl, s, hlt, hs⟩
    apply wp_skip
    exact ⟨n - s.first, hlt, by simp, rfl, s, rfl, hs⟩

end

end NautyVerified.Proofs.Sparse.Bestcell

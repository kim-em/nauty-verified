import NautyVerified.Proofs.Targetcell.Syntax
import NautyVerified.Proofs.Bestcell.Satisfies

/-!
# `targetcell` meets its specification

`targetcellSpec`: with a hint below `n`, naugraph.c's `targetcell` returns
HexGraphIso's `targetcell ⟨g⟩ lab ptn level tcLevel hint`, calling `bestcell`
through its proved specification when `level ≤ tc_level`.
-/

namespace NautyVerified.Proofs.Targetcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Spec.Bestcell
open NautyVerified.Proofs.Bestcell (Pre Post bestcellSpec bestcell_satisfies ptnAt)
open NautyVerified.Proofs.Updatecan (tv)
open Hex.GraphIso.Nauty (VSet cells cellEnd)

def targetcellSpec {n : Nat} (bg : block) (gofs : ptrofs) (gw : Nat → Lib.Integers.int64)
    (grows : Array (VSet n)) (bl : block) (lofs : ptrofs) (lab : Array Nat) (bp : block)
    (pofs : ptrofs) (ptn : Array Nat) (level tcLevel : Nat) (dg : Lib.Integers.int) (hint : Int)
    (M capP : Nat) (bP : block) (capS : Nat) (bS : block) (capB : Nat) (bB : block) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bl lofs, .Vptr bp pofs, .Vint (ir level),
      .Vint (ir tcLevel), .Vint dg, .Vint (ir hint), .Vint (ir M), .Vint (ir n)] ∧
    Pre m bg gofs gw grows bl lofs lab bp pofs ptn level M capP bP capS bS capB bB ∧
    hint < n ∧ -2147483648 ≤ hint ∧ tcLevel < 2147483648
  post _ m t v m' := t = E0 ∧
    v = .Vint (ir (Hex.GraphIso.Nauty.targetcell ⟨grows⟩ lab ptn level tcLevel hint : Int)) ∧
    Post m m' capP bP capS bS capB bB

def entryTemps (bg : block) (gofs : ptrofs) (bl : block) (lofs : ptrofs) (bp : block)
    (pofs : ptrofs) (level tcLevel : Nat) (dg : Lib.Integers.int) (hint : Int) (M n : Nat) :
    temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.hint (.Vint (ir hint)) (PTree.set id.digraph (.Vint dg)
      (PTree.set id.tc_level (.Vint (ir tcLevel)) (PTree.set id.level (.Vint (ir level))
        (PTree.set id.ptn (.Vptr bp pofs) (PTree.set id.lab (.Vptr bl lofs)
          (PTree.set id.g (.Vptr bg gofs)
            (create_undef_temps Source.dense.fn.targetcell.fn_temps)))))))))

theorem cast_bool (b : Bool) (m : mem) {a a' : Cfrontend.Ctypes.attr} :
    Cfrontend.Cop.sem_cast (Val.of_bool b) (.Tint .I32 .Signed a) (.Tint .IBool .Signed a') m =
      some (Val.of_bool b) := by
  cases b <;> rfl

/-- HexGraphIso's test for keeping the hint. -/
abbrev HintOK (ptn : Array Nat) (level : Nat) (hint : Int) : Prop :=
  hint ≥ 0 ∧ ptn[hint.toNat]! > level ∧ ((hint == 0) = true ∨ ptn[hint.toNat - 1]! ≤ level)

theorem wp_hintTest {xi : ExternalCalls} {ge : genv} {f : function} {Q : Post} {le : temp_env}
    {m : mem} {s : statement} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {n level : Nat} {hint : Int}
    (hptn : PTree.get id.ptn le = some (.Vptr bp pofs))
    (harr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n)
    (hn : n < 2147483648) (hlev : PTree.get id.level le = some (.Vint (ir level)))
    (hlevlt : level < 2147483648) (hsmall : ∀ x < n, ptn[x]! < 2147483648)
    (hhint : PTree.get id.hint le = some (.Vint (ir hint))) (hhn : hint < n)
    (hh0 : -2147483648 ≤ hint)
    (hQ : ∀ le', PTree.get id.t7 le' = some (Val.of_bool (decide (HintOK ptn level hint))) →
      (∀ x, x ≠ id.t6 → x ≠ id.t7 → PTree.get x le' = PTree.get x le) →
      Wp xi ge f s Q empty_env le' m) :
    Wp xi ge f (.Ssequence hintTest s) Q empty_env le m := by
  have hpe : ∀ (le' : temp_env) (a : expr) (c : Nat), c < n →
      Exec.evalExpr ge empty_env le' m a = some (.Vint (ir c)) → typeof a = tint →
      PTree.get id.ptn le' = some (.Vptr bp pofs) →
      PTree.get id.level le' = some (.Vint (ir level)) →
      ∀ op, Exec.evalExpr ge empty_env le' m (.Ebinop op (ptnAt a) (tv id.level) tint) =
        Cfrontend.Cop.sem_binary_operation ge.genv_cenv op (.Vint (ir (ptn[c]! : Int))) tint
          (.Vint (ir level)) tint m := by
    intro le' a c hc ha hty hp hl op
    rw [Exec.evalExpr, eval_at (ge := ge) (e := empty_env) harr hn id.ptn hp a c hc ha hty,
      show Exec.evalExpr ge empty_env le' m (tv id.level) = _ from hl]
    rfl
  have hgt : ∀ c, c < n → Cfrontend.Cop.sem_binary_operation ge.genv_cenv .Ogt
      (.Vint (ir (ptn[c]! : Int))) tint (.Vint (ir level)) tint m =
        some (Val.of_bool (decide (level < ptn[c]!))) := by
    intro c hc
    have := hsmall c hc
    simp only [cop]
    rw [ir_lt (a := (level : Int)) (b := (ptn[c]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    congr 2; apply decide_eq_decide.2; omega
  have hle : ∀ c, c < n → Cfrontend.Cop.sem_binary_operation ge.genv_cenv .Ole
      (.Vint (ir (ptn[c]! : Int))) tint (.Vint (ir level)) tint m =
        some (Val.of_bool (decide (ptn[c]! ≤ level))) := by
    intro c hc
    have := hsmall c hc
    simp only [cop]
    rw [ir_lt (a := (level : Int)) (b := (ptn[c]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    congr 2
    by_cases h : ptn[c]! ≤ level <;> simp [h] <;> omega
  wp_step; wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hhint, typeof, cop]
  rw [ir_lt (a := hint) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
  by_cases hs : 0 ≤ hint
  · obtain ⟨h, rfl⟩ : ∃ h : Nat, hint = h := ⟨hint.toNat, by omega⟩
    have hhn' : h < n := by omega
    rw [ite_eq_left (by simp)]
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, hpe le (tv id.hint) h hhn' hhint rfl hptn hlev, hgt h hhn']
    simp only [typeof, cop, cast_bool, E0_append]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    by_cases h1 : level < ptn[h]!
    · rw [show decide (level < ptn[h]!) = true by simpa using h1]
      rw [ite_eq_left rfl]
      wp_step; wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gso _ _ (show id.hint ≠ id.t6 by decide), hhint, typeof, cop]
      rw [ir_eq (a := (h : Int)) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
      by_cases h0 : h = 0
      · subst h0
        rw [ite_eq_left (by simp)]
        wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, typeof, cop, E0_append]
        refine hQ _ ?_ fun x h6 h7 => by rw [temps_gso _ _ h7, temps_gso _ _ h6]
        rw [temps_gss, decide_eq_true ⟨by omega, by simpa using h1, .inl rfl⟩]; rfl
      · rw [ite_eq_right (by simp; omega)]
        wp_step; wp_step; wp_step
        apply wp_set_eval
        let le6 := PTree.set id.t6 (Val.of_bool true) le
        have hsub : Exec.evalExpr ge empty_env le6 m (.Ebinop .Osub (tv id.hint) (ci 1 tint) tint) =
            some (.Vint (ir ((h - 1 : Nat) : Int))) := by
          simp only [Exec.evalExpr, le6, temps_gso _ _ (show id.hint ≠ id.t6 by decide), hhint, typeof,
            cop, ir_sub]
          congr 3; omega
        rw [Exec.evalExpr, hpe le6 _ (h - 1) (by omega) hsub rfl
          (by simp only [le6]; rw [temps_gso _ _ (by decide)]; exact hptn)
          (by simp only [le6]; rw [temps_gso _ _ (by decide)]; exact hlev), hle (h - 1) (by omega)]
        simp only [typeof, cop, cast_bool]
        simp only [E0_append]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop, cast_bool]
        refine hQ _ ?_ fun x h6 h7 => by rw [temps_gso _ _ h7, temps_gso _ _ h7, temps_gso _ _ h6]
        rw [temps_gss]
        congr 2
        apply decide_eq_decide.2
        simp only [HintOK, Int.toNat_natCast]
        constructor
        · intro hp; exact ⟨by omega, h1, .inr hp⟩
        · rintro ⟨-, -, hp | hp⟩
          · simp at hp; omega
          · exact hp
    · rw [show decide (level < ptn[h]!) = false by simpa using h1]
      rw [ite_eq_right (by simp)]
      apply wp_set_eval
      simp only [Exec.evalExpr, E0_append]
      refine hQ _ ?_ fun x h6 h7 => by rw [temps_gso _ _ h7, temps_gso _ _ h6]
      rw [temps_gss, decide_eq_false (fun hc => h1 (by simpa using hc.2.1))]; rfl
  · rw [ite_eq_right (by simp; omega)]
    apply wp_set_eval
    simp only [Exec.evalExpr, E0_append]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    rw [ite_eq_right (by decide)]
    apply wp_set_eval
    simp only [Exec.evalExpr, E0_append]
    refine hQ _ ?_ fun x h6 h7 => by rw [temps_gso _ _ h7, temps_gso _ _ h6]
    rw [temps_gss, decide_eq_false (fun hc => hs hc.1)]; rfl

theorem wp_scan {xi : ExternalCalls} {ge : genv} {f : function} {Q : Post} {le : temp_env}
    {m : mem} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {n level : Nat}
    (hptn : PTree.get id.ptn le = some (.Vptr bp pofs))
    (harr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n)
    (hn : n < 2147483648) (hlev : PTree.get id.level le = some (.Vint (ir level)))
    (hlevlt : level < 2147483648) (hsmall : ∀ x < n, ptn[x]! < 2147483648)
    (hnv : PTree.get id.n le = some (.Vint (ir n)))
    (hQ : ∀ le' k, k ≤ n → PTree.get id.i le' = some (.Vint (ir k)) →
      (∀ y < k, ptn[y]! ≤ level) → (k < n → level < ptn[k]!) →
      (∀ x, x ≠ id.i → x ≠ id.t4 → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m) :
    Wp xi ge f scan Q empty_env le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ c, c ≤ n ∧ v = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
      (∀ y < c, ptn[y]! ≤ level) ∧ ∀ x, x ≠ id.i → x ≠ id.t4 → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ c, c < n ∧ v = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
      (∀ y < c + 1, ptn[y]! ≤ level) ∧ ∀ x, x ≠ id.i → x ≠ id.t4 → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0) ⟨rfl, rfl, rfl, 0, Nat.zero_le _, rfl,
    temps_gss _ _ _, fun y hy => absurd hy (by omega), fun x hx _ => temps_gso _ _ hx⟩
  · rintro v t e' le' m' ⟨rfl, rfl, hmm, c, hc, rfl, hic, hlt, ho⟩
    rw [hmm]
    have hp' : PTree.get id.ptn le' = some (.Vptr bp pofs) := by
      rw [ho _ (by decide) (by decide)]; exact hptn
    have hl' : PTree.get id.level le' = some (.Vint (ir level)) := by
      rw [ho _ (by decide) (by decide)]; exact hlev
    have hn' : PTree.get id.n le' = some (.Vint (ir n)) := by
      rw [ho _ (by decide) (by decide)]; exact hnv
    wp_step; wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hic, hn', typeof, cop,
      ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hcn : c < n
    · rw [ite_eq_left (by simpa using hcn)]
      wp_step; wp_step
      apply wp_set_eval
      have hpc := eval_at (ge := ge) (e := empty_env) harr hn id.ptn hp' (tv id.i) c hcn hic rfl
      have := hsmall c hcn
      rw [Exec.evalExpr, Exec.evalExpr, hpc, show Exec.evalExpr ge empty_env le' m (tv id.level) = _ from hl']
      simp only [ints, typeof, cop]
      rw [ir_lt (a := (level : Int)) (b := (ptn[c]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      have hb : (!decide ((level : Int) < (ptn[c]! : Int))) = decide (ptn[c]! ≤ level) := by
        by_cases h : ptn[c]! ≤ level <;> simp [h] <;> omega
      rw [hb, cast_bool]
      simp only [E0_append]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      by_cases hpl : ptn[c]! ≤ level
      · rw [decide_eq_true hpl, ite_eq_left rfl]
        apply wp_skip
        apply wp_skip
        refine ⟨rfl, rfl, rfl, c, hcn, rfl, by rw [temps_gso _ _ (by decide)]; exact hic,
          fun y hy => ?_, fun x h1 h2 => by rw [temps_gso _ _ h2, ho x h1 h2]⟩
        rcases Nat.lt_or_ge y c with h | h
        · exact hlt y h
        · rw [show y = c by omega]; exact hpl
      · rw [decide_eq_false hpl, ite_eq_right (by decide)]
        apply wp_break
        exact hQ _ c (by omega) (by rw [temps_gso _ _ (by decide)]; exact hic) hlt (fun _ => by omega)
          fun x h1 h2 => by rw [temps_gso _ _ h2, ho x h1 h2]
    · rw [ite_eq_right (by simpa using hcn)]
      apply wp_set_eval
      simp only [Exec.evalExpr, E0_append]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      rw [ite_eq_right (by decide)]
      apply wp_break
      exact hQ _ c hc (by rw [temps_gso _ _ (by decide)]; exact hic) hlt (fun h => absurd h hcn)
        fun x h1 h2 => by rw [temps_gso _ _ h2, ho x h1 h2]
  · rintro v t e' le' m' ⟨rfl, rfl, hmm, c, hc, rfl, hic, hlt, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hic, typeof, cop, ir_add]
    refine ⟨n - (c + 1), by omega, by simp, rfl, hmm, c + 1, by omega, rfl,
      by rw [temps_gss]; push_cast; rfl, hlt, fun x h1 h2 => by rw [temps_gso _ _ h1, ho x h1 h2]⟩

theorem tc_hint {n : Nat} (ctx : Hex.GraphIso.Nauty.Ctx n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (h : HintOK ptn level hint) :
    Hex.GraphIso.Nauty.targetcell ctx lab ptn level tcLevel hint = hint.toNat := by
  unfold Hex.GraphIso.Nauty.targetcell; rw [ite_eq_left h]

theorem tc_best {n : Nat} (ctx : Hex.GraphIso.Nauty.Ctx n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (h : ¬ HintOK ptn level hint) (hl : level ≤ tcLevel) :
    Hex.GraphIso.Nauty.targetcell ctx lab ptn level tcLevel hint =
      Hex.GraphIso.Nauty.bestcell ctx lab ptn level := by
  unfold Hex.GraphIso.Nauty.targetcell; rw [ite_eq_right h, ite_eq_left hl]

theorem tc_scan {n : Nat} (ctx : Hex.GraphIso.Nauty.Ctx n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (h : ¬ HintOK ptn level hint) (hl : ¬ level ≤ tcLevel) (hs : ptn.size = n)
    (hlast : ptn[n - 1]! ≤ level) {k : Nat} (hk : k ≤ n) (hy : ∀ y < k, ptn[y]! ≤ level)
    (hkn : k < n → level < ptn[k]!) :
    Hex.GraphIso.Nauty.targetcell ctx lab ptn level tcLevel hint = if k < n then k else 0 := by
  unfold Hex.GraphIso.Nauty.targetcell; rw [ite_eq_right h, ite_eq_right hl]
  dsimp only
  have hf := findStart hs hlast n 0 k (by omega) (Nat.zero_le _) hk (fun y _ h2 => hy y h2) hkn
  unfold cells at hf ⊢
  split
  · next c1 c2 he => rw [he] at hf; split at hf <;> simp_all
  · next he => rw [he] at hf; split at hf <;> simp_all <;> omega

theorem targetcell_satisfies {xi : ExternalCalls} {n : Nat} (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (grows : Array (VSet n)) (bl : block) (lofs : ptrofs)
    (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat) (level tcLevel : Nat)
    (dg : Lib.Integers.int) (hint : Int) (M capP : Nat) (bP : block) (capS : Nat) (bS : block)
    (capB : Nat) (bB : block) :
    Satisfies xi ge (.Internal Source.dense.fn.targetcell)
      (targetcellSpec bg gofs gw grows bl lofs lab bp pofs ptn level tcLevel dg hint M capP bP capS
        bS capB bB) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bg gofs bl lofs bp pofs level tcLevel dg hint M n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bg gofs bl lofs bp pofs level tcLevel dg hint M n, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hpre, hhn, hh0, htc⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.targetcell.fn_body_eq, body_eq]
    simp only [body]
    have hnlt := hpre.nlt
    have hlev := hpre.levlt
    let E := entryTemps bg gofs bl lofs bp pofs level tcLevel dg hint M n
    have eptn : PTree.get id.ptn E = some (.Vptr bp pofs) := by
      simp (config := {decide := true}) only [E, entryTemps, temps_gso, temps_gss]
    have elev : PTree.get id.level E = some (.Vint (ir level)) := by
      simp (config := {decide := true}) only [E, entryTemps, temps_gso, temps_gss]
    have ehint : PTree.get id.hint E = some (.Vint (ir hint)) := by
      simp (config := {decide := true}) only [E, entryTemps, temps_gso, temps_gss]
    refine wp_hintTest eptn hpre.parr (by omega) elev hlev hpre.psmall ehint hhn hh0 ?_
    intro le1 h7 ho1
    have g1 : ∀ x, x = id.g ∨ x = id.lab ∨ x = id.ptn ∨ x = id.level ∨ x = id.tc_level ∨
        x = id.hint ∨ x = id.m ∨ x = id.n → PTree.get x le1 = PTree.get x E := fun x hx =>
      ho1 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    apply wp_if_eval
    simp only [Exec.evalExpr, h7, typeof, cop]
    by_cases hok : HintOK ptn level hint
    · rw [decide_eq_true hok, ite_eq_left rfl]
      wp_step; wp_step
      apply wp_return_some_eval
      simp only [Exec.evalExpr, g1 _ (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))), ehint, typeof, cop,
        Source.dense.fn.targetcell.fn_return_eq, Nextelement.free_empty]
      refine ⟨rfl, ?_, hpre.post_refl⟩
      rw [tc_hint _ _ _ _ _ _ hok, Int.toNat_of_nonneg hok.1]
    · rw [decide_eq_false hok, ite_eq_right (by decide)]
      have gv : ∀ x, x = id.g ∨ x = id.lab ∨ x = id.ptn ∨ x = id.level ∨ x = id.tc_level ∨
          x = id.hint ∨ x = id.m ∨ x = id.n → ∀ v, PTree.get x E = some v →
          Exec.evalExpr ge empty_env le1 m (.Etempvar x tint) = some v := fun x hx v hv => by
        show PTree.get _ _ = _; rw [g1 x hx]; exact hv
      wp_step; wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, g1 _ (.inr (.inr (.inr (.inl rfl)))),
        g1 _ (.inr (.inr (.inr (.inr (.inl rfl))))), elev, typeof, cop]
      rw [show PTree.get id.tc_level E = some (.Vint (ir tcLevel)) by
        simp (config := {decide := true}) only [E, entryTemps, temps_gso, temps_gss]]
      simp only [cop]
      rw [ir_lt (a := (tcLevel : Int)) (b := (level : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hl : level ≤ tcLevel
      · rw [ite_eq_left (by simp; omega)]
        have eE : ∀ x v, PTree.get x E = some v → (x = id.g ∨ x = id.lab ∨ x = id.ptn ∨
            x = id.level ∨ x = id.tc_level ∨ x = id.hint ∨ x = id.m ∨ x = id.n) →
            PTree.get x le1 = some v := fun x v hv hx => by rw [g1 x hx]; exact hv
        have a1 := eE id.g (.Vptr bg gofs) (by simp (config := {decide := true}) only [E, entryTemps, temps_gso, temps_gss]) (.inl rfl)
        have a2 := eE id.lab (.Vptr bl lofs) (by simp (config := {decide := true}) only [E, entryTemps, temps_gso, temps_gss]) (.inr (.inl rfl))
        have a3 := eE id.ptn _ eptn (.inr (.inr (.inl rfl)))
        have a4 := eE id.level _ elev (.inr (.inr (.inr (.inl rfl))))
        have a5 := eE id.tc_level (.Vint (ir tcLevel)) (by simp (config := {decide := true}) only [E, entryTemps, temps_gso, temps_gss]) (.inr (.inr (.inr (.inr (.inl rfl)))))
        have a7 := eE id.m (.Vint (ir M)) (by simp (config := {decide := true}) only [E, entryTemps, temps_gso, temps_gss]) (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
        have a8 := eE id.n (.Vint (ir n)) (by simp (config := {decide := true}) only [E, entryTemps, temps_gss]) (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))
        wp_step; wp_step; wp_step
        refine wp_call (vf := .Vptr Block.bestcell Ptrofs.zero)
          (targs := [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tint]) (tres := tint)
          (cc := Common.AST.cc_default) _
          (bestcellSpec bg gofs gw grows bl lofs lab bp pofs ptn level tcLevel M capP bP capS bS capB bB)
          (bestcell_satisfies _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) rfl
          (by simp only [Exec.evalExpr, Exec.lvalOfVar,
            show PTree.get Source.dense.id.«naugraph:bestcell» (empty_env : env) = none from rfl,
            find_bestcell, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
          (by simp only [Exec.evalExprlist, Exec.evalExpr, a1, a2, a3, a4, a5, a7, a8, typeof, cop])
          (by simp [Common.Globalenvs.Genv.find_funct, funct_bestcell]) rfl ⟨rfl, hpre⟩ ?_
        rintro t v m' ⟨rfl, rfl, hpost⟩
        simp only [set_opttemp, E0_append]
        apply wp_return_some_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop, Source.dense.fn.targetcell.fn_return_eq,
          Nextelement.free_empty]
        exact ⟨rfl, by rw [tc_best _ _ _ _ _ _ hok hl], hpost⟩
      · rw [ite_eq_right (by simp; omega)]
        wp_step
        refine wp_scan (by rw [g1 _ (.inr (.inr (.inl rfl)))]; exact eptn) hpre.parr (by omega)
          (by rw [g1 _ (.inr (.inr (.inr (.inl rfl))))]; exact elev) hlev hpre.psmall
          (by rw [g1 _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))]
              simp (config := {decide := true}) only [E, entryTemps, temps_gss]) ?_
        intro le2 k hk hik hy hkn ho2
        have hres := tc_scan ⟨grows⟩ lab ptn level tcLevel hint hok hl hpre.psize hpre.plast hk hy hkn
        have hn2 : PTree.get id.n le2 = some (.Vint (ir n)) := by
          rw [ho2 _ (by decide) (by decide), g1 _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))]
          simp (config := {decide := true}) only [E, entryTemps, temps_gss]
        simp only [E0_append]
        wp_step; wp_step; wp_step
        apply wp_if_eval
        simp only [Exec.evalExpr, hik, hn2, typeof, cop]
        rw [ir_eq (a := (k : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
        by_cases hkn' : k = n
        · rw [ite_eq_left (by simp [hkn'])]
          wp_step; wp_step
          apply wp_set_eval
          simp only [Exec.evalExpr, typeof, cop, E0_append]
          apply wp_return_some_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop, Source.dense.fn.targetcell.fn_return_eq,
            Nextelement.free_empty]
          refine ⟨rfl, ?_, hpre.post_refl⟩
          rw [hres, ite_eq_right (by omega)]; rfl
        · rw [ite_eq_right (by simp; omega)]
          wp_step; wp_step
          apply wp_set_eval
          simp only [Exec.evalExpr, hik, typeof, cop, E0_append]
          apply wp_return_some_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop, Source.dense.fn.targetcell.fn_return_eq,
            Nextelement.free_empty]
          refine ⟨rfl, ?_, hpre.post_refl⟩
          rw [hres, ite_eq_left (by omega)]

end NautyVerified.Proofs.Targetcell

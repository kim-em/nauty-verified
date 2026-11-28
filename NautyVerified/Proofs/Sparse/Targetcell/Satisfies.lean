import NautyVerified.Proofs.Targetcell.Satisfies
import NautyVerified.Proofs.Sparse.Bestcell.Satisfies

/-!
# `targetcell_sg` meets its specification

`targetcellSpec`: with a hint below `n`, nausparse.c's `targetcell_sg`
returns HexGraphIso's `Sparse.targetcell (ofGraph G) lab ptn level tcLevel hint`,
calling `bestcell_sg` through its specification (`Bestcell.bestcell_satisfies`)
when `level ≤ tc_level`.
The hint test and the scan are naugraph.c's, proved once for both programs
(`Targetcell.wp_hintTest`, `Targetcell.wp_scan`).

`targetcell_sg` is `dispatch_sparse.targetcell`; nauty.c's `maketargetcell`
calls it through the dispatch pointer, so its result is
`Sparse.maketargetcell`'s first component, and `maketargetCached_eq`
relates that to the cached form the search state uses.
-/

namespace NautyVerified.Proofs.Sparse.Targetcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Bestcell (Pre Post bestcellSpec)
open NautyVerified.Proofs.Targetcell (HintOK wp_hintTest wp_scan)
open NautyVerified.Proofs.Updatecan (tv)
open Hex.GraphIso.Nauty.Sparse (Graph)

abbrev F := sparse.fn.targetcell_sg

def targetcellSpec {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (bl : block)
    (lofs : ptrofs) (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat)
    (level tcLevel : Nat) (dg : Lib.Integers.int) (hint : Int) (M : Nat) (c : Fin 4 → Nat)
    (b : Fin 4 → block) : FunSpec where
  pre args m := args = [.Vptr bsg sofs, .Vptr bl lofs, .Vptr bp pofs, .Vint (ir level),
      .Vint (ir tcLevel), .Vint dg, .Vint (ir hint), .Vint (ir M), .Vint (ir n)] ∧
    Pre m G bsg sofs bv vo bd dofs be eo bl lofs lab bp pofs ptn level c b ∧
    hint < n ∧ -2147483648 ≤ hint ∧ tcLevel < 2147483648
  post _ m t v m' := t = E0 ∧
    v = .Vint (ir (Hex.GraphIso.Nauty.Sparse.targetcell (Graph.ofGraph G) lab ptn level tcLevel hint :
      Int)) ∧
    Post m m' c b

def entryTemps (bsg : block) (sofs : ptrofs) (bl : block) (lofs : ptrofs) (bp : block)
    (pofs : ptrofs) (level tcLevel : Nat) (dg : Lib.Integers.int) (hint : Int) (M n : Nat) :
    temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.hint (.Vint (ir hint)) (PTree.set id.digraph (.Vint dg)
      (PTree.set id.tc_level (.Vint (ir tcLevel)) (PTree.set id.level (.Vint (ir level))
        (PTree.set id.ptn (.Vptr bp pofs) (PTree.set id.lab (.Vptr bl lofs)
          (PTree.set id.g (.Vptr bsg sofs)
            (create_undef_temps F.fn_temps)))))))))

theorem find_range (p : Nat → Bool) : ∀ (n k : Nat), k ≤ n → (∀ y < k, p y = false) →
    (k < n → p k = true) → (List.range n).find? p = if k < n then some k else none
  | 0, k, _, _, _ => by simp
  | n + 1, k, hk, hy, hkn => by
    rw [List.range_succ, List.find?_append]
    by_cases hkn' : k < n
    · rw [find_range p n k (by omega) hy (fun _ => hkn (by omega)), ite_eq_left hkn',
        ite_eq_left (by omega)]
      rfl
    · rw [find_range p n n (Nat.le_refl _) (fun y hy' => hy y (by omega)) (by omega),
        ite_eq_right (by omega)]
      by_cases hk1 : k = n
      · subst hk1
        rw [ite_eq_left (by omega)]
        simp [hkn (by omega)]
      · rw [ite_eq_right (by omega)]
        simp [hy n (by omega)]

theorem tc_hint {n : Nat} (g : Graph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (h : HintOK ptn level hint) :
    Hex.GraphIso.Nauty.Sparse.targetcell g lab ptn level tcLevel hint = hint.toNat := by
  unfold Hex.GraphIso.Nauty.Sparse.targetcell
  rw [ite_eq_left (by simpa [HintOK, and_assoc] using h)]

theorem tc_best {n : Nat} (g : Graph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (h : ¬ HintOK ptn level hint) (hl : level ≤ tcLevel) :
    Hex.GraphIso.Nauty.Sparse.targetcell g lab ptn level tcLevel hint =
      Hex.GraphIso.Nauty.Sparse.bestcell g lab ptn level := by
  unfold Hex.GraphIso.Nauty.Sparse.targetcell
  rw [ite_eq_right (by simpa [HintOK, and_assoc] using h), ite_eq_left hl]

theorem tc_scan {n : Nat} (g : Graph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (h : ¬ HintOK ptn level hint) (hl : ¬ level ≤ tcLevel) {k : Nat} (hk : k ≤ n)
    (hy : ∀ y < k, ptn[y]! ≤ level) (hkn : k < n → level < ptn[k]!) :
    Hex.GraphIso.Nauty.Sparse.targetcell g lab ptn level tcLevel hint = if k < n then k else 0 := by
  unfold Hex.GraphIso.Nauty.Sparse.targetcell
  rw [ite_eq_right (by simpa [HintOK, and_assoc] using h), ite_eq_right hl,
    find_range (fun i => decide (ptn[i]! > level)) n k hk (fun y hy' => by simpa using hy y hy')
      (fun h' => by simpa using hkn h')]
  split <;> rfl

theorem targetcell_satisfies {xi : ExternalCalls} {n : Nat} (G : Hex.SparseGraph n) (bsg : block)
    (sofs : ptrofs) (bv : block) (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block)
    (eo : ptrofs) (bl : block) (lofs : ptrofs) (lab : Array Nat) (bp : block) (pofs : ptrofs)
    (ptn : Array Nat) (level tcLevel : Nat) (dg : Lib.Integers.int) (hint : Int) (M : Nat)
    (c : Fin 4 → Nat) (b : Fin 4 → block) :
    Satisfies xi sge (.Internal F)
      (targetcellSpec G bsg sofs bv vo bd dofs be eo bl lofs lab bp pofs ptn level tcLevel dg hint M
        c b) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bsg sofs bl lofs bp pofs level tcLevel dg hint M n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bsg sofs bl lofs bp pofs level tcLevel dg hint M n, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hpre, hhn, hh0, htc⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [sparse.fn.targetcell_sg.fn_body_eq, body_eq]
    simp only [body]
    have hnlt := hpre.nlt
    have hlev := hpre.levlt
    have hrefl : Post m m c b := Post.refl hpre.works
    let E := entryTemps bsg sofs bl lofs bp pofs level tcLevel dg hint M n
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
        sparse.fn.targetcell_sg.fn_return_eq, Isautom.free_empty]
      refine ⟨rfl, ?_, hrefl⟩
      rw [tc_hint _ _ _ _ _ _ hok, Int.toNat_of_nonneg hok.1]
    · rw [decide_eq_false hok, ite_eq_right (by decide)]
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
        have a1 := eE id.g (.Vptr bsg sofs) (by simp (config := {decide := true}) only [E, entryTemps, temps_gso, temps_gss]) (.inl rfl)
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
          (bestcellSpec G bsg sofs bv vo bd dofs be eo bl lofs lab bp pofs ptn level tcLevel M c b)
          (Bestcell.bestcell_satisfies G bsg sofs bv vo bd dofs be eo bl lofs lab bp pofs ptn level tcLevel
            M c b) rfl
          (by simp only [Exec.evalExpr, Exec.lvalOfVar,
            show PTree.get sparse.id.«nausparse:bestcell_sg» (empty_env : env) = none from rfl,
            find_bestcell, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
          (by simp only [Exec.evalExprlist, Exec.evalExpr, a1, a2, a3, a4, a5, a7, a8, typeof, cop])
          (by simp [Common.Globalenvs.Genv.find_funct, funct_bestcell]) rfl ⟨rfl, hpre⟩ ?_
        rintro t v m' ⟨rfl, rfl, hpost⟩
        simp only [set_opttemp, E0_append]
        apply wp_return_some_eval
        simp only [Exec.evalExpr, temps_gss, typeof, cop, sparse.fn.targetcell_sg.fn_return_eq,
          Isautom.free_empty]
        exact ⟨rfl, by rw [tc_best _ _ _ _ _ _ hok hl], hpost⟩
      · rw [ite_eq_right (by simp; omega)]
        wp_step
        refine wp_scan (by rw [g1 _ (.inr (.inr (.inl rfl)))]; exact eptn) hpre.parr (by omega)
          (by rw [g1 _ (.inr (.inr (.inr (.inl rfl))))]; exact elev) hlev hpre.psmall
          (by rw [g1 _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))]
              simp (config := {decide := true}) only [E, entryTemps, temps_gss]) ?_
        intro le2 k hk hik hy hkn ho2
        have hres := tc_scan (Graph.ofGraph G) lab ptn level tcLevel hint hok hl hk hy hkn
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
          simp only [Exec.evalExpr, temps_gss, typeof, cop, sparse.fn.targetcell_sg.fn_return_eq,
            Isautom.free_empty]
          refine ⟨rfl, ?_, hrefl⟩
          rw [hres, ite_eq_right (by omega)]; rfl
        · rw [ite_eq_right (by simp; omega)]
          wp_step; wp_step
          apply wp_set_eval
          simp only [Exec.evalExpr, hik, typeof, cop, E0_append]
          apply wp_return_some_eval
          simp only [Exec.evalExpr, temps_gss, typeof, cop, sparse.fn.targetcell_sg.fn_return_eq,
            Isautom.free_empty]
          refine ⟨rfl, ?_, hrefl⟩
          rw [hres, ite_eq_left (by omega)]

end NautyVerified.Proofs.Sparse.Targetcell

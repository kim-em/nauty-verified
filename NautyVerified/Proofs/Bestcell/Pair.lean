import NautyVerified.Proofs.Bestcell.Or

/-!
# One `(v1, v2)` pair of `bestcell`

`wp_pair`: for the cell starting at `workperm[v1]`, the word loop and the test
`setword1 != 0 && setword2 != 0` bump `bucket[v1]` and `bucket[v2]` exactly as
HexGraphIso's `rowStep` does. `wp_pairs`: the loop over `v1 < v2` is the fold
`bestcellRow` over `range v2`.
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Spec.Bestcell
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Alloc (Keep gat)
open NautyVerified.Proofs.Updatecan (tv labAt row)
open Hex.GraphIso.Nauty (VSet Ctx)

variable {xi : ExternalCalls}

section
variable {n : Nat} {bg : block} {gofs : ptrofs}
  {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bl : block} {lofs : ptrofs}
  {lab : Array Nat} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {level M : Nat}
  {bP bS bB : block}

theorem wp_bump {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {bv : Nat → val} (hb : ArrayAt m .Mint32 bB 0 bv (n + 2)) (x : Common.AST.ident) (c y : Nat)
    (hc : c < n + 2) (hx : PTree.get x le = some (.Vint (ir c))) (hv : bv c = .Vint (ir y))
    (hQ : ∀ m', ArrayAt m' .Mint32 bB 0 (upd bv c (.Vint (ir ((y + 1 : Nat) : Int)))) (n + 2) →
      Unch m m' (· = bB) → Keep m m' bB → Q.normal E0 empty_env le m') :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» (bump (tv x)) Q empty_env le m := by
  have hnlt := h.nlt
  have he := eval_bk h hb (tv x) c hc hx rfl
  wp_step; wp_step
  refine Alloc.wp_gstore rfl find_naugraphBucket h.bkP hb (by omega) (tv x) c hc hx rfl _
    ((y : Int) + 1) (by rw [Exec.evalExpr, he, hv]; simp only [Exec.evalExpr, typeof, cop]; rw [ir_add]) rfl ?_
  intro m' h1 h2 h3
  rw [show ((y : Int) + 1) = ((y + 1 : Nat) : Int) by push_cast; rfl] at h1
  exact hQ m' h1 h2 h3

theorem setRep_row {le : temp_env} {m : mem} (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {u : Nat} (hu : u < n) : SetRep (fun w => bv64 (gw (M * u + w))) M grows[u]! :=
  h.graph.rep u hu

/-- The counts after `++bucket[j]; ++bucket[v2]` when the test holds. -/
def bumped (B : Array Nat) (j v2 : Nat) : Array Nat :=
  (B.set! j (B[j]! + 1)).set! v2 (B[v2]! + 1)

theorem bumped_get (B : Array Nat) {bv : Nat → val}
    (hbv : ∀ x < B.size, bv x = .Vint (ir (B[x]! : Int))) {j v2 x : Nat} (hj : j ≠ v2)
    (hjs : j < B.size) (hv : v2 < B.size) (hx : x < B.size) :
    upd (upd bv j (.Vint (ir ((B[j]! + 1 : Nat) : Int)))) v2 (.Vint (ir ((B[v2]! + 1 : Nat) : Int))) x =
      .Vint (ir ((bumped B j v2)[x]! : Int)) := by
  simp only [upd, bumped, get_set, Array.size_set!]
  by_cases ex2 : x = v2
  · subst ex2; simp [hx]
  · by_cases ex1 : x = j
    · subst ex1; simp [ex2, hx, Ne.symm ex2]
    · simp [ex1, ex2, Ne.symm ex1, Ne.symm ex2, hbv x hx]

theorem wp_test {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {bv : Nat → val} (hb : ArrayAt m .Mint32 bB 0 bv (n + 2)) {B : Array Nat}
    (hbv : ∀ x < B.size, bv x = .Vint (ir (B[x]! : Int))) (hBn : B.size ≤ n)
    {j v2 : Nat} (hj : j < v2) (hv2 : v2 < B.size)
    (hv1v : PTree.get id.v1 le = some (.Vint (ir j)))
    (hv2v : PTree.get id.v2 le = some (.Vint (ir v2)))
    {c1 c2 : Lib.Integers.int64}
    (hc1 : PTree.get id.sw1 le = some (.Vlong c1)) (hc2 : PTree.get id.sw2 le = some (.Vlong c2))
    (hQ : ∀ le' m' bv', ArrayAt m' .Mint32 bB 0 bv' (n + 2) →
      (∀ x < B.size, bv' x = .Vint (ir ((if bv64 c1 ≠ 0 ∧ bv64 c2 ≠ 0 then bumped B j v2 else B)[x]! : Int))) →
      Unch m m' (· = bB) → Keep m m' bB → (∀ x, x ≠ id.t15 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» test Q empty_env le m := by
  have hnlt := h.nlt
  have h0 : Cfrontend.Cop.cast_int_long .Signed (ir 0) = lr 0 := cast_int_long_ir ⟨by decide, by decide⟩
  have hne : ∀ c : Lib.Integers.int64, (!Lib.Integers.Int64.eq c (lr 0)) = decide (bv64 c ≠ 0) := by
    intro c; rw [bv64_eq]; simp [show bv64 (lr 0) = 0 by rfl]
  simp only [test]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hc1, typeof, cop, h0, hne]
  by_cases e1 : bv64 c1 ≠ 0
  · rw [ite_eq_left (by simpa using e1)]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hc2, typeof, cop, h0, hne]
    by_cases e2 : bv64 c2 ≠ 0
    · have hd : decide (bv64 c2 ≠ 0) = true := by simpa using e2
      rw [hd]
      simp only [Val.of_bool, ite_true, Vtrue, cop,
        show Lib.Integers.Int.eq Lib.Integers.Int.one Lib.Integers.Int.zero = false from rfl,
        Bool.false_eq_true, ite_false, E0_append]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop,
        show Lib.Integers.Int.eq Lib.Integers.Int.one Lib.Integers.Int.zero = false from rfl,
        Bool.not_false, ite_true]
      let le2 := PTree.set id.t15 (.Vint Lib.Integers.Int.one) le
      have hf2 := h.temps (le' := le2) fun x hx => temps_gso _ _ (by
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      wp_step
      refine wp_bump hf2 hb id.v1 j B[j]! (by omega)
        (by rw [temps_gso _ _ (by decide)]; exact hv1v) (hbv j (by omega)) ?_
      intro m1 hb1 hu1 hk1
      simp only [E0_append]
      have hf3 := hf2.unch (m' := m1) (hu1.mono fun _ hz => .inr (.inr hz))
      refine wp_bump hf3 hb1 id.v2 v2 B[v2]! (by omega)
        (by rw [temps_gso _ _ (by decide)]; exact hv2v)
        (by simp only [upd]; rw [ite_eq_right (by omega)]; exact hbv v2 hv2) ?_
      intro m2 hb2 hu2 hk2
      refine hQ le2 m2 _ hb2 (fun x hx => ?_) (hu1.trans hu2) (hk1.trans hk2)
        fun x hx => temps_gso _ _ hx
      rw [ite_eq_left ⟨e1, e2⟩]
      exact bumped_get B hbv (by omega) (by omega) hv2 hx
    · have hd : decide (bv64 c2 ≠ 0) = false := by simpa using e2
      rw [hd]
      simp only [Val.of_bool, Bool.false_eq_true, ite_false, Vfalse, cop,
        show Lib.Integers.Int.eq Lib.Integers.Int.zero Lib.Integers.Int.zero = true from rfl,
        ite_true, E0_append]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop,
        show Lib.Integers.Int.eq Lib.Integers.Int.zero Lib.Integers.Int.zero = true from rfl,
        Bool.not_true]
      rw [ite_eq_right (by simp)]
      apply wp_skip
      refine hQ _ m bv hb (fun x hx => ?_) (Unch.refl _ _) (Keep.refl _ _)
        fun x hx => temps_gso _ _ hx
      rw [ite_eq_right (fun h => e2 h.2)]; exact hbv x hx
  · rw [ite_eq_right (by simpa using e1)]
    apply wp_set_eval
    simp only [Exec.evalExpr, E0_append]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    rw [ite_eq_right (by decide)]
    apply wp_skip
    refine hQ _ m bv hb (fun x hx => ?_) (Unch.refl _ _) (Keep.refl _ _)
      fun x hx => temps_gso _ _ hx
    rw [ite_eq_right (fun h => e1 h.1)]; exact hbv x hx

theorem rowStep_eq {S : List Nat} {W : VSet n} {B : Array Nat} {j v2 : Nat} {c1 c2 : Lib.Integers.int64}
    {ws : Nat → Lib.Integers.int64} (hW : SetRep (fun w => bv64 (ws w)) M W)
    (hr : SetRep (fun w => bv64 (gw (M * lab[S[j]!]! + w))) M grows[lab[S[j]!]!]!)
    (hor : OrInv ws (fun w => gw (M * lab[S[j]!]! + w)) 0 M c1 c2) :
    (if bv64 c1 ≠ 0 ∧ bv64 c2 ≠ 0 then bumped B j v2 else B) =
      rowStep ⟨grows⟩ lab S.toArray W v2 B j := by
  have e1 : bv64 c1 = 0 ↔ W.interIsEmpty grows[lab[S[j]!]!]! = true := by
    rw [hor.1, interIsEmpty_iff hW hr]
    exact ⟨fun h w hw => h w (Nat.zero_le _) hw, fun h w _ hw => h w hw⟩
  have e2 : bv64 c2 = 0 ↔ W.subset grows[lab[S[j]!]!]! = true := by
    rw [hor.2, ← setRep_subset hW hr]
    exact ⟨fun h w hw => h w (Nat.zero_le _) hw, fun h w _ hw => h w hw⟩
  unfold rowStep
  simp only [List.getElem!_toArray]
  by_cases h1 : bv64 c1 = 0
  · rw [ite_eq_right (fun h => h.1 h1), ite_eq_right (fun h => h.1 (e1.1 h1))]
  · by_cases h2 : bv64 c2 = 0
    · rw [ite_eq_right (fun h => h.2 h2), ite_eq_right (fun h => h.2 (e2.1 h2))]
    · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left ⟨fun h => h1 (e1.2 h), fun h => h2 (e2.2 h)⟩]; rfl

theorem wp_pair {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {wv : Nat → val} (hw : ArrayAt m .Mint32 bP 0 wv n) {S : List Nat}
    (hwS : ∀ k < S.length, wv k = .Vint (ir (S[k]! : Int))) (hSn : ∀ k < S.length, S[k]! < n)
    {ws : Nat → Lib.Integers.int64} (hws : ArrayAt m .Mint64 bS 0 (longs ws) M) {W : VSet n}
    (hW : SetRep (fun w => bv64 (ws w)) M W)
    {bv : Nat → val} (hb : ArrayAt m .Mint32 bB 0 bv (n + 2)) {B : Array Nat}
    (hbv : ∀ x < B.size, bv x = .Vint (ir (B[x]! : Int))) (hBs : B.size = S.length)
    (hSlen : S.length ≤ n) {j v2 : Nat} (hj : j < v2) (hv2 : v2 < S.length)
    (hv1v : PTree.get id.v1 le = some (.Vint (ir j)))
    (hv2v : PTree.get id.v2 le = some (.Vint (ir v2)))
    (hQ : ∀ le' m' bv', ArrayAt m' .Mint32 bB 0 bv' (n + 2) →
      (∀ x < B.size, bv' x = .Vint (ir ((rowStep ⟨grows⟩ lab S.toArray W v2 B j)[x]! : Int))) →
      Unch m m' (· = bB) → Keep m m' bB →
      (∀ x, x ≠ id.gp → x ≠ id.t13 → x ≠ id.sw1 → x ≠ id.sw2 → x ≠ id.i → x ≠ id.t14 →
        x ≠ id.t15 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» pair Q empty_env le m := by
  have hnlt := h.nlt
  have hMlt := h.Mlt
  have hjS : S[j]! < n := hSn j (by omega)
  have hu : lab[S[j]!]! < n := h.lsmall _ hjS
  let u := lab[S[j]!]!
  let baseg := intOfZ (Ptrofs.unsigned gofs)
  have ewp := eval_wp h hw (tv id.v1) j (by omega) hv1v rfl
  rw [hwS j (by omega)] at ewp
  have hlab := eval_lab h (gat id.wp (tv id.v1)) S[j]! hjS ewp rfl
  have hrowg : Exec.evalExpr ge empty_env le m (row id.g (labAt (gat id.wp (tv id.v1)))) =
      some (.Vptr bg (ptrTo baseg 8 (M * u))) := by
    have e1 : Exec.evalExpr ge empty_env le m (.Ecast (Set.pv id.g) (tptr tulong)) =
        some (.Vptr bg gofs) := by simp only [Exec.evalExpr, h.hg, typeof, cop]
    have e3 : Exec.evalExpr ge empty_env le m (.Ecast (labAt (gat id.wp (tv id.v1))) tulong) =
        some (.Vlong (lr (u : Int))) := by
      rw [Exec.evalExpr, hlab]
      simp only [typeof, cop]
      rw [cast_int_long_ir (a := (lab[S[j]!]! : Int)) ⟨by omega, by omega⟩]
    rw [Exec.evalExpr, e1, Exec.evalExpr, show Exec.evalExpr ge empty_env le m (tv id.m) = _ from h.hm, e3]
    simp only [typeof, cop, Graph.mul_lr (show M < 2147483648 by omega)]
    rw [show ((M : Int) * (u : Int)) = ((M * u : Nat) : Int) by push_cast; rfl,
      Graph.add_ptrTo_long]
  have h0 : Cfrontend.Cop.cast_int_long .Signed (ir 0) = lr 0 := cast_int_long_ir ⟨by decide, by decide⟩
  simp only [pair]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [hrowg]
  simp only [E0_append]
  wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, h0]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gso _ _ (show id.t13 ≠ id.sw2 by decide), temps_gss, E0_append]
  let le1 := PTree.set id.sw1 (.Vlong (lr 0)) (PTree.set id.sw2 (.Vlong (lr 0))
    (PTree.set id.t13 (.Vlong (lr 0)) (PTree.set id.gp (.Vptr bg (ptrTo baseg 8 (M * u))) le)))
  have ho1 : ∀ x, x ≠ id.gp → x ≠ id.t13 → x ≠ id.sw1 → x ≠ id.sw2 →
      PTree.get x le1 = PTree.get x le := fun x h1 h2 h3 h4 => by
    simp only [le1]; rw [temps_gso _ _ h3, temps_gso _ _ h4, temps_gso _ _ h2, temps_gso _ _ h1]
  wp_step
  refine wp_orLoop (le := le1) h.wsP hws (by simp only [le1]; rw [temps_gso _ _ (by decide),
      temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gss]) (h.graph.row hu)
    (by omega) (by rw [ho1 _ (by decide) (by decide) (by decide) (by decide)]; exact h.hm)
    (temps_gss _ _ _) (by simp only [le1]; rw [temps_gso _ _ (by decide), temps_gss])
    ⟨rfl, rfl⟩ ?_
  intro le2 c1 c2 hc1 hc2 hor ho2
  have hf2 := h.temps (le' := le2) fun x hx => by
    rw [ho2 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      ho1 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  refine wp_test hf2 hb hbv (by omega) hj (by omega)
    (by rw [ho2 _ (by decide) (by decide) (by decide) (by decide),
      ho1 _ (by decide) (by decide) (by decide) (by decide)]; exact hv1v)
    (by rw [ho2 _ (by decide) (by decide) (by decide) (by decide),
      ho1 _ (by decide) (by decide) (by decide) (by decide)]; exact hv2v) hc1 hc2 ?_
  intro le3 m3 bv3 hb3 hbv3 hu3 hk3 ho3
  refine hQ le3 m3 bv3 hb3 (fun x hx => ?_) hu3 hk3 fun x h1 h2 h3 h4 h5 h6 h7 => ?_
  · rw [hbv3 x hx, rowStep_eq hW (setRep_row h hu) hor]
  · rw [ho3 x h7, ho2 x h5 h6 h3 h4, ho1 x h1 h2 h3 h4]

/-- The temporaries the `v1` loop sets. -/
def PairT (x : Common.AST.ident) : Prop :=
  x ≠ id.v1 ∧ x ≠ id.gp ∧ x ≠ id.t13 ∧ x ≠ id.sw1 ∧ x ≠ id.sw2 ∧ x ≠ id.i ∧ x ≠ id.t14 ∧ x ≠ id.t15

theorem wp_pairs {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {wv : Nat → val} (hw : ArrayAt m .Mint32 bP 0 wv n) {S : List Nat}
    (hwS : ∀ k < S.length, wv k = .Vint (ir (S[k]! : Int))) (hSn : ∀ k < S.length, S[k]! < n)
    {ws : Nat → Lib.Integers.int64} (hws : ArrayAt m .Mint64 bS 0 (longs ws) M) {W : VSet n}
    (hW : SetRep (fun w => bv64 (ws w)) M W)
    {bv : Nat → val} (hb : ArrayAt m .Mint32 bB 0 bv (n + 2)) {B : Array Nat}
    (hbv : ∀ x < B.size, bv x = .Vint (ir (B[x]! : Int))) (hBs : B.size = S.length)
    (hSlen : S.length ≤ n) {v2 : Nat} (hv2 : v2 < S.length)
    (hv2v : PTree.get id.v2 le = some (.Vint (ir v2)))
    (hQ : ∀ le' m' bv', ArrayAt m' .Mint32 bB 0 bv' (n + 2) →
      (∀ x < B.size, bv' x =
        .Vint (ir (((List.range v2).foldl (rowStep ⟨grows⟩ lab S.toArray W v2) B)[x]! : Int))) →
      Unch m m' (· = bB) → Keep m m' bB → (∀ x, PairT x → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» pairs Q empty_env le m := by
  have hnlt := h.nlt
  let R := fun k => (List.range k).foldl (rowStep ⟨grows⟩ lab S.toArray W v2) B
  have hRs : ∀ k, (R k).size = B.size := fun k => size_row _ _ _ _ _ _ _
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) => k ≤ v2 ∧
    PTree.get id.v1 le' = some (.Vint (ir k)) ∧ ∃ bv', ArrayAt m' .Mint32 bB 0 bv' (n + 2) ∧
      (∀ x < B.size, bv' x = .Vint (ir ((R k)[x]! : Int))) ∧ Unch m m' (· = bB) ∧
      Keep m m' bB ∧ ∀ x, PairT x → PTree.get x le' = PTree.get x le
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    PTree.get id.v1 le' = some (.Vint (ir k)) ∧ k < v2 ∧ ∃ bv', ArrayAt m' .Mint32 bB 0 bv' (n + 2) ∧
      (∀ x < B.size, bv' x = .Vint (ir ((R (k + 1))[x]! : Int))) ∧ Unch m m' (· = bB) ∧
      Keep m m' bB ∧ ∀ x, PairT x → PTree.get x le' = PTree.get x le
  have hv2' : ∀ le', (∀ x, PairT x → PTree.get x le' = PTree.get x le) →
      PTree.get id.v2 le' = some (.Vint (ir v2)) := fun le' ho => by
    rw [ho _ (by unfold PairT; decide)]; exact hv2v
  refine wp_forLoop id.v1 id.v2 pair v2 (by omega) Inv Mid ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hv1, -, -, -, -, -, ho⟩
    exact ⟨hk, hv1, hv2' le' ho⟩
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, bv, hb, hbv, Unch.refl _ _, Keep.refl _ _,
      fun x hx => temps_gso _ _ hx.1⟩
  · rintro k le' m' hk ⟨-, hv1, bv', hb', hbv', hu, hkp, ho⟩
    have hf := (h.unch (m' := m') (hu.mono fun _ hz => .inr (.inr hz))).temps (le' := le')
      fun x hx => ho x (by unfold PairT; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    refine wp_pair hf (hw.unch hu h.dPB) hwS hSn (hws.unch hu h.dSB) hW hb'
      (fun x hx => by rw [hRs] at hx; exact hbv' x hx) (by rw [hRs]; exact hBs) hSlen hk hv2 hv1
      (hv2' le' ho) ?_
    intro le2 m2 bv2 hb2 hbv2 hu2 hk2 ho2
    refine ⟨rfl, by rw [ho2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hv1, hk, bv2, hb2, fun x hx => ?_, hu.trans hu2, hkp.trans hk2,
      fun x hx => by
        rw [ho2 x hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1
          hx.2.2.2.2.2.2.2, ho x hx]⟩
    rw [hbv2 x (by rw [hRs]; exact hx)]
    simp only [R]
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · rintro k le' m' ⟨hv1, hk, bv', hb', hbv', hu, hkp, ho⟩
    exact ⟨hv1, by omega, temps_gss _ _ _, bv', hb', hbv', hu, hkp,
      fun x hx => by rw [temps_gso _ _ hx.1, ho x hx]⟩
  · rintro le' m' ⟨-, -, bv', hb', hbv', hu, hkp, ho⟩
    exact hQ le' m' bv' hb' hbv' hu hkp ho

end

end NautyVerified.Proofs.Bestcell

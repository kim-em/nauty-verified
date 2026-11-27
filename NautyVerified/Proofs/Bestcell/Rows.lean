import NautyVerified.Proofs.Bestcell.Pair
import NautyVerified.Proofs.Bestcell.Starts

/-!
# The row loop of `bestcell`

`wp_addCell`: `do { ++i; ADDELEMENT(workset, lab[i]); } while (ptn[i] > level);`
from the start `s` of a cell builds HexGraphIso's `worksetOf n lab s (cellEnd …)`.
`wp_rows`: the loop over `v2 = 1 .. nnt-1` computes the counts as
`bestcellRows`, unrolled into `rowsStep`.
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Spec.Bestcell
open NautyVerified.Proofs.Set (longs addW)
open NautyVerified.Proofs.Alloc (Keep gat)
open NautyVerified.Proofs.Updatecan (tv labAt row)
open Hex.GraphIso.Nauty (VSet Ctx cellEnd worksetOf)

variable {xi : ExternalCalls}

/-- The first `k` members `lab[s], …, lab[s+k-1]` of a cell. -/
def part (n : Nat) (lab : Array Nat) (s k : Nat) : VSet n :=
  (List.range k).foldl (fun w o => w.insert lab[s + o]!) .empty

theorem part_succ (n : Nat) (lab : Array Nat) (s k : Nat) :
    part n lab s (k + 1) = (part n lab s k).insert lab[s + k]! := by
  simp only [part, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

section
variable {n : Nat} {bg : block} {gofs : ptrofs}
  {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bl : block} {lofs : ptrofs}
  {lab : Array Nat} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {level M : Nat}
  {bP bS bB : block}

theorem wp_addCell {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {ws : Nat → Lib.Integers.int64} (hws : ArrayAt m .Mint64 bS 0 (longs ws) M)
    (hW : SetRep (fun w => bv64 (ws w)) M (VSet.empty : VSet n))
    {s : Nat} (hs : s < n) (hi : PTree.get id.i le = some (.Vint (ir ((s : Int) - 1))))
    (hQ : ∀ le' m' ws', ArrayAt m' .Mint64 bS 0 (longs ws') M →
      SetRep (fun w => bv64 (ws' w)) M (worksetOf n lab s (cellEnd ptn level s)) →
      Unch m m' (· = bS) → Keep m m' bS →
      (∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» addCell Q empty_env le m := by
  have hnlt := h.nlt
  have hnM := h.nM
  have hMlt := h.Mlt
  have sp := cellEnd_spec h.psize hs h.plast
  obtain ⟨e, he⟩ : ∃ e, e = cellEnd ptn level s := ⟨_, rfl⟩
  rw [← he] at sp hQ
  have hown := h.owned bS (.inr (.inl rfl))
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k ws', s + k ≤ e ∧ v = e - s - k ∧
      PTree.get id.i le' = some (.Vint (ir ((s : Int) + k - 1))) ∧
      ArrayAt m' .Mint64 bS 0 (longs ws') M ∧ SetRep (fun w => bv64 (ws' w)) M (part n lab s k) ∧
      Unch m m' (· = bS) ∧ Keep m m' bS ∧ ∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ ∃ k ws', s + k ≤ e ∧ v = e - s - k ∧
      PTree.get id.i le' = some (.Vint (ir ((s + k : Nat) : Int))) ∧
      ArrayAt m' .Mint64 bS 0 (longs ws') M ∧
      SetRep (fun w => bv64 (ws' w)) M (part n lab s (k + 1)) ∧
      Unch m m' (· = bS) ∧ Keep m m' bS ∧ ∀ x, x ≠ id.i → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := e - s - 0)
    ⟨rfl, rfl, 0, ws, by omega, rfl, by simpa using hi, hws, by simpa [part] using hW,
      Unch.refl _ _, Keep.refl _ _, fun _ _ => rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, k, ws', hk, rfl, hik, hws', hW', hu, hkp, ho⟩
    have hf := (h.unch (m' := m') (hu.mono fun _ hz => .inr (.inl hz))).temps (le' := le')
      fun x hx => ho x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hik, typeof, cop, ir_add]
    simp only [E0_append]
    have hsk : s + k < n := by have := sp.2.1; omega
    let le2 := PTree.set id.i (.Vint (ir ((s : Int) + k - 1 + 1))) le'
    have hi2 : Exec.evalExpr ge empty_env le2 m' (tv id.i) = some (.Vint (ir ((s + k : Nat) : Int))) := by
      show PTree.get _ _ = _
      rw [temps_gss]; congr 3; push_cast; omega
    have hf2 := hf.temps (le' := le2) fun x hx => temps_gso _ _ (by
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hl := eval_lab hf2 (tv id.i) (s + k) hsk hi2 rfl
    have hlk := h.lsmall (s + k) hsk
    refine Set.wp_addElementG rfl find_naugraphWorkset hf2.wsP hws' (by omega) hl rfl (by omega)
      (by omega) rfl find_naugraphBit hf2.bit ?_
    intro m2 hws2 hu2 _ hk2
    refine ⟨rfl, rfl, k, addW ws' lab[s + k]!, hk, rfl, by rw [temps_gss]; congr 3; push_cast; omega,
      hws2, by rw [part_succ]; exact Set.setRep_add hW' hlk, hu.trans hu2, hkp.trans hk2,
      fun x hx => by rw [temps_gso _ _ hx, ho x hx]⟩
  · rintro v t e' le' m' ⟨rfl, rfl, k, ws', hk, rfl, hik, hws', hW', hu, hkp, ho⟩
    have hf := (h.unch (m' := m') (hu.mono fun _ hz => .inr (.inl hz))).temps (le' := le')
      fun x hx => ho x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hsk : s + k < n := by have := sp.2.1; omega
    wp_step; wp_step
    apply wp_if_eval
    rw [eval_ptnGt hf (s + k) hsk hik]
    simp only [typeof, cop]
    by_cases hend : s + k = e
    · rw [ite_eq_right (by simp; have := sp.2.2.1; rw [← hend] at this; omega)]
      apply wp_break
      refine hQ le' m' ws' hws' ?_ hu hkp ho
      rw [show worksetOf n lab s e = part n lab s (k + 1) by
        simp only [worksetOf, part]; rw [show e + 1 - s = k + 1 by omega]]
      exact hW'
    · have hgt := sp.2.2.2 (s + k) (by omega) (by omega)
      rw [ite_eq_left (by simpa using hgt)]
      apply wp_skip
      refine ⟨e - s - (k + 1), by omega, by simp, rfl, k + 1, ws', by omega, rfl, ?_, hws', hW', hu,
        hkp, ho⟩
      rw [hik]; congr 3; push_cast; omega

/-- The temporaries one row sets. -/
def RowT (x : Common.AST.ident) : Prop := PairT x ∧ x ≠ id.es ∧ x ≠ id.t12

theorem wp_rowBody {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {wv : Nat → val} (hw : ArrayAt m .Mint32 bP 0 wv n) {S : List Nat}
    (hwS : ∀ k < S.length, wv k = .Vint (ir (S[k]! : Int))) (hSn : ∀ k < S.length, S[k]! < n)
    {vals : Nat → val} (hws : ArrayAt m .Mint64 bS 0 vals M)
    {bv : Nat → val} (hb : ArrayAt m .Mint32 bB 0 bv (n + 2)) {B : Array Nat}
    (hbv : ∀ x < B.size, bv x = .Vint (ir (B[x]! : Int))) (hBs : B.size = S.length)
    (hSlen : S.length ≤ n) {k : Nat} (hk : k < S.length)
    (hv2v : PTree.get id.v2 le = some (.Vint (ir k)))
    (hQ : ∀ le' m' ws' bv', ArrayAt m' .Mint64 bS 0 (longs ws') M → ArrayAt m' .Mint32 bB 0 bv' (n + 2) →
      (∀ x < B.size, bv' x =
        .Vint (ir ((rowsStep ⟨grows⟩ lab ptn level S.toArray B k)[x]! : Int))) →
      Unch m m' (fun z => z = bS ∨ z = bB) → Keep m m' bS → Keep m m' bB →
      (∀ x, RowT x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» rowBody Q empty_env le m := by
  have hnlt := h.nlt
  have hMlt := h.Mlt
  have hown := h.owned bS (.inr (.inl rfl))
  simp only [rowBody]
  wp_step
  refine Set.wp_emptySetG (by decide) rfl find_naugraphWorkset h.wsP (Ne.symm hown.2.2.2.2.1) hws
    h.M1 (by omega) h.hm ?_
  intro le1 m1 hws1 hu1 _ hk1 ho1
  have hf1 := (h.unch (m' := m1) (hu1.mono fun _ hz => .inr (.inl hz))).temps (le' := le1)
    fun x hx => ho1 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hw1 := hw.unch hu1 h.dPS
  have hb1 := hb.unch hu1 h.dSB.symm
  have hv2' : PTree.get id.v2 le1 = some (.Vint (ir k)) := by
    rw [ho1 _ (by decide) (by decide)]; exact hv2v
  have hsk := hSn k hk
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_wp hf1 hw1 (tv id.v2) k (by omega) hv2' rfl, hwS k hk]
  simp only [Exec.evalExpr, typeof, cop, ir_sub, E0_append]
  let le2 := PTree.set id.i (.Vint (ir ((S[k]! : Int) - 1))) le1
  have hf2 := hf1.temps (le' := le2) fun x hx => temps_gso _ _ (by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  wp_step
  refine wp_addCell hf2 hws1 (Set.setRep_zero h.nM) hsk (temps_gss _ _ _) ?_
  intro le3 m3 ws3 hws3 hW3 hu3 hk3 ho3
  have hf3 := (hf2.unch (m' := m3) (hu3.mono fun _ hz => .inr (.inl hz))).temps (le' := le3)
    fun x hx => ho3 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine wp_pairs hf3 (hw1.unch hu3 h.dPS) hwS hSn hws3 hW3 (hb1.unch hu3 h.dSB.symm) hbv hBs hSlen
    hk (by rw [ho3 _ (by decide), temps_gso _ _ (by decide)]; exact hv2') ?_
  intro le4 m4 bv4 hb4 hbv4 hu4 hk4 ho4
  refine hQ le4 m4 ws3 bv4 (hws3.unch hu4 h.dSB) hb4 (fun x hx => ?_)
    (((hu1.mono fun _ hz => .inl hz).trans (hu3.mono fun _ hz => .inl hz)).trans
      (hu4.mono fun _ hz => .inr hz))
    ((hk1.trans hk3).trans (Keep.unch hu4 h.dSB))
    ((Keep.unch hu1 h.dSB.symm).trans ((Keep.unch hu3 h.dSB.symm).trans hk4)) fun x hx => ?_
  · rw [hbv4 x hx]; simp only [rowsStep, List.getElem!_toArray]
  · rw [ho4 x hx.1, ho3 x hx.1.2.2.2.2.2.1, temps_gso _ _ hx.1.2.2.2.2.2.1, ho1 x hx.2.1 hx.2.2]

theorem size_rows (ctx : Ctx n) (startArr : Array Nat) :
    ∀ (l : List Nat) (B : Array Nat),
      (l.foldl (rowsStep ctx lab ptn level startArr) B).size = B.size
  | [], _ => rfl
  | v2 :: l, B => by
    rw [List.foldl_cons, size_rows ctx startArr l, rowsStep, size_row]

theorem wp_rows {Q : Post} {le : temp_env} {m : mem}
    (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {wv : Nat → val} (hw : ArrayAt m .Mint32 bP 0 wv n) {S : List Nat}
    (hwS : ∀ k < S.length, wv k = .Vint (ir (S[k]! : Int))) (hSn : ∀ k < S.length, S[k]! < n)
    {vals : Nat → val} (hws : ArrayAt m .Mint64 bS 0 vals M)
    {bv : Nat → val} (hb : ArrayAt m .Mint32 bB 0 bv (n + 2))
    (hbv : ∀ x < S.length, bv x = .Vint (ir 0)) (hSlen : S.length ≤ n) (hS1 : 1 ≤ S.length)
    (hnnt : PTree.get id.nnt le = some (.Vint (ir (S.length : Int))))
    (hQ : ∀ le' m' bv', ArrayAt m' .Mint32 bB 0 bv' (n + 2) →
      (∀ x < S.length, bv' x = .Vint (ir (((List.range' 1 (S.length - 1)).foldl
        (rowsStep ⟨grows⟩ lab ptn level S.toArray) (Array.replicate S.length 0))[x]! : Int))) →
      Unch m m' (fun z => z = bS ∨ z = bB) → Keep m m' bS → Keep m m' bB →
      (∀ x, RowT x → x ≠ id.v2 → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi ge Source.dense.fn.«naugraph:bestcell» rows Q empty_env le m := by
  have hnlt := h.nlt
  let K := S.length
  let Bk := fun k => (List.range' 1 (k - 1)).foldl (rowsStep ⟨grows⟩ lab ptn level S.toArray)
    (Array.replicate K 0)
  have hBk : ∀ k, (Bk k).size = K := fun k => by simp only [Bk]; rw [size_rows]; simp
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) => 1 ≤ k ∧ k ≤ K ∧
    PTree.get id.v2 le' = some (.Vint (ir k)) ∧ (∃ vals', ArrayAt m' .Mint64 bS 0 vals' M) ∧
    ∃ bv', ArrayAt m' .Mint32 bB 0 bv' (n + 2) ∧ (∀ x < K, bv' x = .Vint (ir ((Bk k)[x]! : Int))) ∧
      Unch m m' (fun z => z = bS ∨ z = bB) ∧ Keep m m' bS ∧ Keep m m' bB ∧
      ∀ x, RowT x → x ≠ id.v2 → PTree.get x le' = PTree.get x le
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    PTree.get id.v2 le' = some (.Vint (ir k)) ∧ 1 ≤ k ∧ k < K ∧
    (∃ vals', ArrayAt m' .Mint64 bS 0 vals' M) ∧
    ∃ bv', ArrayAt m' .Mint32 bB 0 bv' (n + 2) ∧
      (∀ x < K, bv' x = .Vint (ir ((Bk (k + 1))[x]! : Int))) ∧
      Unch m m' (fun z => z = bS ∨ z = bB) ∧ Keep m m' bS ∧ Keep m m' bB ∧
      ∀ x, RowT x → x ≠ id.v2 → PTree.get x le' = PTree.get x le
  have hR : RowT id.nnt := by unfold RowT PairT; decide
  refine wp_forLoopFrom id.v2 id.nnt rowBody 1 K hS1 (by omega) Inv Mid ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk1, hk, hv2, -, -, -, -, -, -, -, ho⟩
    exact ⟨hk1, hk, hv2, by rw [ho _ hR (by decide)]; exact hnnt⟩
  · refine ⟨Nat.le_refl _, hS1, temps_gss _ _ _, ⟨vals, hws⟩, bv, hb, fun x hx => ?_, Unch.refl _ _,
      Keep.refl _ _, Keep.refl _ _, fun x _ hx => temps_gso _ _ hx⟩
    rw [hbv x hx]; simp only [Bk, Nat.sub_self, List.range'_zero, List.foldl_nil, get_rep]; rfl
  · rintro k le' m' hk1 hk ⟨-, -, hv2, ⟨vals', hws'⟩, bv', hb', hbv', hu, hk2, hk3, ho⟩
    have hf := (h.unch (m' := m') (hu.mono fun _ hz => .inr hz)).temps (le' := le')
      fun x hx => ho x (by
        unfold RowT PairT; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    refine wp_rowBody hf (hw.unch hu (by rintro (h1 | h1); exact h.dPS h1; exact h.dPB h1)) hwS hSn
      hws' hb' (B := Bk k) (fun x hx => by rw [hBk] at hx; exact hbv' x hx) (hBk k) hSlen hk hv2 ?_
    intro le2 m2 ws2 bv2 hws2 hb2 hbv2 hu2 hk2' hk3' ho2
    refine ⟨rfl, by rw [ho2 _ (by unfold RowT PairT; decide)]; exact hv2, hk1, hk, ⟨_, hws2⟩, bv2, hb2,
      fun x hx => ?_, hu.trans hu2, hk2.trans hk2', hk3.trans hk3', fun x hx hx2 => by
        rw [ho2 x hx, ho x hx hx2]⟩
    rw [hbv2 x (by rw [hBk]; exact hx)]
    simp only [Bk]
    rw [show k + 1 - 1 = (k - 1) + 1 by omega, List.range'_concat, List.foldl_append,
      List.foldl_cons, List.foldl_nil, show 1 + 1 * (k - 1) = k by omega]
  · rintro k le' m' ⟨hv2, hk1, hk, hws', bv', hb', hbv', hu, hk2, hk3, ho⟩
    exact ⟨hv2, by omega, by omega, temps_gss _ _ _, hws', bv', hb', hbv', hu, hk2, hk3,
      fun x hx hx2 => by rw [temps_gso _ _ hx2, ho x hx hx2]⟩
  · rintro le' m' ⟨-, -, -, -, bv', hb', hbv', hu, hk2, hk3, ho⟩
    exact hQ le' m' bv' hb' hbv' hu hk2 hk3 ho

end

end NautyVerified.Proofs.Bestcell

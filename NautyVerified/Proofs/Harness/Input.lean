import NautyVerified.Proofs.Harness.Loop
import NautyVerified.Proofs.Refine.Finish

/-!
# Reading the colours

`wp_colours`: `for (i = 0; i < n; ++i) { colour[i] = (int)nv_read(); if
(colour[i] > maxc) maxc = colour[i]; }`, with the reads returning `cs`,
leaves `cs` in `colour` and their maximum in `maxc`.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)

/-- The first `k` of `cs`, then zeros, as an `N`-entry array. -/
def prefixArr (cs : List Nat) (N k : Nat) : Array Nat :=
  Array.ofFn (n := N) fun j => if j.val < k then cs[j.val]! else 0

theorem prefixArr_get {cs : List Nat} {N k j : Nat} (hj : j < N) :
    (prefixArr cs N k)[j]! = if j < k then cs[j]! else 0 := by
  simp [prefixArr, hj]

theorem ints_prefixArr_succ {cs : List Nat} {N k j : Nat} (hj : j < N) :
    upd (ints (prefixArr cs N k)) k (.Vint (ir (cs[k]! : Int))) j =
      ints (prefixArr cs N (k + 1)) j := by
  simp only [upd, ints]
  rw [prefixArr_get hj]
  split
  · rename_i h; subst h; rw [prefixArr_get hj]; simp
  · rename_i h
    rw [prefixArr_get hj]
    by_cases hjk : j < k
    · simp [hjk, show j < k + 1 by omega]
    · simp [hjk, show ¬ j < k + 1 by omega]

/-- The maximum of the first `k` of `cs` (and 0). -/
def maxPrefix (cs : List Nat) (k : Nat) : Nat := (cs.take k).foldl max 0

theorem maxPrefix_succ {cs : List Nat} {k : Nat} (hk : k < cs.length) :
    maxPrefix cs (k + 1) = max (maxPrefix cs k) cs[k]! := by
  simp only [maxPrefix]
  rw [List.take_add_one, List.foldl_append]
  simp [List.getElem?_eq_getElem hk, getElem!_pos cs k hk]

theorem foldl_max_lt {B : Nat} : ∀ (l : List Nat) (a : Nat), a < B → (∀ x ∈ l, x < B) →
    l.foldl max a < B
  | [], _, ha, _ => ha
  | x :: l, a, ha, hl => foldl_max_lt l (max a x) (by have := hl x (by simp); omega)
      fun y hy => hl y (by simp [hy])

theorem maxPrefix_lt {cs : List Nat} {B k : Nat} (hB : 0 < B) (h : ∀ j < cs.length, cs[j]! < B) :
    maxPrefix cs k < B :=
  foldl_max_lt _ 0 hB fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_take hx)
    have := h j hj
    rwa [getElem!_pos cs j hj] at this

/-- The body of the colour loop. -/
abbrev colourBody : statement :=
  .Ssequence
    (.Ssequence (sk (rd (idOf 710)))
      (.Sassign (ix dense.id.colour (tv dense.id.i)) (.Ecast (.Etempvar (idOf 710) tlong) tint)))
    (sk (.Sifthenelse (.Ebinop .Ogt (ix dense.id.colour (tv dense.id.i)) (tv dense.id.maxc) tint)
      (sk (.Sset dense.id.maxc (ix dense.id.colour (tv dense.id.i)))) .Sskip))

theorem colourLoop_eq :
    .Ssequence (sk (.Sset dense.id.i (ci 0 tint))) colourLoop =
      forT dense.id.i (tv dense.id.n) colourBody := rfl

theorem wp_colours {Q : Post} {e : env} {le : temp_env} {m : mem} {bcol : block} {N : Nat}
    (cs : List Nat) (hlen : cs.length = N) (hN : N < 2147483648)
    (hcs : ∀ j < N, cs[j]! < 2147483648)
    (he : PTree.get dense.id.nv_read e = none)
    (hcol : PTree.get dense.id.colour le = some (.Vptr bcol Ptrofs.zero))
    (hn : PTree.get dense.id.n le = some (.Vint (ir N)))
    (hmaxc : PTree.get dense.id.maxc le = some (.Vint (ir 0)))
    (harr : ArrayAt m .Mint32 bcol 0 (ints (prefixArr cs N 0)) N)
    (hQ : ∀ t le' m', Reads t (cs.map (fun c : Nat => (c : Int))) →
      ArrayAt m' .Mint32 bcol 0 (ints (prefixArr cs N N)) N → Unch m m' (· = bcol) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      PTree.get dense.id.maxc le' = some (.Vint (ir (maxPrefix cs N))) →
      (∀ x, x ≠ dense.id.i → x ≠ dense.id.maxc → x ≠ idOf 710 → PTree.get x le' = PTree.get x le) →
      Q.normal t e le' m') :
    Wp Statement.xi ge dense.fn.main (forT dense.id.i (tv dense.id.n) colourBody) Q e le m := by
  let Inv := fun (k : Nat) (t : trace) (le' : temp_env) (m' : mem) =>
    k ≤ N ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
    Reads t ((cs.take k).map (fun c : Nat => (c : Int))) ∧
    ArrayAt m' .Mint32 bcol 0 (ints (prefixArr cs N k)) N ∧ Unch m m' (· = bcol) ∧
    PTree.get dense.id.maxc le' = some (.Vint (ir (maxPrefix cs k))) ∧
    (∀ x, x ≠ dense.id.i → x ≠ dense.id.maxc → x ≠ idOf 710 → PTree.get x le' = PTree.get x le) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  refine wp_forT (Inv := Inv) dense.id.i (tv dense.id.n) colourBody N hN ?_ ?_ ?_ ?_
  · rintro k t le' m' ⟨hk, hi, -, -, -, -, ho, -⟩
    refine ⟨hk, hi, ?_, rfl⟩
    show PTree.get _ _ = _
    rw [ho _ (by decide) (by decide) (by decide)]; exact hn
  · refine ⟨Nat.zero_le _, temps_gss _ _ _, Reads.nil, harr, Unch.refl _ _, ?_,
      fun x h1 _ _ => temps_gso _ _ h1, fun _ h => h⟩
    rw [temps_gso _ _ (by decide)]; exact hmaxc
  · rintro k t le' m' hk ⟨-, hi, hr, ha, hu, hmx, ho, hgr⟩
    have hck := hcs k hk
    have hcol' : PTree.get dense.id.colour le' = some (.Vptr bcol Ptrofs.zero) := by
      rw [ho _ (by decide) (by decide) (by decide)]; exact hcol
    wp_step; wp_step; wp_step; wp_step
    refine wp_rd (idOf 710) (lr (cs[k]! : Int)) he ?_
    dsimp only
    let le1 := PTree.set (idOf 710) (.Vlong (lr (cs[k]! : Int))) le'
    have hi1 : PTree.get dense.id.i le1 = some (.Vint (ir k)) := by
      rw [temps_gso _ _ (by decide)]; exact hi
    have hrhs : Exec.evalExpr ge e le1 m' (.Ecast (.Etempvar (idOf 710) tlong) tint) =
        some (.Vint (ir (cs[k]! : Int))) := by
      simp only [Exec.evalExpr, le1, temps_gss, typeof, cop]
      rw [Refine.repr_unsigned_lr hck]
    refine wp_storeV ha hN dense.id.colour (by rw [temps_gso _ _ (by decide)]; exact hcol')
      (tv dense.id.i) k hk hi1 rfl _ (cs[k]! : Int) hrhs rfl ?_
    intro m1 ha1 hu1 hg1
    have ha1' : ArrayAt m1 .Mint32 bcol 0 (ints (prefixArr cs N (k + 1))) N :=
      ha1.congr fun j hj => ints_prefixArr_succ hj
    have hel : Exec.evalExpr ge e le1 m1 (ix dense.id.colour (tv dense.id.i)) =
        some (.Vint (ir (cs[k]! : Int))) := by
      rw [eval_at ha1' hN dense.id.colour (by rw [temps_gso _ _ (by decide)]; exact hcol')
        (tv dense.id.i) k hk hi1 rfl]
      simp [ints, prefixArr_get hk]
    have hmx1 : PTree.get dense.id.maxc le1 = some (.Vint (ir (maxPrefix cs k))) := by
      rw [temps_gso _ _ (by decide)]; exact hmx
    have hmk : maxPrefix cs k < 2147483648 :=
      maxPrefix_lt (by decide) fun j hj => hcs j (by omega)
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hel, show Exec.evalExpr ge e le1 m1 (tv dense.id.maxc) = _ from hmx1]
    simp only [typeof, cop]
    rw [ir_lt (a := (maxPrefix cs k : Int)) (b := (cs[k]! : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    have hms := maxPrefix_succ (cs := cs) (k := k) (by omega)
    have hrk : Reads (t ++ tr1 (readEv (lr (cs[k]! : Int))))
        ((cs.take (k + 1)).map (fun c : Nat => (c : Int))) := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.map_append]
      refine hr.append ?_
      have := Reads.one (lr (cs[k]! : Int))
      rw [signed_lr (by omega) (by omega)] at this
      simpa [getElem!_pos cs k (by omega)] using this
    by_cases hgt : maxPrefix cs k < cs[k]!
    · rw [ite_eq_left (by simpa using hgt)]
      wp_step; wp_step
      apply wp_set_eval
      rw [hel]
      refine ⟨by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hi, by omega,
        temps_gss _ _ _, ?_, ha1', hu.trans hu1, ?_, ?_, ?_⟩
      · exact hrk
      · rw [temps_gso _ _ (by decide), temps_gss, hms, Nat.max_eq_right (by omega)]
      · intro x h1 h2 h3
        rw [temps_gso _ _ h1, temps_gso _ _ h2, temps_gso _ _ h3, ho x h1 h2 h3]
      · exact fun z hz => hg1 _ (hgr _ hz)
    · rw [ite_eq_right (by simpa using hgt)]
      apply wp_skip
      refine ⟨by rw [temps_gso _ _ (by decide)]; exact hi, by omega,
        temps_gss _ _ _, ?_, ha1', hu.trans hu1, ?_, ?_, ?_⟩
      · exact hrk
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), hms, Nat.max_eq_left (by omega)]
        exact hmx
      · intro x h1 h2 h3
        rw [temps_gso _ _ h1, temps_gso _ _ h3, ho x h1 h2 h3]
      · exact fun z hz => hg1 _ (hgr _ hz)
  · rintro t le' m' ⟨-, -, hr, ha, hu, hmx, ho, hgr⟩
    refine hQ t le' m' ?_ ha hu hgr hmx ho
    rwa [List.take_of_length_le (show cs.length ≤ N by omega)] at hr

end NautyVerified.Proofs.Harness

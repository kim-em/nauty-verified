import NautyVerified.Proofs.Refine.State
import NautyVerified.Proofs.Nextelement.Leftbit

/-!
# `POPCOUNT` and the neighbour-count loop

`eval_popcount`: nauty's table `POPCOUNT(x)` (eight `bytecount` lookups)
evaluates to `popCount` of the word. `wp_popLoop`: the loop
`for (c1 = m; --c1 >= 0;) if ((x = *set1++ & *set2++) != 0) cnt += POPCOUNT(x);`
adds the number of common bits of two `m`-word sets. `cardInter_words`: that
number is `VSet.cardInter` of the sets the words represent.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs
open NautyVerified.Proofs.Init (BytecountTable)
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty (popCount)

variable {xi : ExternalCalls}

theorem eval_byteAt {e : env} {le : temp_env} {m : mem} (w : Lib.Integers.int64)
    (hx : PTree.get dense.id.x le = some (.Vlong w)) (hbt : BytecountTable m)
    (he : PTree.get dense.id.«naugraph:bytecount» e = none) (k : Nat) (hk : k < 64)
    (hlt : Lib.Integers.Int.ltu (Lib.Integers.Int.repr (zOfInt k)) Int64.iwordsize' = true) :
    Exec.evalExpr ge e le m (byteAt k) =
      some (.Vint (ir (popCount ((bv64 w).toNat / 2 ^ k % 256)))) := by
  simp only [Exec.evalExpr, hx, Exec.lvalOfVar, he, find_naugraphBytecount]
  simp only [typeof, cop, hlt, ite_true, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  rw [show Cfrontend.Cop.cast_int_long Cfrontend.Ctypes.Signed (Lib.Integers.Int.repr (zOfInt 255)) =
    lr 255 from cast_int_long_ir (a := 255) ⟨by decide, by decide⟩]
  have hy : (bv64 (Int64.and (Int64.shru w (Int64.repr (Int.unsigned
      (Lib.Integers.Int.repr (zOfInt (k : Int)))))) (lr 255))).toNat =
      (bv64 w).toNat / 2 ^ k % 256 := by
    rw [bv64_and, BitVec.toNat_and, Nextelement.shr_toNat w k (by omega) (by omega)]
    simp only [bv64_repr, intOfZ_zOfInt, BitVec.toNat_ofInt]
    rw [show (((255 : Int) % ((2 ^ 64 : Nat) : Int)).toNat) = 2 ^ 8 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Int.toNat_natCast]
  show Mem.load _ _ _ _ = _
  rw [Nextelement.ofs_leftbit _ _ (by rw [hy]; exact Nat.mod_lt _ (by decide)), hy]
  exact hbt _ (Nat.mod_lt _ (by decide))

theorem eval_byte0 {e : env} {le : temp_env} {m : mem} (w : Lib.Integers.int64)
    (hx : PTree.get dense.id.x le = some (.Vlong w)) (hbt : BytecountTable m)
    (he : PTree.get dense.id.«naugraph:bytecount» e = none) :
    Exec.evalExpr ge e le m byte0 = some (.Vint (ir (popCount ((bv64 w).toNat % 256)))) := by
  simp only [Exec.evalExpr, hx, Exec.lvalOfVar, he, find_naugraphBytecount]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  rw [show Cfrontend.Cop.cast_int_long Cfrontend.Ctypes.Signed (Lib.Integers.Int.repr (zOfInt 255)) =
    lr 255 from cast_int_long_ir (a := 255) ⟨by decide, by decide⟩]
  have hy : (bv64 (Int64.and w (lr 255))).toNat = (bv64 w).toNat % 256 := by
    rw [bv64_and, BitVec.toNat_and]
    simp only [bv64_repr, intOfZ_zOfInt, BitVec.toNat_ofInt]
    rw [show (((255 : Int) % ((2 ^ 64 : Nat) : Int)).toNat) = 2 ^ 8 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
  show Mem.load _ _ _ _ = _
  rw [Nextelement.ofs_leftbit _ _ (by rw [hy]; exact Nat.mod_lt _ (by decide)), hy]
  exact hbt _ (Nat.mod_lt _ (by decide))

/-- `a + b` of two `int`s. -/
theorem eval_add_ii {e : env} {le : temp_env} {m : mem} {a b : expr} {x y : Int}
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir x))) (hta : typeof a = tint)
    (hb : Exec.evalExpr ge e le m b = some (.Vint (ir y))) (htb : typeof b = tint) :
    Exec.evalExpr ge e le m (.Ebinop .Oadd a b tint) = some (.Vint (ir (x + y))) := by
  rw [Exec.evalExpr, ha, hb, hta, htb]
  simp only [cop, ir_add]

/-- `popCount` from the eight bytes, most significant first. -/
theorem popCount_bytes (x : Nat) (hx : x < 2 ^ 64) :
    popCount (x / 2 ^ 56 % 256) + popCount (x / 2 ^ 48 % 256) + popCount (x / 2 ^ 40 % 256) +
      popCount (x / 2 ^ 32 % 256) + popCount (x / 2 ^ 24 % 256) + popCount (x / 2 ^ 16 % 256) +
      popCount (x / 2 ^ 8 % 256) + popCount (x % 256) = popCount x := by
  have step : ∀ k, popCount (x / 2 ^ k) = popCount (x / 2 ^ k % 256) + popCount (x / 2 ^ (k + 8)) := by
    intro k
    rw [Hex.GraphIso.Nauty.popCount_split_pow 8 (x / 2 ^ k), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h0 : popCount (x / 2 ^ 0) = popCount (x / 2 ^ 0 % 256) + popCount (x / 2 ^ 8) := step 0
  have h8 : popCount (x / 2 ^ 8) = popCount (x / 2 ^ 8 % 256) + popCount (x / 2 ^ 16) := step 8
  have h16 : popCount (x / 2 ^ 16) = popCount (x / 2 ^ 16 % 256) + popCount (x / 2 ^ 24) := step 16
  have h24 : popCount (x / 2 ^ 24) = popCount (x / 2 ^ 24 % 256) + popCount (x / 2 ^ 32) := step 24
  have h32 : popCount (x / 2 ^ 32) = popCount (x / 2 ^ 32 % 256) + popCount (x / 2 ^ 40) := step 32
  have h40 : popCount (x / 2 ^ 40) = popCount (x / 2 ^ 40 % 256) + popCount (x / 2 ^ 48) := step 40
  have h48 : popCount (x / 2 ^ 48) = popCount (x / 2 ^ 48 % 256) + popCount (x / 2 ^ 56) := step 48
  have h56 : popCount (x / 2 ^ 56) = popCount (x / 2 ^ 56 % 256) + popCount (x / 2 ^ 64) := step 56
  have h64 : x / 2 ^ 64 = 0 := Nat.div_eq_of_lt hx
  rw [h64, Hex.GraphIso.Nauty.popCount_zero] at h56
  simp only [Nat.pow_zero, Nat.div_one] at h0
  omega

theorem eval_popcount {e : env} {le : temp_env} {m : mem} (w : Lib.Integers.int64)
    (hx : PTree.get dense.id.x le = some (.Vlong w)) (hbt : BytecountTable m)
    (he : PTree.get dense.id.«naugraph:bytecount» e = none) :
    Exec.evalExpr ge e le m popcount = some (.Vint (ir (popCount (bv64 w).toNat))) := by
  have hb := fun k hk hlt => eval_byteAt (e := e) (le := le) (m := m) w hx hbt he k hk hlt
  rw [← popCount_bytes _ (bv64 w).isLt]
  simp only [popcount]
  push_cast
  refine eval_add_ii (eval_add_ii (eval_add_ii (eval_add_ii (eval_add_ii (eval_add_ii
    (eval_add_ii (hb 56 (by decide) (by decide)) rfl (hb 48 (by decide) (by decide)) rfl) rfl
    (hb 40 (by decide) (by decide)) rfl) rfl (hb 32 (by decide) (by decide)) rfl) rfl
    (hb 24 (by decide) (by decide)) rfl) rfl (hb 16 (by decide) (by decide)) rfl) rfl
    (hb 8 (by decide) (by decide)) rfl) rfl (eval_byte0 w hx hbt he) rfl

/-- `popCount` of a word counts its bits from the most significant end. -/
theorem popCount_msb (x : BitVec 64) :
    popCount x.toNat = (List.range 64).countP fun j => x.getMsbD j := by
  rw [Hex.GraphIso.Nauty.popCount_eq_bitCount 64 _ x.isLt, Hex.GraphIso.Nauty.bitCount]
  have h1 : ((List.range 64).countP fun i => x.toNat.testBit i) =
      (List.range 64).countP ((fun j => x.getMsbD j) ∘ fun i => 0 + 64 - 1 - i) := by
    apply List.countP_congr
    intro i hi
    have hi := List.mem_range.mp hi
    simp only [BitVec.testBit_toNat, BitVec.getLsbD_eq_getMsbD, Function.comp, hi, decide_true,
      Bool.true_and]
  rw [h1, ← List.countP_map, ← List.reverse_range', List.countP_reverse, ← List.range_eq_range']

/-- Counting below `64 * M` word by word. -/
theorem countP_words (f : Nat → Bool) :
    ∀ M, (List.range (64 * M)).countP f =
      ((List.range M).map fun w => (List.range 64).countP fun j => f (64 * w + j)).sum
  | 0 => by simp
  | M + 1 => by
    rw [show 64 * (M + 1) = 64 * M + 64 by omega, List.range_add, List.countP_append,
      countP_words f M, List.range_succ (n := M), List.map_append, List.sum_append, List.countP_map]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rfl

/-- The common bits of two `M`-word sets, word by word, are `VSet.cardInter`. -/
theorem cardInter_words {n M : Nat} {a b : Nat → Lib.Integers.int64} {s t : Hex.GraphIso.Nauty.VSet n}
    (hs : SetRep (fun w => bv64 (a w)) M s) (ht : SetRep (fun w => bv64 (b w)) M t) :
    ((List.range M).map fun w => popCount (bv64 (Int64.and (a w) (b w))).toNat).sum =
      s.cardInter t := by
  rw [Hex.GraphIso.Nauty.VSet.cardInter_eq, Hex.GraphIso.Nauty.VSet.card_eq_countBelow,
    Hex.GraphIso.Nauty.VSet.countBelow]
  have hn := hs.1
  have hsplit : (List.range (64 * M)).countP (s.inter t).mem =
      (List.range n).countP (s.inter t).mem := by
    rw [show 64 * M = n + (64 * M - n) by omega, List.range_add, List.countP_append,
      List.countP_map]
    have h0 : List.countP ((s.inter t).mem ∘ fun x => n + x) (List.range (64 * M - n)) = 0 :=
      List.countP_eq_zero.mpr fun v _ hv => by
        rw [Function.comp_apply] at hv
        exact absurd (Hex.GraphIso.Nauty.VSet.mem_lt hv) (by omega)
    rw [h0, Nat.add_zero]
  rw [← hsplit, countP_words]
  congr 1
  apply List.map_congr_left
  intro w hw
  have hw := List.mem_range.mp hw
  rw [bv64_and, popCount_msb]
  apply List.countP_congr
  intro j hj
  have hj := List.mem_range.mp hj
  have hv : 64 * w + j < 64 * M := by omega
  have e1 : (64 * w + j) / 64 = w := by omega
  have e2 : (64 * w + j) % 64 = j := by omega
  rw [Hex.GraphIso.Nauty.VSet.mem_inter, ← hs.2 _ hv, ← ht.2 _ hv]
  simp only [SetwordsMem, e1, e2, BitVec.getMsbD_and]

/-- Entries `i < j` of a list of pairwise distinct elements differ. -/
theorem pwNe {α : Type} {l : List α} (h : l.Pairwise (· ≠ ·)) (i j : Nat) (hij : i < j)
    (hj : j < l.length) : l[i]'(Nat.lt_trans hij hj) ≠ l[j] := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => exact h.1 _ (List.getElem_mem _)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih h.2 i j (by omega) (by simpa using hj)

/-- `p + 1` for an `unsigned long *` at element `j`. -/
theorem add_ptr8 (ce : Cfrontend.Ctypes.composite_env) (base : Int) (j : Nat) :
    Ptrofs.add (ptrTo base 8 j) (Ptrofs.mul (Ptrofs.repr (Cfrontend.Ctypes.sizeof ce tulong))
      (Ptrofs.of_ints (ir 1))) = ptrTo base 8 (j + 1) := by
  have h := add_ptrTo_ptrTo base (Cfrontend.Ctypes.sizeof ce tulong) j 1 (by decide)
  rw [show intOfZ (Cfrontend.Ctypes.sizeof ce tulong) = 8 from rfl] at h
  exact h

/-- Reading word `j` through a pointer to it. -/
theorem load_ptr8 {m : mem} {b : block} {base : Int} {ws : Nat → Lib.Integers.int64} {M : Nat}
    (harr : ArrayAt m .Mint64 b base (longs ws) M) {j : Nat} (hj : j < M) :
    Mem.loadv .Mint64 m (.Vptr b (ptrTo base 8 j)) = some (.Vlong (ws j)) := by
  show Mem.load _ _ _ _ = _
  have hf := harr.fits
  have h0 := harr.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  have hu := unsigned_ptrTo (base := base) (sz := 8) (k := j) (by omega) (by omega)
  rw [show Ptrofs.unsigned (ptrTo base 8 j) = elemOfs .Mint64 base j by
    unfold elemOfs; rw [h8, ← hu, zOfInt_intOfZ]]
  exact harr.load j hj

/-- The common-bit count of the first `j` words. -/
abbrev pops (a b : Nat → Lib.Integers.int64) (j : Nat) : Nat :=
  ((List.range j).map fun w => popCount (bv64 (Int64.and (a w) (b w))).toNat).sum

theorem pops_succ (a b : Nat → Lib.Integers.int64) (j : Nat) :
    pops a b (j + 1) = pops a b j + popCount (bv64 (Int64.and (a j) (b j))).toNat := by
  simp [pops, List.range_succ]

theorem pops_le (a b : Nat → Lib.Integers.int64) : ∀ j, pops a b j ≤ 64 * j
  | 0 => by simp [pops]
  | j + 1 => by
    rw [pops_succ]
    have := pops_le a b j
    have : popCount (bv64 (Int64.and (a j) (b j))).toNat ≤ 64 := by
      rw [popCount_msb]
      exact Nat.le_trans (List.countP_le_length) (by simp)
    omega

/-- `for (c1 = m; --c1 >= 0;) if ((x = *set1++ & *set2++) != 0) cnt += POPCOUNT(x);` -/
theorem wp_popLoop {f : function} {Q : Post} {le : temp_env} {m : mem} {a b c d : Common.AST.ident}
    (hd : [dense.id.c1, a, b, c, d, dense.id.x, dense.id.set1, dense.id.set2, dense.id.cnt,
      dense.id.m].Pairwise (· ≠ ·))
    {bA bB : block} {baseA baseB : Int} {wa wb : Nat → Lib.Integers.int64} {M k : Nat}
    (ha : ArrayAt m .Mint64 bA baseA (longs wa) M) (hb : ArrayAt m .Mint64 bB baseB (longs wb) M)
    (hs1 : PTree.get dense.id.set1 le = some (.Vptr bA (ptrTo baseA 8 0)))
    (hs2 : PTree.get dense.id.set2 le = some (.Vptr bB (ptrTo baseB 8 0)))
    (hm : PTree.get dense.id.m le = some (.Vint (ir M)))
    (hc : PTree.get dense.id.cnt le = some (.Vint (ir k)))
    (hk : k + 64 * M < 2147483648) (hbt : BytecountTable m)
    (hQ : ∀ le', PTree.get dense.id.cnt le' = some (.Vint (ir (k + pops wa wb M : Nat))) →
      (∀ z, z ≠ dense.id.c1 → z ≠ a → z ≠ b → z ≠ c → z ≠ d → z ≠ dense.id.x →
        z ≠ dense.id.set1 → z ≠ dense.id.set2 → z ≠ dense.id.cnt →
        PTree.get z le' = PTree.get z le) →
      Q.normal E0 empty_env le' m) :
    Wp xi ge f (popLoop a b c d) Q empty_env le m := by
  have n01 := pwNe hd 0 1 (by decide) (by simp)
  have n02 := pwNe hd 0 2 (by decide) (by simp)
  have n03 := pwNe hd 0 3 (by decide) (by simp)
  have n04 := pwNe hd 0 4 (by decide) (by simp)
  have n05 := pwNe hd 0 5 (by decide) (by simp)
  have n06 := pwNe hd 0 6 (by decide) (by simp)
  have n07 := pwNe hd 0 7 (by decide) (by simp)
  have n08 := pwNe hd 0 8 (by decide) (by simp)
  have n12 := pwNe hd 1 2 (by decide) (by simp)
  have n13 := pwNe hd 1 3 (by decide) (by simp)
  have n14 := pwNe hd 1 4 (by decide) (by simp)
  have n15 := pwNe hd 1 5 (by decide) (by simp)
  have n16 := pwNe hd 1 6 (by decide) (by simp)
  have n17 := pwNe hd 1 7 (by decide) (by simp)
  have n18 := pwNe hd 1 8 (by decide) (by simp)
  have n23 := pwNe hd 2 3 (by decide) (by simp)
  have n24 := pwNe hd 2 4 (by decide) (by simp)
  have n25 := pwNe hd 2 5 (by decide) (by simp)
  have n26 := pwNe hd 2 6 (by decide) (by simp)
  have n27 := pwNe hd 2 7 (by decide) (by simp)
  have n28 := pwNe hd 2 8 (by decide) (by simp)
  have n34 := pwNe hd 3 4 (by decide) (by simp)
  have n35 := pwNe hd 3 5 (by decide) (by simp)
  have n36 := pwNe hd 3 6 (by decide) (by simp)
  have n37 := pwNe hd 3 7 (by decide) (by simp)
  have n38 := pwNe hd 3 8 (by decide) (by simp)
  have n45 := pwNe hd 4 5 (by decide) (by simp)
  have n46 := pwNe hd 4 6 (by decide) (by simp)
  have n47 := pwNe hd 4 7 (by decide) (by simp)
  have n48 := pwNe hd 4 8 (by decide) (by simp)
  have n09 := pwNe hd 0 9 (by decide) (by simp)
  have n19 := pwNe hd 1 9 (by decide) (by simp)
  have n29 := pwNe hd 2 9 (by decide) (by simp)
  have n39 := pwNe hd 3 9 (by decide) (by simp)
  have n49 := pwNe hd 4 9 (by decide) (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at *
  have hM : M < 33554432 := by omega
  let Oth := fun le' : temp_env => ∀ z, z ≠ dense.id.c1 → z ≠ a → z ≠ b → z ≠ c → z ≠ d →
    z ≠ dense.id.x → z ≠ dense.id.set1 → z ≠ dense.id.set2 → z ≠ dense.id.cnt →
    PTree.get z le' = PTree.get z le
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ j, j ≤ M ∧ v = M - j ∧
      PTree.get dense.id.c1 le' = some (.Vint (ir ((M - j : Nat) : Int))) ∧
      PTree.get dense.id.set1 le' = some (.Vptr bA (ptrTo baseA 8 j)) ∧
      PTree.get dense.id.set2 le' = some (.Vptr bB (ptrTo baseB 8 j)) ∧
      PTree.get dense.id.cnt le' = some (.Vint (ir ((k + pops wa wb j : Nat) : Int))) ∧ Oth le'
  simp only [popLoop, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, hm, E0_append]
  refine wp_loop (I := I) (J := fun v t e' le' m' => ∃ v', v' < v ∧ I v' t e' le' m') ?_ ?_
    (n := M) ⟨rfl, rfl, rfl, 0, Nat.zero_le _, by simp, by simp,
      by rw [temps_gso _ _ (Ne.symm n06)]; exact hs1,
      by rw [temps_gso _ _ (Ne.symm n07)]; exact hs2,
      by rw [temps_gso _ _ (Ne.symm n08)]; simpa [pops] using hc,
      fun z h0 _ _ _ _ _ _ _ _ => temps_gso _ _ h0⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, j, hj, rfl, hc1, hp1, hp2, hcn, ho⟩
    have hpj := pops_le wa wb j
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hc1, typeof, cop, ir_sub]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gso _ _ (Ne.symm n01), temps_gss, typeof, cop]
    rw [ir_lt (a := ((M - j : Nat) : Int) - 1) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
    by_cases hjM : j = M
    · subst hjM
      rw [ite_eq_right (by simp)]
      apply wp_break
      apply hQ
      · rw [temps_gso _ _ (Ne.symm n08), temps_gso _ _ (Ne.symm n18)]
        simpa using hcn
      · intro z h0 h1 h2 h3 h4 h5 h6 h7 h8
        rw [temps_gso _ _ h0, temps_gso _ _ h1]
        exact ho z h0 h1 h2 h3 h4 h5 h6 h7 h8
    · rw [ite_eq_left (by simp; omega)]
      apply wp_skip
      have hjM' : j < M := by omega
      have hl1 := load_ptr8 ha hjM'
      have hl2 := load_ptr8 hb hjM'
      wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [Exec.evalExpr,
        temps_gso, hp1]
      apply wp_set_eval
      simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [Exec.evalExpr, temps_gss,
        typeof, cop, add_ptr8]
      apply wp_set_eval
      simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [Exec.evalExpr,
        temps_gso, hp2]
      apply wp_set_eval
      simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [Exec.evalExpr, temps_gss,
        typeof, cop, add_ptr8]
      apply wp_set_eval
      simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [Exec.evalExpr, temps_gss,
        temps_gso, typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode, hl1, hl2]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss]
      have hcnt' := hcn
      have hpo : popCount (bv64 (Int64.and (wa j) (wb j))).toNat ≤ 64 := by
        rw [popCount_msb]; exact Nat.le_trans List.countP_le_length (by simp)
      apply wp_if_eval
      simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [Exec.evalExpr,
        temps_gss, temps_gso, typeof, cop,
        cast_int_long_ir (a := 0) ⟨by decide, by decide⟩, bv64_eq]
      have hnext : ∀ le2 : temp_env,
          PTree.get dense.id.c1 le2 = some (.Vint (ir ((M - (j + 1) : Nat) : Int))) →
          PTree.get dense.id.set1 le2 = some (.Vptr bA (ptrTo baseA 8 (j + 1))) →
          PTree.get dense.id.set2 le2 = some (.Vptr bB (ptrTo baseB 8 (j + 1))) →
          PTree.get dense.id.cnt le2 = some (.Vint (ir ((k + pops wa wb (j + 1) : Nat) : Int))) →
          Oth le2 → ∃ v', v' < M - j ∧ I v' E0 empty_env le2 m' := fun le2 h1 h2 h3 h4 h5 =>
        ⟨M - (j + 1), by omega, rfl, rfl, rfl, j + 1, by omega, rfl, h1, h2, h3, h4, h5⟩
      have hc1' : ((M - j : Nat) : Int) - 1 = ((M - (j + 1) : Nat) : Int) := by omega
      by_cases hz : bv64 (Int64.and (wa j) (wb j)) = bv64 (lr 0)
      · simp only [hz, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        apply wp_skip
        simp only [E0_append]
        apply hnext
        · simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [temps_gso, temps_gss, hc1']
        · simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [temps_gso, temps_gss]
        · simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [temps_gso, temps_gss]
        · simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [temps_gso]
          have h0 : popCount (bv64 (lr 0)).toNat = 0 := by
            rw [show (bv64 (lr 0)).toNat = 0 from rfl, Hex.GraphIso.Nauty.popCount_zero]
          rw [pops_succ, hz, h0, Nat.add_zero]
          exact hcn
        · intro z h0 h1 h2 h3 h4 h5 h6 h7 h8
          simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [temps_gso]
          exact ho z h0 h1 h2 h3 h4 h5 h6 h7 h8
      · simp only [hz, decide_false, Bool.not_false, ite_true]
        wp_step
        apply wp_skip
        apply wp_set_eval
        rw [eval_add_ii (x := ((k + pops wa wb j : Nat) : Int))
          (y := (popCount (bv64 (Int64.and (wa j) (wb j))).toNat : Int))
          (by simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [Exec.evalExpr,
            temps_gso]; exact hcn) rfl
          (eval_popcount _ (temps_gss _ _ _) hbt rfl) rfl]
        simp only [E0_append]
        apply hnext
        · simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [temps_gso, temps_gss, hc1']
        · simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [temps_gso, temps_gss]
        · simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [temps_gso, temps_gss]
        · rw [temps_gss, pops_succ]; push_cast; rw [Int.add_assoc]
        · intro z h0 h1 h2 h3 h4 h5 h6 h7 h8
          simp (disch := first | assumption | exact Ne.symm ‹_› | decide) only [temps_gso]
          exact ho z h0 h1 h2 h3 h4 h5 h6 h7 h8
  · rintro v t e' le' m' hJ
    apply wp_skip
    simpa using hJ

end NautyVerified.Proofs.Refine

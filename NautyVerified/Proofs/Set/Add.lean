import NautyVerified.Proofs.Set.Clear
import NautyVerified.Spec.Setwords

/-!
# `ADDELEMENT`

`wp_addElement`: `s[a >> 6] |= bit[a & 63]`, for an `int` expression `a`
holding `c`, sets bit `c` of the set `s`, reading nautil.c's `bit` table.
`setRep_single`: the words `EMPTYSET` then `ADDELEMENT(s, c)` leave represent
`{c}`.
-/

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec

variable {xi : ExternalCalls}

/-- A copy of nauty's `bit[64]` table, as it is in memory `m`: entry `i` is the
word with only bit `63 - i` (position `i` from the most significant end) set. -/
def BitTable (m : mem) (b : block) : Prop :=
  ∀ i : Nat, i < 64 → Mem.load .Mint64 m b (elemOfs .Mint64 0 i) =
    some (.Vlong (lr ((2 ^ (63 - i) : Nat) : Int)))

/-- Reading word `p[a]` of a setword array through a `unsigned long *` temporary. -/
theorem eval_word {e : env} {le : temp_env} {m : mem} {ba : block} {ofs : ptrofs}
    {ws : Nat → Lib.Integers.int64} {M : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M)
    (hM : M < 2147483648) (p : Common.AST.ident) (hp : PTree.get p le = some (.Vptr ba ofs))
    (a : expr) (c : Nat) (hc : c < M)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge e le m
      (.Ederef (.Ebinop .Oadd (.Etempvar p (tptr tulong)) a (tptr tulong)) tulong) =
        some (.Vlong (ws c)) := by
  simp only [Exec.evalExpr, hp, ha, hty]
  simp only [typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  apply load_array harr hc
  apply addr_elem ofs _ .Mint64 rfl rfl (by omega)
  have hf := harr.fits
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf ⊢
  omega

/-- The words after `ADDELEMENT(s, c)` on words `ws`. -/
abbrev addW (ws : Nat → Lib.Integers.int64) (c : Nat) : Nat → Lib.Integers.int64 :=
  upd ws (c / 64) (Int64.or (ws (c / 64)) (lr ((2 ^ (63 - c % 64) : Nat) : Int)))

theorem longs_upd (ws : Nat → Lib.Integers.int64) (i : Nat) (x : Lib.Integers.int64) :
    upd (longs ws) i (.Vlong x) = longs (upd ws i x) := by
  funext j; simp only [upd, longs]; split <;> rfl

/-- The address `p + a` of word `a` of a setword array. -/
theorem addr_word {ba : block} {ofs : ptrofs} {M : Nat} {m : mem} {vals : Nat → val}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) vals M) {c : Nat} (hc : c < M)
    (hM : M < 2147483648) :
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint64 (intOfZ (Ptrofs.unsigned ofs)) c := by
  apply addr_elem ofs _ .Mint64 rfl rfl (by omega)
  have hf := harr.fits
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf ⊢
  omega

/-- `ADDELEMENT(s, a)`: word `c / 64` of the set gets bit `c % 64`. -/
theorem wp_addElement' {s : Common.AST.ident} {a : expr} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {ba : block}
    {ofs : ptrofs} {ws : Nat → Lib.Integers.int64} {M c : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M)
    (hM : M < 2147483648) (hact : PTree.get s le = some (.Vptr ba ofs))
    (htc : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) (hc : c < 64 * M) (hc2 : c < 2147483648)
    (hbit : BitTable m Block.nautilBit) (he : PTree.get bit e = none)
    (hQ : ∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs))
        (longs (addW ws c)) M →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * M) →
      Q.normal E0 e le m') :
    Wp xi ge f (addElement s a) Q e le m := by
  have hw : c / 64 < M := by omega
  have hb : c % 64 < 64 := Nat.mod_lt _ (by decide)
  have h6 : Lib.Integers.Int.ltu (ir 6) Lib.Integers.Int.iwordsize = true := by decide
  have hshr : Lib.Integers.Int.shr (ir c) (ir 6) = ir ((c / 64 : Nat) : Int) := by
    rw [ir_shr6 ⟨by omega, by omega⟩]; congr 1
  have hand : Lib.Integers.Int.and (ir c) (ir 63) = ir ((c % 64 : Nat) : Int) := by
    rw [ir_and63 (by omega) (by omega)]; congr 1
  have hbaddr : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int))))) =
      elemOfs .Mint64 0 (c % 64) := by
    apply addr_elem _ _ .Mint64 rfl (base := 0) (by decide) (by omega)
    have h8 : csize .Mint64 = 8 := rfl
    rw [h8]; omega
  obtain ⟨m', hst, harr', -⟩ := store_array harr hw
    (.Vlong (Int64.or (ws (c / 64)) (lr ((2 ^ (63 - c % 64) : Nat) : Int)))) rfl
  simp only [addElement, setWord, sk]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hact, htc, hty, he, find_nautilBit]
  simp only [typeof, cop, h6, hshr, hand, ite_true]
  simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Exec.assignLoc]
  simp only [cop]
  have hl1 := load_array harr hw (addr_word harr hw hM)
  have hl2 : Mem.loadv .Mint64 m (.Vptr Block.nautilBit (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong))
      (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int)))))) =
      some (.Vlong (lr ((2 ^ (63 - c % 64) : Nat) : Int))) := by
    show Mem.load _ _ _ _ = _
    rw [hbaddr]; exact hbit _ hb
  simp only [hl1, hl2, longs, cop, Mem.storev]
  rw [addr_word harr hw hM, hst]
  rw [longs_upd] at harr'
  exact hQ m' harr' (Unch.store hst rfl) (Outside.store harr hw hst (Int.le_refl _)
    (by rw [show csize .Mint64 = 8 from rfl]; exact Int.le_refl _))


theorem wp_addElement {s : Common.AST.ident} {a : expr} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {ba : block}
    {ofs : ptrofs} {ws : Nat → Lib.Integers.int64} {M c : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M)
    (hM : M < 2147483648) (hact : PTree.get s le = some (.Vptr ba ofs))
    (htc : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) (hc : c < 64 * M)
    (hc2 : c < 2147483648)
    (hbit : BitTable m Block.nautilBit) (he : PTree.get bit e = none)
    (hQ : ∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs))
        (longs (addW ws c)) M →
      Unch m m' (· = ba) → Q.normal E0 e le m') :
    Wp xi ge f (addElement s a) Q e le m :=
  wp_addElement' harr hM hact htc hty hc hc2 hbit he fun m' ha hu _ => hQ m' ha hu

end NautyVerified.Proofs.Set

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers NautyVerified.Logic NautyVerified.Word NautyVerified.Spec

theorem BitTable.unch {m m' : mem} {S : block → Prop} {b : block} (h : BitTable m b)
    (hu : Unch m m' S) (hb : ¬ S b) : BitTable m' b := fun i hi => by
  rw [hu.load _ _ _ hb]; exact h i hi

theorem setRep_zero {n M : Nat} (hn : n ≤ 64 * M) :
    SetRep (fun w : Nat => bv64 ((fun _ : Nat => lr 0) w)) M
      (Hex.GraphIso.Nauty.VSet.empty : Hex.GraphIso.Nauty.VSet n) := by
  have h := setRep_empty (n := n) hn
  have he : (fun w : Nat => bv64 ((fun _ : Nat => lr 0) w)) = fun _ => (0 : BitVec 64) := by
    funext w; simp [intOfZ_zOfInt]
  rw [he]; exact h

/-- `ADDELEMENT` on words representing `s` gives words representing `s.insert c`. -/
theorem setRep_add {n M c : Nat} {ws : Nat → Lib.Integers.int64} {s : Hex.GraphIso.Nauty.VSet n}
    (h : SetRep (fun w => bv64 (ws w)) M s) (hc : c < n) :
    SetRep (fun w => bv64 (addW ws c w)) M (s.insert c) := by
  have h' := setRep_insert h hc
  have he : (fun w => bv64 (upd ws (c / 64) (Int64.or (ws (c / 64))
      (lr ((2 ^ (63 - c % 64) : Nat) : Int))) w)) =
      fun w => if w = c / 64 then (fun w => bv64 (ws w)) w ||| bitAt (c % 64)
        else (fun w => bv64 (ws w)) w := by
    funext w
    simp only [upd]
    split
    · rename_i hw; subst hw
      simp only [bv64_or, bv64_repr, intOfZ_zOfInt, bitAt, BitVec.ofInt_natCast]
    · rfl
  rw [he]; exact h'

/-- The words of `{c}`. -/
def single (c : Nat) : Nat → Lib.Integers.int64 :=
  upd (fun _ => lr 0) (c / 64) (Int64.or (lr 0) (lr ((2 ^ (63 - c % 64) : Nat) : Int)))

theorem setRep_single {n M c : Nat} (hn : n ≤ 64 * M) (hc : c < n) :
    SetRep (fun w => bv64 (single c w)) M
      (Hex.GraphIso.Nauty.VSet.empty.insert c : Hex.GraphIso.Nauty.VSet n) := by
  have h := setRep_insert (setRep_empty (n := n) hn) hc
  have he : (fun w => bv64 (single c w)) =
      fun w => if w = c / 64 then (fun _ => (0 : BitVec 64)) w ||| bitAt (c % 64)
        else (fun _ => (0 : BitVec 64)) w := by
    funext w
    simp only [single, upd]
    split
    · simp only [bv64_or, bv64_repr, intOfZ_zOfInt, bitAt, BitVec.ofInt_natCast]
      simp
    · simp [intOfZ_zOfInt]
  rw [he]; exact h

end NautyVerified.Proofs.Set

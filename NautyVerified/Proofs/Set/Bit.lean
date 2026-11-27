import NautyVerified.Proofs.Set.Elem

/-!
# `ADDELEMENT` and `DELELEMENT` with a given `bit` table

Each nauty source file has its own static copy of `bit[64]` (`nautil:bit`,
`naugraph:bit`, …). `addElementB s bitId a` and `delElementB s bitId a` are
`ADDELEMENT(s, a)` and `DELELEMENT(s, a)` reading the table `bitId`, for a set
`s` held in a temporary. `wp_addElementB` and `wp_delElementB` give the words
afterwards (`addW`, `delW`); `setRep_del` relates `delW` to `VSet.erase`.
-/

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec

variable {xi : ExternalCalls}

/-- `bitId[a & 63]`. -/
abbrev bitOf (bitId : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar bitId (tarray tulong 64)) (.Ebinop .Oand a (ci 63 tint) tint)
    (tptr tulong)) tulong

/-- `ADDELEMENT(s, a)` reading the table `bitId`. -/
abbrev addElementB (s bitId : Common.AST.ident) (a : expr) : statement :=
  sk (.Sassign (setWord s a) (.Ebinop .Oor (setWord s a) (bitOf bitId a) tulong))

/-- `DELELEMENT(s, a)` reading the table `bitId`. -/
abbrev delElementB (s bitId : Common.AST.ident) (a : expr) : statement :=
  sk (.Sassign (setWord s a)
    (.Ebinop .Oand (setWord s a) (.Eunop .Onotint (bitOf bitId a) tulong) tulong))

/-- The words after `DELELEMENT(s, c)` on words `ws`. -/
abbrev delW (ws : Nat → Lib.Integers.int64) (c : Nat) : Nat → Lib.Integers.int64 :=
  upd ws (c / 64) (Int64.and (ws (c / 64)) (Int64.not (lr ((2 ^ (63 - c % 64) : Nat) : Int))))

/-- The shared address computations of `s[a >> 6]` and `bit[a & 63]`. -/
private theorem bit_facts {c : Nat} (hc2 : c < 2147483648) :
    Lib.Integers.Int.ltu (ir 6) Lib.Integers.Int.iwordsize = true ∧
    Lib.Integers.Int.shr (ir c) (ir 6) = ir ((c / 64 : Nat) : Int) ∧
    Lib.Integers.Int.and (ir c) (ir 63) = ir ((c % 64 : Nat) : Int) ∧
    Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int))))) =
      elemOfs .Mint64 0 (c % 64) := by
  have hb : c % 64 < 64 := Nat.mod_lt _ (by decide)
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [ir_shr6 ⟨by omega, by omega⟩]; congr 1
  · rw [ir_and63 (by omega) (by omega)]; congr 1
  · apply addr_elem _ _ .Mint64 rfl (base := 0) (by decide) (by omega)
    have h8 : csize .Mint64 = 8 := rfl
    rw [h8]; omega

/-- `ADDELEMENT(s, a)` with the table `bitId`: word `c / 64` gets bit `c % 64`. -/
theorem wp_addElementB {s bitId : Common.AST.ident} {a : expr} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {ba bb : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64}
    {M c : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M)
    (hM : M < 2147483648) (hact : PTree.get s le = some (.Vptr ba ofs))
    (htc : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < 64 * M) (hc2 : c < 2147483648)
    (hfind : Genv.find_symbol ge.genv_genv bitId = some bb)
    (hbit : BitTable m bb) (he : PTree.get bitId e = none)
    (hQ : ∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs (addW ws c)) M →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * M) →
      Q.normal E0 e le m') :
    Wp xi ge f (addElementB s bitId a) Q e le m := by
  have hw : c / 64 < M := by omega
  have hb : c % 64 < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨h6, hshr, hand, hbaddr⟩ := bit_facts (c := c) hc2
  obtain ⟨m', hst, harr', -⟩ := store_array harr hw
    (.Vlong (Int64.or (ws (c / 64)) (lr ((2 ^ (63 - c % 64) : Nat) : Int)))) rfl
  simp only [addElementB, bitOf, setWord, sk]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hact, htc, hty, he, hfind]
  simp only [typeof, cop, h6, hshr, hand, ite_true]
  simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Exec.assignLoc]
  simp only [cop]
  have hl1 := load_array harr hw (addr_word harr hw hM)
  have hl2 : Mem.loadv .Mint64 m (.Vptr bb (Ptrofs.add Ptrofs.zero (Ptrofs.mul
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

/-- `DELELEMENT(s, a)` with the table `bitId`: word `c / 64` loses bit `c % 64`. -/
theorem wp_delElementB {s bitId : Common.AST.ident} {a : expr} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {ba bb : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64}
    {M c : Nat}
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M)
    (hM : M < 2147483648) (hact : PTree.get s le = some (.Vptr ba ofs))
    (htc : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < 64 * M) (hc2 : c < 2147483648)
    (hfind : Genv.find_symbol ge.genv_genv bitId = some bb)
    (hbit : BitTable m bb) (he : PTree.get bitId e = none)
    (hQ : ∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs (delW ws c)) M →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * M) →
      Q.normal E0 e le m') :
    Wp xi ge f (delElementB s bitId a) Q e le m := by
  have hw : c / 64 < M := by omega
  have hb : c % 64 < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨h6, hshr, hand, hbaddr⟩ := bit_facts (c := c) hc2
  obtain ⟨m', hst, harr', -⟩ := store_array harr hw
    (.Vlong (Int64.and (ws (c / 64)) (Int64.not (lr ((2 ^ (63 - c % 64) : Nat) : Int))))) rfl
  simp only [delElementB, bitOf, setWord, sk]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hact, htc, hty, he, hfind]
  simp only [typeof, cop, h6, hshr, hand, ite_true]
  simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Exec.assignLoc]
  simp only [cop]
  have hl1 := load_array harr hw (addr_word harr hw hM)
  have hl2 : Mem.loadv .Mint64 m (.Vptr bb (Ptrofs.add Ptrofs.zero (Ptrofs.mul
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

theorem setRep_del {n M c : Nat} {ws : Nat → Lib.Integers.int64} {s : Hex.GraphIso.Nauty.VSet n}
    (h : SetRep (fun w => bv64 (ws w)) M s) (hc : c < 64 * M) :
    SetRep (fun w => bv64 (delW ws c w)) M (s.erase c) := by
  refine ⟨h.1, fun u hu => ?_⟩
  rw [Hex.GraphIso.Nauty.VSet.mem_erase, ← h.2 u hu]
  simp only [SetwordsMem, delW, upd]
  have hb : c % 64 < 64 := Nat.mod_lt _ (by decide)
  have hu64 : u % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases hw : u / 64 = c / 64
  · rw [ite_eq_left hw, bv64_and, bv64_not, bv64_repr, intOfZ_zOfInt, BitVec.ofInt_natCast]
    rw [BitVec.getMsbD_and, BitVec.getMsbD_not, hw]
    have hbt := getMsbD_bitAt hb hu64
    unfold bitAt at hbt
    rw [hbt]
    by_cases huc : u = c
    · subst huc; simp
    · have : u % 64 ≠ c % 64 := fun h' => huc (by omega)
      simp [this, Ne.symm huc, hu64]
  · rw [ite_eq_right hw]
    have : u ≠ c := fun h' => hw (by rw [h'])
    simp [Ne.symm this]

end NautyVerified.Proofs.Set

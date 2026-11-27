import NautyVerified.Proofs.Set.Global
import NautyVerified.Proofs.Set.Bit

/-!
# `DELELEMENT` on a static set pointer

`delElementG g bitId a` is `DELELEMENT(g, a)` for a set reached through the
pointer global `g`, reading the `bit` table `bitId`; `wp_delElementG` is
`wp_addElementG` for it, leaving the words `delW ws c`; `wp_addElementGV` is `wp_addElementG`
also giving the growth of valid blocks.
-/

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Alloc (Keep)

variable {xi : ExternalCalls}

/-- `DELELEMENT(g, a)` for a pointer global `g`, with the `bit` table `bitId`. -/
abbrev delElementG (g bitId : Common.AST.ident) (a : expr) : statement :=
  sk (.Sassign (setWordG g a)
    (.Ebinop .Oand (setWordG g a)
      (.Eunop .Onotint (.Ederef (.Ebinop .Oadd (.Evar bitId (tarray tulong 64))
        (.Ebinop .Oand a (ci 63 tint) tint) (tptr tulong)) tulong) tulong) tulong))

theorem wp_delElementG {g bitId : Common.AST.ident} {a : expr} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {bg ba bitB : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64}
    {M c : Nat}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr ba ofs))
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M)
    (hM : M < 2147483648)
    (htc : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < 64 * M) (hc2 : c < 2147483648)
    (hbe : PTree.get bitId e = none) (hbg : Genv.find_symbol ge.genv_genv bitId = some bitB)
    (hbit : BitTable m bitB)
    (hQ : ∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs (delW ws c)) M →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * M) →
      Keep m m' ba → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (delElementG g bitId a) Q e le m := by
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
    (.Vlong (Int64.and (ws (c / 64)) (Int64.not (lr ((2 ^ (63 - c % 64) : Nat) : Int))))) rfl
  simp only [delElementG, setWordG, sk]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hge, hg, hbe, hbg, htc, hty]
  simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp]
  simp only [typeof, cop, h6, hshr, hand, ite_true]
  simp only [Exec.assignLoc, cop]
  have hl1 := load_array harr hw (addr_word harr hw hM)
  have hl2 : Mem.loadv .Mint64 m (.Vptr bitB (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong))
      (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int)))))) =
      some (.Vlong (lr ((2 ^ (63 - c % 64) : Nat) : Int))) := by
    show Mem.load _ _ _ _ = _
    rw [hbaddr]; exact hbit _ hb
  rw [hbaddr, hbit _ hb, addr_word harr hw hM, harr.load _ hw]
  simp only [longs, cop, Cfrontend.Ctypes.access_mode]
  simp only [Mem.storev]
  rw [addr_word harr hw hM, hst]
  rw [longs_upd] at harr'
  have hb0 := harr.base_nonneg
  exact hQ m' harr' (Unch.store hst rfl) (Outside.store harr hw hst (Int.le_refl _)
    (by rw [show csize .Mint64 = 8 from rfl]; exact Int.le_refl _))
    (Alloc.Keep.store hst (by simp only [elemOfs, intOfZ_zOfInt, show csize .Mint64 = 8 from rfl]; omega))
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst z hz)

/-- `wp_addElementG`, also giving the growth of valid blocks. -/
theorem wp_addElementGV {g bitId : Common.AST.ident} {a : expr} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {bg ba bitB : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64}
    {M c : Nat}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr ba ofs))
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M)
    (hM : M < 2147483648)
    (htc : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < 64 * M) (hc2 : c < 2147483648)
    (hbe : PTree.get bitId e = none) (hbg : Genv.find_symbol ge.genv_genv bitId = some bitB)
    (hbit : BitTable m bitB)
    (hQ : ∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs (addW ws c)) M →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * M) →
      Keep m m' ba → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp xi ge f (addElementG g bitId a) Q e le m := by
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
  simp only [addElementG, setWordG, sk]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hge, hg, hbe, hbg, htc, hty]
  simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp]
  simp only [typeof, cop, h6, hshr, hand, ite_true]
  simp only [Exec.assignLoc, cop]
  have hl1 := load_array harr hw (addr_word harr hw hM)
  have hl2 : Mem.loadv .Mint64 m (.Vptr bitB (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong))
      (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int)))))) =
      some (.Vlong (lr ((2 ^ (63 - c % 64) : Nat) : Int))) := by
    show Mem.load _ _ _ _ = _
    rw [hbaddr]; exact hbit _ hb
  rw [hbaddr, hbit _ hb, addr_word harr hw hM, harr.load _ hw]
  simp only [longs, cop, Cfrontend.Ctypes.access_mode]
  simp only [Mem.storev]
  rw [addr_word harr hw hM, hst]
  rw [longs_upd] at harr'
  have hb0 := harr.base_nonneg
  exact hQ m' harr' (Unch.store hst rfl) (Outside.store harr hw hst (Int.le_refl _)
    (by rw [show csize .Mint64 = 8 from rfl]; exact Int.le_refl _))
    (Alloc.Keep.store hst (by simp only [elemOfs, intOfZ_zOfInt, show csize .Mint64 = 8 from rfl]; omega))
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst z hz)

end NautyVerified.Proofs.Set

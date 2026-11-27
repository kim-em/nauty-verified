import NautyVerified.Proofs.Top.NautyMain
import NautyVerified.Proofs.Search.Node.Fields

/-!
# `nauty()`'s target-cell list

`wp_tTc`: on the first call `alloc_m` is 0 and the list from `tcnode0` is
empty, so `m > alloc_m`, the freeing loop stops at once, and `nauty()` sets
`alloc_m = m` and `tcnode0.next = NULL`.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (FieldAt IntAt)

set_option linter.unusedSimpArgs false

section
variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
theorem ne_null_null (ce : Cfrontend.Ctypes.composite_env) (m : mem) (t : Cfrontend.Ctypes.type) :
    Cfrontend.Cop.sem_binary_operation ce .One Vnullptr (tptr t)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
      (tptr .Tvoid) m = some (Val.of_bool false) := rfl
end

theorem cast_null_ptr (m : mem) (t t' : Cfrontend.Ctypes.type) :
    Cfrontend.Cop.sem_cast Vnullptr (tptr t) (tptr t') m = some Vnullptr := rfl

/-- `tcnode0.next`. -/
abbrev tcHead : expr :=
  .Efield (.Evar dense.id.«nauty:tcnode0» (.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr))
    dense.id.«next» (tptr (.Tstruct dense.id.«tcnode_struct» Cfrontend.Ctypes.noattr))

theorem eval_tcHead {le : temp_env} {m : mem} {v : val}
    (h : FieldAt m .Mint64 Search.Block.tcnode0 0 v) :
    Exec.evalExpr ge empty_env le m tcHead = some v := by
  simp only [tcHead, Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar,
    show PTree.get Source.dense.id.«nauty:tcnode0» (empty_env : env) = none from rfl,
    Search.find_tcnode0, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, typeof]
  rw [Search.field_tcnodeNext]
  show Mem.load _ _ _ (Ptrofs.unsigned _) = _
  rw [Search.unsigned_add_off Ptrofs.zero (by decide) (by decide)]
  exact (show Mem.load .Mint64 m _ (zOfInt (intOfZ (Ptrofs.unsigned Ptrofs.zero) + 0)) = _ by
    simpa using h.load)

variable {xi : ExternalCalls} in
theorem wp_tTc {Q : Post} {le : temp_env} {m : mem} {M : Nat}
    (hM : IntAt m Search.Block.m M) (hM0 : 0 < M) (hMl : M < 2147483648)
    (hA : IntAt m Search.Block.allocM 0)
    (hT : FieldAt m .Mint64 Search.Block.tcnode0 0 Vnullptr)
    (hQ : ∀ le' m', IntAt m' Search.Block.allocM M → FieldAt m' .Mint64 Search.Block.tcnode0 0 Vnullptr →
      Unch m m' (fun z => z = Search.Block.allocM ∨ z = Search.Block.tcnode0) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.tcp → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tOpts Q empty_env le' m') :
    Wp xi ge dense.fn.nauty Nauty.tTc Q empty_env le m := by
  simp only [Nauty.tTc, Nauty.tcIf]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, Search.eval_gint (e := empty_env) rfl Search.find_m hM,
    Search.eval_gint (e := empty_env) rfl Search.find_allocM hA]
  simp only [typeof, cop]
  rw [ir_lt (a := 0) (b := M) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩]
  rw [ite_eq_left (by simp; omega)]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tcHead hT]
  simp only [seqPost, Post.after, E0_append]
  wp_step
  -- the loop stops at once
  refine wp_loop (I := fun v t e' le' m' => t = E0 ∧ e' = empty_env ∧ v = 0 ∧ m' = m ∧
      le' = PTree.set dense.id.tcp Vnullptr le)
    (J := fun _ _ _ _ _ => False) ?_ ?_ (n := 0) ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro v t e' le' m' ⟨rfl, rfl, rfl, rfl, rfl⟩
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    rw [ne_null_null]
    simp only [Val.of_bool, Bool.false_eq_true, ite_false, Vfalse, cop]
    rw [ite_eq_right (by decide)]
    apply wp_break
    simp only [E0_append]
    wp_step; wp_step; wp_step
    refine Search.wp_gint rfl Search.find_allocM hA.writable (rhs := .Evar dense.id.«nauty:m» tint) (x := M)
      (Search.eval_gint rfl Search.find_m hM) rfl ?_
    intro m1 hA1 hu1 hv1
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    have hTw := hu1.access _ _ _ _ (by decide) hT.writable
    obtain ⟨m2, hst⟩ := Mem.valid_access_store _ Mptr _ _ Vnullptr hTw
    apply wp_assign_eval
    simp only [tcHead, Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get Source.dense.id.«nauty:tcnode0» (empty_env : env) = none from rfl,
      Search.find_tcnode0, typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
    rw [Search.field_tcnodeNext]
    simp only [Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
    rw [Search.unsigned_add_off Ptrofs.zero (by decide) (by decide),
      show zOfInt (intOfZ (Ptrofs.unsigned Ptrofs.zero) + 0) = zOfInt 0 from rfl,
      show val.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))) =
        Vnullptr from rfl, cast_null_ptr]
    simp only [hst, E0_append]
    refine hQ _ m2 (hA1.unch (Unch.store hst rfl) (by decide))
      ⟨Mem.load_store_same _ _ _ _ _ _ hst, Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hTw⟩
      ((hu1.mono fun z h => .inl h).trans ((Unch.store hst rfl).mono fun z h => .inr h.symm))
      (fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ (hv1 _ h)) (fun x hx => ?_)
    rw [temps_gso _ _ hx]
  · rintro _ _ _ _ _ h; exact h.elim

end NautyVerified.Proofs.Top

import NautyVerified.Proofs.Sparse.Refine.Ops
import NautyVerified.Proofs.Refine.Finish

/-!
# `refine_sg`'s code

`*code = CLEANUP(longcode)`, with `CLEANUP(l)` the `int` cast of `l % 077777`:
`wp_code` writes HexGraphIso's `cleanup l` into `*code`, both at the early
return (`l` the cell count) and at the end, after
`longcode = MASH(longcode, *numcells)` (`wp_finish`).
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- `l % 32767` for `0 ≤ l < 2^62`. -/
theorem mods_32767' {l : Nat} (hl : l < 2 ^ 62) :
    Lib.Integers.Int64.mods (lr l) (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 32767))) =
      lr ((l % 32767 : Nat) : Int) := by
  apply bv64_inj.1
  have e : ∀ x y : Lib.Integers.int64, Lib.Integers.Int64.mods x y = Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.sub (Lib.Integers.Int64.signed x) (ZArith.BinInt.Z.mul
        (ZArith.BinInt.Z.quot (Lib.Integers.Int64.signed x) (Lib.Integers.Int64.signed y))
        (Lib.Integers.Int64.signed y))) := fun _ _ => rfl
  rw [e, bv64_repr, bv64_repr]
  simp only [intOfZ_sub, intOfZ_mul, ZArith.BinInt.Z.quot, intOfZ_zOfInt, intOfZ_Int64_signed,
    bv64_repr]
  rw [show intOfZ (Lib.Integers.Int.signed (ir 32767)) = ((32767 : Nat) : Int) from
    Refine.signed_ir (by decide)]
  have h1 : (BitVec.ofInt 64 (l : Int)).toInt = l := by
    rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> omega
  have h2 : (BitVec.ofInt 64 ((32767 : Nat) : Int)).toInt = 32767 := by
    rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> decide
  rw [h1, h2]
  congr 1
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

/-- `*code = CLEANUP(longcode)`. -/
theorem wp_code {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (hcode : PTree.get id.«code» le = some (.Vptr L.bk L.kofs)) {l : Nat}
    (hl : PTree.get id.longcode le = some (.Vlong (lr l))) (hl2 : l < 2 ^ 62)
    (hQ : ∀ m', Mem m' L G t S →
      ArrayAt m' .Mint32 L.bk L.kb (fun _ => .Vint (ir (Hex.GraphIso.Nauty.cleanup l : Nat))) 1 →
      Unch m m' (· = L.bk) → Alloc.KeepA m m' → Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (.Ederef (pi id.«code») tint)
      (.Ecast (.Ebinop .Omod (.Etempvar id.«longcode» tlong) (ci 32767 tint) tlong) tint))
      Q empty_env le m := by
  obtain ⟨kv, hk⟩ := hm.code
  have hcl : Hex.GraphIso.Nauty.cleanup l = l % 32767 := rfl
  obtain ⟨m', hst, harr', -⟩ := store_array hk (show 0 < 1 by decide)
    (.Vint (ir (Hex.GraphIso.Nauty.cleanup l : Nat))) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hcode, hl, typeof, cop, Exec.assignLoc,
    Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [mods_32767' hl2, Refine.repr_unsigned_lr (by omega), ← hcl]
  rw [show Ptrofs.unsigned L.kofs = elemOfs .Mint32 L.kb 0 by
    unfold elemOfs
    rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, Loc.kb, zOfInt_intOfZ],
    hst]
  have harr : ArrayAt m' .Mint32 L.bk L.kb (fun _ => .Vint (ir (Hex.GraphIso.Nauty.cleanup l : Nat))) 1 :=
    harr'.congr fun i hi => by simp [upd, show i = 0 by omega]
  exact hQ m' (hm.setCode hok (Unch.store hst rfl) _ harr) harr (Unch.store hst rfl)
    (Alloc.KeepA.storeArr hk hst)

/-- `longcode = MASH(longcode, *numcells); *code = CLEANUP(longcode);` -/
theorem wp_finish {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (ht : Tmp le L t) (hc : t.longcode < 2 ^ 62) (hnc : t.numcells < 2147483648)
    (hQ : ∀ m', Mem m' L G t S →
      ArrayAt m' .Mint32 L.bk L.kb (fun _ => .Vint (ir (Hex.GraphIso.Nauty.cleanup
        (Hex.GraphIso.Nauty.mash t.longcode t.numcells) : Nat))) 1 →
      Unch m m' (· = L.bk) → Alloc.KeepA m m' →
      Q.normal E0 empty_env (PTree.set id.longcode
        (.Vlong (lr (Hex.GraphIso.Nauty.mash t.longcode t.numcells : Nat))) le) m') :
    Wp xi sge F finish Q empty_env le m := by
  have hml := Refine.mash_lt t.longcode t.numcells
  wp_step; wp_step; wp_step
  refine wp_mash ht.longcode hc (eval_nc hm ht) rfl hnc ?_
  simp only [E0_append]
  wp_step; wp_step
  exact wp_code hok hm (by rw [temps_gso _ _ (by decide)]; exact ht.code) (temps_gss _ _ _)
    (by omega) hQ

end NautyVerified.Proofs.Sparse.Refine

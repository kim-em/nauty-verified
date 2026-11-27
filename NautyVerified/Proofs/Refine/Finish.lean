import NautyVerified.Proofs.Refine.Step

/-!
# The end of `refine`

`longcode = MASH(longcode, *numcells); *code = CLEANUP(longcode);`, with
`CLEANUP(l)` the `int` cast of `l % 077777`: `wp_finish` writes HexGraphIso's
`cleanup (mash longcode numcells)` into `*code`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Source
open Hex.GraphIso.Nauty (RefineSt Ctx)

set_option linter.unusedSimpArgs false

section Cop
variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
variable (ce : composite_env) (m : mem) (a b : attr) (x : Lib.Integers.int64)

/-- `x % 32767` on a signed `long`. -/
@[simp, cop] theorem mod_sl32767 : sem_binary_operation ce .Omod (.Vlong x) (Tlong .Signed a)
    (.Vint (ir 32767)) (Tint .I32 .Signed b) m =
      some (.Vlong (Lib.Integers.Int64.mods x
        (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 32767))))) := by
  simp [sem_binary_operation, sem_mod, sem_binarith, classify_binarith, sem_cast, classify_cast,
    binarith_type, CompCert4Lean.X86_64.Archi.ptr64]
  exact ⟨⟨by decide, fun _ => by decide⟩, rfl⟩

/-- The `int` cast of a signed `long`. -/
@[simp, cop] theorem cast_sli : sem_cast (.Vlong x) (Tlong .Signed a) (Tint .I32 .Signed b) m =
    some (.Vint (Lib.Integers.Int.repr (Lib.Integers.Int64.unsigned x))) := rfl

end Cop

/-- `l % 32767` for `0 ≤ l < 2^15`. -/
theorem mods_32767 {l : Nat} (hl : l < 32768) :
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
    signed_ir (by decide)]
  have h1 : (BitVec.ofInt 64 (l : Int)).toInt = l := by
    rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> omega
  have h2 : (BitVec.ofInt 64 ((32767 : Nat) : Int)).toInt = 32767 := by
    rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> decide
  rw [h1, h2]
  congr 1
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

/-- The `int` cast of a small `long`. -/
theorem repr_unsigned_lr {c : Nat} (hc : c < 2147483648) :
    Lib.Integers.Int.repr (Lib.Integers.Int64.unsigned (lr c)) = ir c := by
  apply bv32_inj.1
  rw [bv32_repr, bv32_repr, intOfZ_Int64_unsigned, bv64_repr, intOfZ_zOfInt]
  congr 1
  rw [BitVec.toNat_ofInt]
  omega

variable {xi : ExternalCalls}

/-- `longcode = MASH(longcode, *numcells); *code = CLEANUP(longcode);` -/
theorem wp_finish {n : Nat} {Q : Post} {le : temp_env} {m : mem} {L : Loc} {ctx : Ctx n}
    {st : RefineSt n} {aw : Nat → Lib.Integers.int64} (hok : Ok n L) (hm : Mem m L ctx st aw)
    (ht : Tmp le L st) (hi : StInv n L st) {kv : Nat → val}
    (hk : ArrayAt m .Mint32 L.bk L.kb kv 1)
    (hQ : ∀ m', ArrayAt m' .Mint32 L.bk L.kb (fun _ => .Vint (ir
        (Hex.GraphIso.Nauty.cleanup (Hex.GraphIso.Nauty.mash st.longcode st.numcells) : Nat))) 1 →
      Unch m m' (· = L.bk) →
      Q.normal E0 empty_env (PTree.set dense.id.longcode
        (.Vlong (lr (Hex.GraphIso.Nauty.mash st.longcode st.numcells : Nat))) le) m') :
    Wp xi ge dense.fn.refine finish Q empty_env le m := by
  have hnc := hi.ncSmall
  have hnl := hok.nlt
  have hml := mash_lt st.longcode st.numcells
  simp only [finish, Set.sk]
  wp_step; wp_step; wp_step
  refine wp_mash ht.longcode hi.code (eval_numcells hm ht) rfl (by omega) ?_
  simp only [seqPost, Post.after, E0_append]
  wp_step
  have hcode : PTree.get dense.id.code (PTree.set dense.id.longcode
      (.Vlong (lr (Hex.GraphIso.Nauty.mash st.longcode st.numcells : Nat))) le) =
      some (.Vptr L.bk L.kofs) := by rw [temps_gso _ _ (by decide)]; exact ht.code
  have hcl : Hex.GraphIso.Nauty.cleanup (Hex.GraphIso.Nauty.mash st.longcode st.numcells) =
      Hex.GraphIso.Nauty.mash st.longcode st.numcells % 32767 := rfl
  obtain ⟨m', hst, harr', -⟩ := store_array hk (show 0 < 1 by decide)
    (.Vint (ir (Hex.GraphIso.Nauty.cleanup (Hex.GraphIso.Nauty.mash st.longcode st.numcells) : Nat)))
    rfl
  wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hcode, temps_gss, typeof, cop, Exec.assignLoc,
    Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [mods_32767 hml, repr_unsigned_lr (by omega), ← hcl]
  rw [show Ptrofs.unsigned L.kofs = elemOfs .Mint32 L.kb 0 by
    unfold elemOfs
    rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, Loc.kb, zOfInt_intOfZ],
    hst]
  exact hQ m' (harr'.congr fun i hi => by simp [upd, show i = 0 by omega]) (Unch.store hst rfl)

end NautyVerified.Proofs.Refine

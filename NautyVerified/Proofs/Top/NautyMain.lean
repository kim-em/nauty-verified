import NautyVerified.Proofs.Top.Head
import NautyVerified.Proofs.Top.Check
import NautyVerified.Proofs.Top.NautyAlloc

/-!
# `nauty()`'s copies of `m` and `n`, and the version checks

`wp_tMain`: `m = m_arg; n = n_arg; nautil_check(…); (*dispatch.check)(…)`.
Both checks pass; afterwards `nauty:m`, `nauty:n` hold `M`, `n`.
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

theorem cmp_null_ne {m : mem} {b : block} (hp : Mem.perm m b (zOfInt 0) .Cur .Nonempty) :
    Val.cmplu_bool (Mem.valid_pointer m) .Cne (.Vptr b Ptrofs.zero)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 0)))) = some true := by
  have hvp : Mem.valid_pointer m b (Ptrofs.unsigned Ptrofs.zero) = true :=
    (Mem.valid_pointer_nonempty_perm m b _).2 hp
  unfold Val.cmplu_bool
  show (if _ && _ && (Mem.valid_pointer m b _ || Mem.valid_pointer m b _) then _ else _) = _
  rw [hvp, Bool.true_or]
  rfl

section
variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
theorem ne_pl (ce : Cfrontend.Ctypes.composite_env) (m : mem) (blk : block) (ofs : ptrofs)
    (t1 t2 : Cfrontend.Ctypes.type) (a b : Cfrontend.Ctypes.attr) (y : Lib.Integers.int64) :
    Cfrontend.Cop.sem_binary_operation ce .One (.Vptr blk ofs) (.Tpointer t1 a) (.Vlong y)
      (.Tpointer t2 b) m =
      (Val.cmplu_bool (Mem.valid_pointer m) .Cne (.Vptr blk ofs) (.Vlong y)).map Val.of_bool := rfl
end

/-- The type of `xxx_check`. -/
abbrev checkType : Cfrontend.Ctypes.type := tfun [tint, tint, tint, tint] .Tvoid

variable {xi : ExternalCalls} in
theorem wp_tMain {Q : Post} {le : temp_env} {m : mem} {M n : Nat}
    (hm : PTree.get dense.id.m_arg le = some (.Vint (ir M)))
    (hn : PTree.get dense.id.n_arg le = some (.Vint (ir n)))
    (hMl : M < 2147483648) (hnl : n < 2147483648)
    (hmw : Mem.valid_access m .Mint32 Search.Block.m (zOfInt 0) .Writable)
    (hnw : Mem.valid_access m .Mint32 Search.Block.n (zOfInt 0) .Writable)
    (hD : DispatchAt m M)
    (hcp : Mem.perm m Block.naugraphCheck (zOfInt 0) .Cur .Nonempty)
    (hQ : ∀ m', IntAt m' Search.Block.m M → IntAt m' Search.Block.n n →
      Unch m m' (fun z => z = Search.Block.m ∨ z = Search.Block.n) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Wp xi ge dense.fn.nauty Nauty.tAlloc Q empty_env le m') :
    Wp xi ge dense.fn.nauty Nauty.tMain Q empty_env le m := by
  simp only [Nauty.tMain]
  wp_step; wp_step; wp_step
  refine Search.wp_gint rfl Search.find_m hmw (x := M) (by simp [Exec.evalExpr, Refine.tv, hm]) rfl ?_
  intro m1 hM1 hu1 hv1
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine Search.wp_gint rfl Search.find_n (hu1.access _ _ _ _ (by decide) hnw) (x := n)
    (rhs := Refine.tv dense.id.n_arg)
    (by simp [Exec.evalExpr, Refine.tv, hn]) rfl ?_
  intro m2 hN2 hu2 hv2
  have hM2 : IntAt m2 Search.Block.m M := hM1.unch hu2 (by decide)
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.nautilCheck Ptrofs.zero) (targs := [tint, tint, tint, tint])
    (tres := .Tvoid) (cc := Common.AST.cc_default) _ (checkSpec (.Vint (ir M)) (.Vint (ir n)))
    (nautil_check_satisfies _ _) rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get Source.dense.id.nautil_check (empty_env : env) = none from rfl,
      find_nautilCheck, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
    (by simp only [Exec.evalExprlist, Search.eval_gint (e := empty_env) rfl Search.find_m hM2,
          Search.eval_gint (e := empty_env) rfl Search.find_n hN2]
        simp only [Exec.evalExpr, typeof, cop]
        rw [show Lib.Integers.Int.repr (zOfInt 29300) = ir 29300 from rfl,
          show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, ir_add,
          show Lib.Integers.Int.repr (zOfInt 64) = ir 64 from rfl]
        simp)
    (by simp [Common.Globalenvs.Genv.find_funct, funct_nautilCheck]) rfl rfl ?_
  rintro t v m3 ⟨rfl, rfl⟩
  simp only [set_opttemp, seqPost, Post.after, E0_append]
  have hu12 : Unch m m3 (fun z => z = Search.Block.m ∨ z = Search.Block.n) :=
    (hu1.mono fun z h => .inl h).trans (hu2.mono fun z h => .inr h)
  have hck : Mem.load .Mint64 m3 Search.Block.dispatch (zOfInt 64) =
      some (.Vptr Block.naugraphCheck Ptrofs.zero) := by
    rw [hu12.load _ _ _ (by decide)]
    exact (hD 8 (by decide)).load.trans (by simp [dispatchOf, dispatchVals])
  have hcp2 : Mem.perm m3 Block.naugraphCheck (zOfInt 0) .Cur .Nonempty := by
    have hv : Mem.valid_access m .Mint8unsigned Block.naugraphCheck (zOfInt 0) .Nonempty :=
      ⟨fun o ho => by
        have : o = zOfInt 0 := by
          apply intOfZ_injective
          have h1 := ho.1; have h2 := ho.2
          change intOfZ _ ≤ intOfZ _ at h1; change intOfZ _ < intOfZ _ at h2
          rw [intOfZ_add] at h2; simp [intOfZ_zOfInt] at h1 h2 ⊢
          have : intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 := rfl
          omega
        rw [this]; exact hcp, ⟨zOfInt 0, rfl⟩⟩
    exact (hu12.access _ _ _ _ (by decide) hv).1 _ ⟨by
      change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt], by
      change intOfZ _ < intOfZ _; rw [intOfZ_add]; simp [intOfZ_zOfInt]; decide⟩
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_dispF field_dCheck (by decide) (by decide) hck]
  simp only [Exec.evalExpr, typeof, cop, ne_pl, cmp_null_ne hcp2]
  simp only [Option.map, Val.of_bool, cop]
  rw [ite_eq_left (by decide)]
  wp_step; wp_step
  refine wp_call (vf := .Vptr Block.naugraphCheck Ptrofs.zero) (targs := [tint, tint, tint, tint])
    (tres := .Tvoid) (cc := Common.AST.cc_default) _ (checkSpec (.Vint (ir M)) (.Vint (ir n)))
    (naugraph_check_satisfies _ _) rfl ?_
    (by simp only [Exec.evalExprlist, Search.eval_gint (e := empty_env) rfl Search.find_m hM2,
          Search.eval_gint (e := empty_env) rfl Search.find_n hN2]
        simp only [Exec.evalExpr, typeof, cop]
        rw [show Lib.Integers.Int.repr (zOfInt 29300) = ir 29300 from rfl,
          show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl, ir_add,
          show Lib.Integers.Int.repr (zOfInt 64) = ir 64 from rfl]
        simp)
    (by simp [Common.Globalenvs.Genv.find_funct, funct_naugraphCheck]) rfl rfl ?_
  · rw [Exec.evalExpr, eval_dispF field_dCheck (by decide) (by decide) hck]
    simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  rintro t v m4 ⟨rfl, rfl⟩
  simp only [set_opttemp, seqPost, Post.after, E0_append]
  exact hQ _ hM2 hN2 hu12 (fun z h => hv2 _ (hv1 _ h))

end NautyVerified.Proofs.Top

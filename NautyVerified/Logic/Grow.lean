import NautyVerified.Logic.Call

/-!
# Valid blocks stay valid

Every Clight step (stores, allocations, frees, external calls) keeps the valid
blocks valid (`step_valid`, `steps_valid`). `Satisfies.grow`: a function
satisfying a specification also satisfies it with "every block valid before the
call is valid after it" added to the postcondition.
-/

namespace NautyVerified.Logic

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Values
open CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {ge : genv}

/-- The memory of a state. -/
def smem : state → mem
  | .State _ _ _ _ _ m => m
  | .Callstate _ _ _ m => m
  | .Returnstate _ _ m => m

theorem free_valid {m m' : mem} {b : block} {lo hi : Z} (h : Mem.free m b lo hi = some m')
    {z : block} (hz : Mem.valid_block m z) : Mem.valid_block m' z := by
  unfold Mem.valid_block at hz ⊢
  rw [Mem.nextblock_free _ _ _ _ _ h]; exact hz

theorem free_list_valid : ∀ {l : List (block × Z × Z)} {m m' : mem}, Mem.free_list m l = some m' →
    ∀ z, Mem.valid_block m z → Mem.valid_block m' z
  | [], m, m', h, z, hz => by cases h; exact hz
  | (b, lo, hi) :: rest, m, m', h, z, hz => by
    rw [Mem.free_list] at h
    split at h
    · cases h
    · rename_i m1 hf
      exact free_list_valid h z (free_valid hf hz)

theorem assign_loc_valid {ce : Cfrontend.Ctypes.composite_env} {ty : Cfrontend.Ctypes.type}
    {m m' : mem} {b : block} {ofs : Lib.Integers.ptrofs} {bf : Cfrontend.Ctypes.bitfield} {v : val}
    (h : assign_loc ce ty m b ofs bf v m') (z : block) (hz : Mem.valid_block m z) :
    Mem.valid_block m' z := by
  cases h with
  | assign_loc_value v chunk m' hmode hstore =>
    simp only [Mem.storev] at hstore
    exact Mem.store_valid_block_1 _ _ _ _ _ _ hstore _ hz
  | assign_loc_copy b' ofs' bytes m' hmode h1 h2 h3 hload hst =>
    exact Mem.storebytes_valid_block_1 _ _ _ _ _ hst _ hz
  | assign_loc_bitfield sz sg pos width v m' v' hst =>
    cases hst with
    | store_bitfield_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hstore =>
      simp only [Mem.storev] at hstore
      exact Mem.store_valid_block_1 _ _ _ _ _ _ hstore _ hz

theorem alloc_variables_valid : ∀ {e : env} {m : mem} {vars : List (Common.AST.ident × Cfrontend.Ctypes.type)}
    {e' : env} {m' : mem}, alloc_variables ge e m vars e' m' →
    ∀ z, Mem.valid_block m z → Mem.valid_block m' z
  | _, _, _, _, _, .nil _ _, _, hz => hz
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ halloc hrest, z, hz =>
    alloc_variables_valid hrest z (Mem.valid_block_alloc _ _ _ _ _ halloc _ hz)

theorem step_valid {s t s'} (h : Step xi ge s t s') (z : block) (hz : Mem.valid_block (smem s) z) :
    Mem.valid_block (smem s') z := by
  cases h with
  | step_assign f a1 a2 k e le m loc ofs bf v2 v m' hl hr hc hassign => exact assign_loc_valid hassign z hz
  | step_builtin f r ef tys args k e le m vargs t vres m' ha hcall =>
    exact external_call_valid_block_proof _ _ _ _ _ _ _ _ _ hcall hz
  | step_return_0 f k e le m m' hfree => exact free_list_valid hfree z hz
  | step_return_1 f a k e le m v v' m' he hc hfree => exact free_list_valid hfree z hz
  | step_skip_call f k e le m m' hc hfree => exact free_list_valid hfree z hz
  | step_internal_function f vargs k m e le m1 hentry =>
    cases hentry with
    | intro _ _ _ halloc _ => exact alloc_variables_valid halloc z hz
  | step_external_function ef tys rt cc vargs k m vres t m' hcall =>
    exact external_call_valid_block_proof _ _ _ _ _ _ _ _ _ hcall hz
  | _ => exact hz

theorem steps_valid {s t s'} (h : Steps xi ge s t s') (z : block) (hz : Mem.valid_block (smem s) z) :
    Mem.valid_block (smem s') z := by
  induction h with
  | refl => exact hz
  | step h1 _ ih => exact ih (step_valid h1 z hz)

/-- A satisfied specification, with validity growth added to the postcondition. -/
theorem Satisfies.grow {fd : fundef} {S : FunSpec} (h : Satisfies xi ge fd S) :
    Satisfies xi ge fd { pre := S.pre, post := (fun args m t v m' => S.post args m t v m' ∧
      ∀ z, Mem.valid_block m z → Mem.valid_block m' z) } := by
  intro args m hp k hk
  obtain ⟨t, v, m', hs, hq⟩ := h args m hp k hk
  exact ⟨t, v, m', hs, hq, fun z hz => steps_valid hs z hz⟩

end NautyVerified.Logic

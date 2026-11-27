import NautyVerified.Proofs.Alloc.Blocks
import NautyVerified.Logic.Call
import NautyVerified.Logic.Array
import NautyVerified.Logic.PtrArith

/-!
# `malloc`

CompCert's `malloc` builtin allocates a fresh block with a size header at
offset `-8`. `mallocSpec sz`: it returns a pointer to offset 0 of a block `b`
not valid before, `Freeable` on `[-8, sz)`, with the header `free` reads, and
leaves every other block as it was (`Fresh`).
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word

theorem vptrofs_lr (N : Nat) : Vptrofs (Ptrofs.repr (zOfInt N)) = .Vlong (lr N) := by
  unfold Vptrofs
  simp only [show CompCert4Lean.X86_64.Archi.ptr64 = true from rfl, ite_true]
  congr 1
  apply bv64_inj.1
  simp only [Ptrofs.to_int64, bv64_repr]
  rw [intOfZ_Ptrofs_unsigned, bvp_repr, intOfZ_zOfInt]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  omega

/-- Allocation changes only the new block. -/
theorem Unch.alloc {m m' : mem} {lo hi : Z} {b : block} (h : Mem.alloc m lo hi = (m', b)) :
    Unch m m' (· = b) where
  load chunk b' ofs hb := by
    cases hl : Mem.load chunk m b' ofs with
    | some v => exact Mem.load_alloc_other _ _ _ _ _ h _ _ _ _ hl
    | none =>
      cases hl' : Mem.load chunk m' b' ofs with
      | none => rfl
      | some v =>
        have hva := Mem.load_valid_access _ _ _ _ _ hl'
        have := Mem.valid_access_alloc_inv _ _ _ _ _ h _ _ _ _ hva
        rcases hdec : eq_block b' b with heq | hne
        · exact absurd heq hb
        · rw [hdec] at this
          obtain ⟨v', hv'⟩ := Mem.valid_access_load _ _ _ _ this
          rw [hl] at hv'; cases hv'
  access chunk b' ofs p _ hva :=
    ⟨fun o ho => Mem.perm_alloc_1 _ _ _ _ _ h _ _ _ _ (hva.1 o ho), hva.2⟩

/-- A fresh block of `sz` bytes from `malloc`. -/
structure Fresh (m m' : mem) (b : block) (sz : Nat) : Prop where
  unch : Unch m m' (· = b)
  hdr : Mem.load Mptr m' b (zOfInt (-8)) = some (.Vlong (lr sz))
  perm : ∀ ofs : Int, -8 ≤ ofs → ofs < sz → Mem.perm m' b (zOfInt ofs) .Cur .Freeable
  new : ¬ Mem.valid_block m b
  grow : ∀ z, Mem.valid_block m z → Mem.valid_block m' z

def mallocSpec (sz : Nat) : FunSpec where
  pre args _ := args = [.Vlong (lr sz)] ∧ sz < 2 ^ 63
  post _ m t v m' := t = E0 ∧ ∃ b, v = .Vptr b Ptrofs.zero ∧ Fresh m m' b sz

theorem malloc_satisfies {xi : ExternalCalls} (sz : Nat) :
    Satisfies xi ge (.External .EF_malloc [tulong] (tptr .Tvoid) Common.AST.cc_default)
      (mallocSpec sz) := by
  apply satisfies_external
  rintro args m ⟨rfl, hsz⟩
  have hu : intOfZ (Ptrofs.unsigned (Ptrofs.repr (zOfInt sz))) = sz := by
    rw [intOfZ_Ptrofs_unsigned, bvp_repr, intOfZ_zOfInt, BitVec.toNat_ofInt]; omega
  rcases ha : Mem.alloc m (ZArith.BinInt.Z.opp (size_chunk Mptr)) (Ptrofs.unsigned (Ptrofs.repr (zOfInt sz)))
    with ⟨m1, b⟩
  have hperm : ∀ ofs : Int, -8 ≤ ofs → ofs < sz → Mem.perm m1 b (zOfInt ofs) .Cur .Freeable :=
    fun ofs h1 h2 => Mem.perm_alloc_2 _ _ _ _ _ ha _ _ ⟨by
      change intOfZ _ ≤ intOfZ _; rw [intOfZ_zOfInt]; exact h1, by
      change intOfZ _ < intOfZ _; rw [intOfZ_zOfInt, hu]; exact h2⟩
  have hva : Mem.valid_access m1 Mptr b (ZArith.BinInt.Z.opp (size_chunk Mptr)) .Writable := by
    refine ⟨fun o ho => ?_, ⟨zOfInt (-1), rfl⟩⟩
    have h1 : -8 ≤ intOfZ o := ho.1
    have h2 : intOfZ o < 0 := ho.2
    have := hperm (intOfZ o) h1 (by omega)
    rw [zOfInt_intOfZ] at this
    exact Mem.perm_implies _ _ _ _ _ _ this (.perm_F_any _)
  obtain ⟨m2, hst⟩ := Mem.valid_access_store _ _ _ _ (Vptrofs (Ptrofs.repr (zOfInt sz))) hva
  refine ⟨E0, .Vptr b Ptrofs.zero, m2, ?_, rfl, b, rfl, ?_⟩
  · rw [← vptrofs_lr sz]
    exact .extcall_malloc_sem_intro _ _ _ _ _ ha hst
  · refine ⟨(Unch.alloc ha).trans (Unch.store hst rfl), ?_, ?_, ?_, fun z hz =>
      Mem.store_valid_block_1 _ _ _ _ _ _ hst _ (Mem.valid_block_alloc _ _ _ _ _ ha _ hz)⟩
    · have := Mem.load_store_same _ _ _ _ _ _ hst
      rw [vptrofs_lr sz] at this
      exact this
    · intro ofs h1 h2
      exact Mem.perm_store_1 _ _ _ _ _ _ hst _ _ _ _ (hperm ofs h1 h2)
    · exact Mem.fresh_block_alloc _ _ _ _ _ ha

end NautyVerified.Proofs.Alloc

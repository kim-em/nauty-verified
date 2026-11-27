import NautyVerified.Proofs.Alloc.Zero
import NautyVerified.Proofs.Alloc.Free

/-!
# nauty's `DYNALLSTAT` arrays

A `DYNALLSTAT(type, name, name_sz)` pair is a static pointer `name` and a
static capacity `name_sz`. `DynAt m gp gs c cap b`: the capacity global `gs`
holds `cap`, and when `cap > 0` the pointer global `gp` points to block `b`,
allocated by `malloc` for `c * cap` bytes (`c` the element size).
`malloced_array`: such a block holds an array of `cap` elements (values
unknown); `DYNALLOC1` (`wp_dynalloc1`) re-establishes `DynAt` with capacity
at least the size asked for.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs

/-- The first `k` elements of a `malloc`ed block of at least `c * k` bytes
form an array, whatever their values. -/
theorem malloced_array {m : mem} {b : block} {N : Nat} (h : Malloced m b N) (chunk : memory_chunk)
    (c : Nat) (hc : csize chunk = c) (ha : intOfZ (align_chunk chunk) = c) (k : Nat)
    (hk : c * k ≤ N) : ∃ vals, ArrayAt m chunk b 0 vals k := by
  have hcpos := csize_pos chunk
  have hofs : ∀ i : Nat, elemOfs chunk 0 i = zOfInt ((c * i : Nat) : Int) := fun i => by
    simp only [elemOfs, hc]; congr 1; push_cast; omega
  have hle : ∀ i, i < k → c * i + c ≤ N := fun i hi => by
    have := Nat.mul_le_mul_left c (show i + 1 ≤ k by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  have hva : ∀ i, i < k → Mem.valid_access m chunk b (elemOfs chunk 0 i) .Writable := fun i hi => by
    rw [hofs]
    refine ⟨fun o ho => ?_, ⟨zOfInt i, by
      apply intOfZ_injective
      simp only [intOfZ_mul, intOfZ_zOfInt, ha]; push_cast; rw [Int.mul_comm]⟩⟩
    have h1 : ((c * i : Nat) : Int) ≤ intOfZ o := by
      have := ho.1; change intOfZ _ ≤ intOfZ _ at this; rwa [intOfZ_zOfInt] at this
    have h2 : intOfZ o < ((c * i : Nat) : Int) + c := by
      have := ho.2; change intOfZ _ < intOfZ _ at this
      rwa [intOfZ_add, intOfZ_zOfInt, show intOfZ (size_chunk chunk) = c from hc] at this
    have := h.perm (intOfZ o) (by omega) (by have := hle i hi; omega)
    rw [zOfInt_intOfZ] at this
    exact Mem.perm_implies _ _ _ _ _ _ this (.perm_F_any _)
  refine ⟨fun i => (Mem.load chunk m b (elemOfs chunk 0 i)).getD .Vundef,
    ⟨Int.le_refl _, ?_, fun i hi => ?_, hva⟩⟩
  · rw [hc]
    have := h.small
    have : ((c * k : Nat) : Int) = (c : Int) * k := by push_cast; rfl
    omega
  · obtain ⟨v, hv⟩ := Mem.valid_access_load _ _ _ _
      (Mem.valid_access_implies _ _ _ _ _ _ (hva i hi) .perm_W_R)
    rw [hv]; rfl

abbrev sk (s : statement) : statement := .Ssequence .Sskip s

/-- `DYNALLOC1(elt, gp, gs, sz, msg)`, as SimplExpr writes it, with temporaries
`t1` (the allocator's result) and `t2` (its cast). -/
abbrev dynalloc1 (gs gp : Common.AST.ident) (elt : Cfrontend.Ctypes.type) (szE : expr) (t1 t2 msg : Common.AST.ident)
    (msgLen : Int) : statement :=
  sk (.Sifthenelse (.Ebinop .Ogt (.Ecast szE tulong) (.Evar gs tulong) tint)
    (.Ssequence
      (sk (.Sifthenelse (.Evar gs tulong)
        (sk (.Scall none (.Evar Source.dense.id.free (tfun [tptr .Tvoid] .Tvoid))
          [.Evar gp (tptr elt)]))
        .Sskip))
      (.Ssequence
        (sk (.Sassign (.Evar gs tulong) szE))
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (sk (.Scall (some t1) (.Evar Source.dense.id.nauty_zalloc (tfun [tulong] (tptr .Tvoid)))
                [.Ebinop .Omul (.Ecast szE tulong) (.Ecast (.Esizeof elt tulong) tulong) tulong]))
              (.Sset t2 (.Ecast (.Ecast (.Etempvar t1 (tptr .Tvoid)) (tptr elt)) (tptr elt))))
            (.Sassign (.Evar gp (tptr elt)) (.Etempvar t2 (tptr elt))))
          (.Sifthenelse (.Ebinop .Oeq (.Etempvar t2 (tptr elt)) (.Ecast (ci 0 tint) (tptr .Tvoid)) tint)
            (sk (.Scall none (.Evar Source.dense.id.alloc_error (tfun [tptr tschar] .Tvoid))
              [.Evar msg (tarray tschar msgLen)]))
            .Sskip))))
    .Sskip)

end NautyVerified.Proofs.Alloc

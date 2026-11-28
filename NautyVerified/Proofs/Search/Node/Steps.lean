import NautyVerified.Proofs.Search.Node.Spec
import NautyVerified.Proofs.Search.Frame
import NautyVerified.Proofs.Search.Ops
import NautyVerified.Proofs.Search.Node.Rebuild
import NautyVerified.Proofs.Refine.Mash

/-!
# The straight-line steps of a search node

Pieces of `firstpathnode0` and `othernode0` stated in `SearchAt` terms, shared
by the two node proofs:

- `wp_numnodes`: `++stats->numnodes` (HexGraphIso's `visit` counts the node
  first).
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

theorem lr_succ (a : Nat) :
    Lib.Integers.Int64.add (lr a) (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 1))) =
      lr ((a + 1 : Nat) : Int) := by
  apply bv64_inj.1
  rw [bv64_add, bv64_repr, bv64_repr, bv64_repr, intOfZ_zOfInt, intOfZ_zOfInt,
    show intOfZ (Lib.Integers.Int.signed (ir 1)) = ((1 : Nat) : Int) from
      Refine.signed_ir (by decide), ← BitVec.ofInt_add]
  push_cast; rfl

theorem csize32 : csize .Mint32 = 4 := rfl
theorem csize64 : csize .Mint64 = 8 := rfl

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- `++stats->numnodes`, for `D`. -/
theorem wp_numnodesG {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} (h : SearchAtG D m S gl cl G st pre nsp)
    (hge : PTree.get dense.id.«nauty:stats» e = none)
    (hQ : ∀ m', SearchAtG D m' S gl cl G { st with numnodes := st.numnodes + 1 } pre nsp →
      Unch m m' (· = S.bst) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (statsF dense.id.numnodes tulong)
      (.Ebinop .Oadd (statsF dense.id.numnodes tulong) (ci 1 tint) tulong)) Q e le m := by
  have hfit := h.stats.fits
  refine wp_statsStore (off := 24) (chunk := .Mint64) hge fld_numnodes rfl h.fixed.stats
    (by decide) (by omega) h.stats.numnodes.writable
    (w := .Vlong (lr ((st.numnodes + 1 : Nat) : Int)))
    (w' := .Vlong (lr ((st.numnodes + 1 : Nat) : Int))) ?_ rfl ?_
  · have hv := eval_statsF (le := le) (ty := tulong) hge fld_numnodes rfl h.fixed.stats
      (by decide) (by omega) h.stats.numnodes
    rw [Exec.evalExpr, hv]
    simp only [Exec.evalExpr, typeof, cop, lr_succ]
  intro m' hst
  have hu : Unch m m' (· = S.bst) := Unch.store hst rfl
  have hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z :=
    fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz
  refine hQ m' ?_ hu hv
  have hd := h.lit
  have hs := h.stats
  refine h.rebuild (L := [S.bst]) (hu.mono fun z hz => by simp [hz]) (by simp)
    (fun z hz => Keep.unch hu (by revert z hz; sep_all hd)) hv
    { h.scalars.unch hu (by sep_all hd) with }
    { (hs.fix.store hst (by first | omega | (simp only [csize32, csize64]; omega))) with
      numorbits := hs.numorbits.store_other hst (by simp only [csize32, csize64]; omega)
      numgenerators := hs.numgenerators.store_other hst (by simp only [csize32, csize64]; omega)
      numnodes := FieldAt.store_same hst hs.numnodes.writable
      numbadleaves := hs.numbadleaves.store_other hst (by simp only [csize32, csize64]; omega)
      maxlevel := fun hp => (hs.maxlevel hp).store_other hst (by simp only [csize32, csize64]; omega)
      maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hs.maxlevelW
      tctotal := hs.tctotal.store_other hst (by simp only [csize32, csize64]; omega)
      canupdates := hs.canupdates.store_other hst (by simp only [csize32, csize64]; omega)
      fits := hs.fits }
    { h.arrays.unch hu (by sep_all hd) (fun z hz e => h.graph_ne hz (.inl (by simp)) e)
      (fun z hz e => h.canon_ne hz (.inr (.inl (by simp))) e) with }
    { h.inv with }

end Generic

theorem wp_numnodes {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hge : PTree.get dense.id.«nauty:stats» e = none)
    (hQ : ∀ m', SearchAt m' S ctx { st with numnodes := st.numnodes + 1 } pre nsp →
      Unch m m' (· = S.bst) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (statsF dense.id.numnodes tulong)
      (.Ebinop .Oadd (statsF dense.id.numnodes tulong) (ci 1 tint) tulong)) Q e le m :=
  wp_numnodesG h.toG hge fun m' h' hu hv => hQ m' (h'.dense h.gw) hu hv

end NautyVerified.Proofs.Search

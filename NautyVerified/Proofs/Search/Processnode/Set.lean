import NautyVerified.Proofs.Search.Processnode.State

/-!
# Updating one component of the search state

Each lemma rebuilds `Arrays`, `Scalars` or `Stats` after a change confined to
the blocks of the fields it replaces.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

variable {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {nsp : Bool}
  {pre : Bool}

/-- `Arrays` with the fields stored in the blocks `L` replaced. Each new field
is given, or the field's block is outside `L`. -/
theorem Arrays.set {st' : Search n} (h : Arrays m S ctx st) {L : List block}
    (hu : Unch m m' (· ∈ L))
    (lab : ArrayAt m' .Mint32 S.bl S.lb (ints st'.lab) n)
    (ptn : ArrayAt m' .Mint32 S.bp S.pb (ints st'.ptn) n)
    (orbits : ArrayAt m' .Mint32 S.bo S.ob (ints st'.orbits) n)
    (active : ∃ aw, ArrayAt m' .Mint64 S.bA 0 (longs aw) S.M ∧
      SetRep (fun w => bv64 (aw w)) S.M st'.active)
    (fixedpts : ∃ fw, ArrayAt m' .Mint64 S.bF 0 (longs fw) S.M ∧
      SetRep (fun w => bv64 (fw w)) S.M st'.fixedpts)
    (workperm : ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n)
    (firstlab : ArrayAt m' .Mint32 S.bFL 0 (ints st'.firstlab) n)
    (canonlab : ArrayAt m' .Mint32 S.bCL 0 (ints st'.canonlab) n)
    (firstcode : ArrayAt m' .Mint16signed S.bFC 0 (shorts st'.firstcode) (n + 2))
    (canoncode : ArrayAt m' .Mint16signed S.bCC 0 (shorts st'.canoncode) (n + 2))
    (firsttc : ArrayAt m' .Mint32 S.bTC 0 (intsZ st'.firsttc) (n + 2))
    (canong : CanongAt m' S st'.canong st'.samerows)
    (autos : AutosAt m' S st'.autos) (hg : S.bg ∉ L) : Arrays m' S ctx st' :=
  ⟨lab, ptn, orbits, active, fixedpts, workperm, firstlab, canonlab, firstcode, canoncode, firsttc,
    canong, autos, ⟨h.graph.arr.unch hu hg, h.graph.rep⟩⟩

theorem Arrays.active' (h : Arrays m S ctx st) {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W S.bA) :
    ∃ aw, ArrayAt m' .Mint64 S.bA 0 (longs aw) S.M ∧ SetRep (fun w => bv64 (aw w)) S.M st.active :=
  let ⟨aw, ha, hr⟩ := h.active; ⟨aw, ha.unch hu hb, hr⟩

theorem Arrays.fixedpts' (h : Arrays m S ctx st) {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W S.bF) :
    ∃ fw, ArrayAt m' .Mint64 S.bF 0 (longs fw) S.M ∧ SetRep (fun w => bv64 (fw w)) S.M st.fixedpts :=
  let ⟨fw, ha, hr⟩ := h.fixedpts; ⟨fw, ha.unch hu hb, hr⟩

theorem Arrays.workperm' (h : Arrays m S ctx st) {W : block → Prop} (hu : Unch m m' W) (hb : ¬ W S.bWP) :
    ∃ v, ArrayAt m' .Mint32 S.bWP 0 v n :=
  let ⟨v, ha⟩ := h.workperm; ⟨v, ha.unch hu hb⟩

/-- A store to one `statsblk` member leaves the others. -/
theorem stats_other {chunk c' : memory_chunk} {off off' : Int} {v w : val}
    (h : FieldAt m chunk S.bst (S.sb + off) v)
    (hst : Mem.store c' m S.bst (zOfInt (S.sb + off')) w = some m')
    (hd : off + csize chunk ≤ off' ∨ off' + csize c' ≤ off) : FieldAt m' chunk S.bst (S.sb + off) v :=
  h.store_other hst (by omega)

end NautyVerified.Proofs.Search.Processnode

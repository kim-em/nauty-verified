import NautyVerified.Proofs.Search.Node.Spec
import NautyVerified.Proofs.Search.Frame

/-!
# The callback's block across search frames

Neither `SFrame` nor `NodeFrame` lets a call change the harness callback's
block `S.bUA`, so its validity and its permission at offset 0 (which the
`userautomproc != NULL` test needs) carry across every search call.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified NautyVerified.Logic NautyVerified.Program
open Hex.GraphIso.Nauty

theorem SFrame.not_bUA {n : Nat} {m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) (hv : Mem.valid_block m S.bUA) :
    ¬ (S.Chg S.bUA ∨ ¬ Mem.valid_block m S.bUA ∨ IsWork m S.bUA) := by
  rintro (⟨-, hne, -⟩ | hnv | hw)
  · exact hne rfl
  · exact hnv hv
  · exact h.work_not hw (by simp [SLoc.blocks])

/-- The callback's block stays valid across a search call. -/
theorem SFrame.valid_bUA {m m' : mem} {S : SLoc} (hf : SFrame m m' S)
    (hv : Mem.valid_block m S.bUA) : Mem.valid_block m' S.bUA :=
  hf.2 _ hv

/-- The callback's permission at offset 0 survives a search call. -/
theorem SFrame.perm_bUA {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) (hf : SFrame m m' S)
    (hv : Mem.valid_block m S.bUA) (hp : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty) :
    Mem.perm m' S.bUA (zOfInt 0) .Cur .Nonempty :=
  (Alloc.Keep.unch hf.1 (SFrame.not_bUA h hv)).perm _ _ hp

theorem NodeFrame.not_bUA {n : Nat} {m : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} {chain : List (block × block)} {level : Nat}
    (h : SearchAt m S ctx st pre nsp) (hok : TcOk m S chain) (hv : Mem.valid_block m S.bUA) :
    ¬ (S.Chg S.bUA ∨ ¬ Mem.valid_block m S.bUA ∨ IsWork m S.bUA ∨ S.bUA = Block.tcnode0 ∨
      (∃ i p, chain[i]? = some p ∧ level ≤ i + 2 ∧ S.bUA = p.1) ∨
      (∃ i p, chain[i]? = some p ∧ level ≤ i + 1 ∧ S.bUA = p.2)) := by
  have hm : S.bUA ∈ S.blocks := by simp [SLoc.blocks]
  rintro (⟨-, hne, -⟩ | hnv | hw | he | ⟨i, p, hp, -, e⟩ | ⟨i, p, hp, -, e⟩)
  · exact hne rfl
  · exact hnv hv
  · exact h.work_not hw hm
  · exact absurd he (by sep_ne h.distinct)
  · exact (hok.apart p (List.mem_of_getElem? hp)).1 (e ▸ hm)
  · exact (hok.apart p (List.mem_of_getElem? hp)).2.1 (e ▸ hm)

/-- The callback's block stays valid across a child node. -/
theorem NodeFrame.valid_bUA {m m' : mem} {S : SLoc} {chain : List (block × block)} {level : Nat}
    (hf : NodeFrame m m' S chain level) (hv : Mem.valid_block m S.bUA) :
    Mem.valid_block m' S.bUA :=
  hf.2 _ hv

/-- The callback's permission at offset 0 survives a child node. -/
theorem NodeFrame.perm_bUA {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} {chain : List (block × block)} {level : Nat}
    (h : SearchAt m S ctx st pre nsp) (hok : TcOk m S chain) (hf : NodeFrame m m' S chain level)
    (hv : Mem.valid_block m S.bUA) (hp : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty) :
    Mem.perm m' S.bUA (zOfInt 0) .Cur .Nonempty :=
  (Alloc.Keep.unch hf.1 (NodeFrame.not_bUA (level := level) h hok hv)).perm _ _ hp

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

theorem SFrameG.not_bUA {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {pre nsp : Bool} (h : SearchAtG D m S gl cl G st pre nsp)
    (hv : Mem.valid_block m S.bUA) :
    ¬ (S.ChgG D gl cl S.bUA ∨ ¬ Mem.valid_block m S.bUA ∨ IsWorkG D m S.bUA) := by
  rintro (⟨-, hne, -⟩ | hnv | hw)
  · exact hne rfl
  · exact hnv hv
  · exact h.work_not hw (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inl (by simp))))))

theorem SFrameG.valid_bUA {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    (hf : SFrameG D m m' S gl cl) (hv : Mem.valid_block m S.bUA) : Mem.valid_block m' S.bUA :=
  hf.2 _ hv

theorem SFrameG.perm_bUA {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) (hf : SFrameG D m m' S gl cl)
    (hv : Mem.valid_block m S.bUA) (hp : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty) :
    Mem.perm m' S.bUA (zOfInt 0) .Cur .Nonempty :=
  (Alloc.Keep.unch hf.1 (SFrameG.not_bUA h hv)).perm _ _ hp

theorem NodeFrameG.not_bUA {n : Nat} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {chain : List (block × block)} {level : Nat}
    (h : SearchAtG D m S gl cl G st pre nsp) (hok : TcOkG D m S gl cl chain)
    (hv : Mem.valid_block m S.bUA) :
    ¬ (S.ChgG D gl cl S.bUA ∨ ¬ Mem.valid_block m S.bUA ∨ IsWorkG D m S.bUA ∨
      S.bUA = E.tcnode0 ∨
      (∃ i p, chain[i]? = some p ∧ level ≤ i + 2 ∧ S.bUA = p.1) ∨
      (∃ i p, chain[i]? = some p ∧ level ≤ i + 1 ∧ S.bUA = p.2)) := by
  have hm : S.bUA ∈ S.blocksG D gl cl :=
    SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inl (by simp)))))
  rintro (⟨-, hne, -⟩ | hnv | hw | he | ⟨i, p, hp, -, e⟩ | ⟨i, p, hp, -, e⟩)
  · exact hne rfl
  · exact hnv hv
  · exact h.work_not hw hm
  · exact absurd he (by sep_ne h.lit)
  · exact (hok.apart p (List.mem_of_getElem? hp)).1 (e ▸ hm)
  · exact (hok.apart p (List.mem_of_getElem? hp)).2.1 (e ▸ hm)

theorem NodeFrameG.valid_bUA {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {chain : List (block × block)} {level : Nat}
    (hf : NodeFrameG D m m' S gl cl chain level) (hv : Mem.valid_block m S.bUA) :
    Mem.valid_block m' S.bUA :=
  hf.2 _ hv

theorem NodeFrameG.perm_bUA {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {chain : List (block × block)} {level : Nat}
    (h : SearchAtG D m S gl cl G st pre nsp) (hok : TcOkG D m S gl cl chain)
    (hf : NodeFrameG D m m' S gl cl chain level)
    (hv : Mem.valid_block m S.bUA) (hp : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty) :
    Mem.perm m' S.bUA (zOfInt 0) .Cur .Nonempty :=
  (Alloc.Keep.unch hf.1 (NodeFrameG.not_bUA (level := level) h hok hv)).perm _ _ hp

end Generic

end NautyVerified.Proofs.Search

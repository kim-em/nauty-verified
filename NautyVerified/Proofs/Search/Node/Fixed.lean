import NautyVerified.Proofs.Search.Node.Rebuild
import NautyVerified.Proofs.Set.GlobalDel

/-!
# Fixing a vertex: `ADDELEMENT(fixedpts, tv)` and `DELELEMENT(fixedpts, tv)`

Both nodes record the vertex fixed for a child in nauty.c's global set
`fixedpts` before the recursive call and remove it afterwards;
`wp_fixAdd`/`wp_fixDel` give `SearchAt` for HexGraphIso's
`fixedpts.insert tv` and `fixedpts.erase tv`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (longs)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

/-- The arrays of `SearchAt` across a change of `fixedpts`' block only. -/
theorem Arrays.setFixed {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    (h : Arrays m S ctx st) (hd : S.blocks.Pairwise (· ≠ ·)) (hu : Unch m m' (· = S.bF))
    {fw : Nat → Lib.Integers.int64} {s : VSet n} (hf : ArrayAt m' .Mint64 S.bF 0 (longs fw) S.M)
    (hr : SetRep (fun w => bv64 (fw w)) S.M s) :
    Arrays m' S ctx { st with fixedpts := s } := by
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨wv, hwv⟩ := h.workperm
  exact
    { lab := h.lab.unch hu (by sep_ne hd)
      ptn := h.ptn.unch hu (by sep_ne hd)
      orbits := h.orbits.unch hu (by sep_ne hd)
      active := ⟨aw, ha.unch hu (by sep_ne hd), har⟩
      fixedpts := ⟨fw, hf, hr⟩
      workperm := ⟨wv, hwv.unch hu (by sep_ne hd)⟩
      firstlab := h.firstlab.unch hu (by sep_ne hd)
      canonlab := h.canonlab.unch hu (by sep_ne hd)
      firstcode := h.firstcode.unch hu (by sep_ne hd)
      canoncode := h.canoncode.unch hu (by sep_ne hd)
      firsttc := h.firsttc.unch hu (by sep_ne hd)
      canong := h.canong.unch hu (by sep_ne hd)
      autos := h.autos.unch hu (by sep_ne hd) (by sep_ne hd)
      graph := ⟨h.graph.arr.unch hu (by sep_ne hd), h.graph.rep⟩ }

/-- `SearchAt` after writing `fixedpts`' words. -/
theorem SearchAt.setFixed {n : Nat} {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp) (hu : Unch m m' (· = S.bF))
    (hk : Keep m m' S.bF)
    {fw : Nat → Lib.Integers.int64} {s : VSet n} (hf : ArrayAt m' .Mint64 S.bF 0 (longs fw) S.M)
    (hr : SetRep (fun w => bv64 (fw w)) S.M s) :
    SearchAt m' S ctx { st with fixedpts := s } pre nsp := by
  have hd := h.distinct
  refine h.rebuild (L := [S.bF]) (hu.mono fun z hz => by simp [hz])
    (fun z hz => by simp at hz; subst hz; simp [SLoc.wr, SLoc.wrV]) ?_
    { h.scalars.unch hu (by sep_all hd) with } { h.stats.unch hu (by sep_ne hd) with }
    (h.arrays.setFixed hd hu hf hr) { h.inv with }
  intro z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Keep.unch hu (by sep_ne hd)
  · exact hk
  all_goals exact Keep.unch hu (by sep_ne hd)

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- `SearchAtG` after writing `fixedpts`' words. -/
theorem SearchAtG.setFixed {n : Nat} {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
    {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) (hu : Unch m m' (· = S.bF)) (hk : Keep m m' S.bF)
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z)
    {fw : Nat → Lib.Integers.int64} {s : VSet n} (hf : ArrayAt m' .Mint64 S.bF 0 (longs fw) S.M)
    (hr : SetRep (fun w => bv64 (fw w)) S.M s) :
    SearchAtG D m' S gl cl G { st with fixedpts := s } pre nsp := by
  have hd := h.lit
  have hA := h.arrays
  obtain ⟨aw, ha, har⟩ := hA.active
  obtain ⟨wv, hwv⟩ := hA.workperm
  refine h.rebuild (L := [S.bF]) (hu.mono fun z hz => by simp [hz]) (by simp) ?_ hv
    { h.scalars.unch hu (by sep_all hd) with } { h.stats.unch hu (by sep_ne hd) with }
    { lab := hA.lab.unch hu (by sep_ne hd)
      ptn := hA.ptn.unch hu (by sep_ne hd)
      orbits := hA.orbits.unch hu (by sep_ne hd)
      active := ⟨aw, ha.unch hu (by sep_ne hd), har⟩
      fixedpts := ⟨fw, hf, hr⟩
      workperm := ⟨wv, hwv.unch hu (by sep_ne hd)⟩
      firstlab := hA.firstlab.unch hu (by sep_ne hd)
      canonlab := hA.canonlab.unch hu (by sep_ne hd)
      firstcode := hA.firstcode.unch hu (by sep_ne hd)
      canoncode := hA.canoncode.unch hu (by sep_ne hd)
      firsttc := hA.firsttc.unch hu (by sep_ne hd)
      canong := D.canon_unch hA.canong hu fun z hz e => h.canon_ne hz (.inr (.inr (.inl (by simp)))) e
      autos := hA.autos.unch hu (by sep_ne hd) (by sep_ne hd)
      graph := D.graph_unch hA.graph hu fun z hz e => h.graph_ne hz (.inr (.inr (.inl (by simp)))) e }
    { h.inv with }
  intro z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Keep.unch hu (by sep_ne hd)
  · exact hk
  all_goals exact Keep.unch hu (by sep_ne hd)

/-- `ADDELEMENT(fixedpts, tv)`, for `D`. -/
theorem wp_fixAddG {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} {v : Nat} (h : SearchAtG D m S gl cl G st pre nsp)
    (hge : PTree.get dense.id.«nauty:fixedpts» e = none) (hbe : PTree.get dense.id.«nauty:bit» e = none)
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v))) (hv : v < n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G { st with fixedpts := st.fixedpts.insert v } pre nsp →
      Unch m m' (· = S.bF) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (Set.addElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
      Q e le m := by
  have hnl := h.nlt
  have hnM := h.nM
  have hMl := h.Mlt
  obtain ⟨fw, hf, hfr⟩ := h.arrays.fixedpts
  refine Set.wp_addElementGV hge E.find_nautyFixedpts
    (h.dyns.fixedpts.ptr (by have := h.dyns.capF; have := h.M1; omega)) hf (by omega)
    (c := v) htv rfl (by omega) (by omega) hbe E.find_nautyBit h.tables.env.nautyBit ?_
  intro m' hf' hu _ hk hg
  exact hQ m' (h.setFixed hu hk hg hf' (Set.setRep_add hfr hv)) hu hg

/-- `DELELEMENT(fixedpts, tv)`, for `D`. -/
theorem wp_fixDelG {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} {v : Nat} (h : SearchAtG D m S gl cl G st pre nsp)
    (hge : PTree.get dense.id.«nauty:fixedpts» e = none) (hbe : PTree.get dense.id.«nauty:bit» e = none)
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v))) (hv : v < n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G { st with fixedpts := st.fixedpts.erase v } pre nsp →
      Unch m m' (· = S.bF) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (Set.delElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
      Q e le m := by
  have hnl := h.nlt
  have hnM := h.nM
  have hMl := h.Mlt
  obtain ⟨fw, hf, hfr⟩ := h.arrays.fixedpts
  refine Set.wp_delElementG hge E.find_nautyFixedpts
    (h.dyns.fixedpts.ptr (by have := h.dyns.capF; have := h.M1; omega)) hf (by omega)
    (c := v) htv rfl (by omega) (by omega) hbe E.find_nautyBit h.tables.env.nautyBit ?_
  intro m' hf' hu _ hk hg
  exact hQ m' (h.setFixed hu hk hg hf' (Set.setRep_del hfr (by omega))) hu hg

end Generic

/-- `ADDELEMENT(fixedpts, tv)`. -/
theorem wp_fixAdd {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {v : Nat}
    (h : SearchAt m S ctx st pre nsp)
    (hge : PTree.get dense.id.«nauty:fixedpts» e = none) (hbe : PTree.get dense.id.«nauty:bit» e = none)
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v))) (hv : v < n)
    (hQ : ∀ m', SearchAt m' S ctx { st with fixedpts := st.fixedpts.insert v } pre nsp →
      Unch m m' (· = S.bF) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (Set.addElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
      Q e le m :=
  wp_fixAddG h.toG hge hbe htv hv fun m' h' hu hg => hQ m' (h'.dense h.gw) hu hg

/-- `DELELEMENT(fixedpts, tv)`. -/
theorem wp_fixDel {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {v : Nat}
    (h : SearchAt m S ctx st pre nsp)
    (hge : PTree.get dense.id.«nauty:fixedpts» e = none) (hbe : PTree.get dense.id.«nauty:bit» e = none)
    (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v))) (hv : v < n)
    (hQ : ∀ m', SearchAt m' S ctx { st with fixedpts := st.fixedpts.erase v } pre nsp →
      Unch m m' (· = S.bF) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (Set.delElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
      Q e le m :=
  wp_fixDelG h.toG hge hbe htv hv fun m' h' hu hg => hQ m' (h'.dense h.gw) hu hg

end NautyVerified.Proofs.Search

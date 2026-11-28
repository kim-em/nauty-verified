import NautyVerified.Proofs.Search.Node.FirstSteps

/-!
# Locals and the `firsttc` store of `firstpathnode0`

`wp_localStore`: `x = rhs;` for an addressable `int` local `x`.
`wp_firsttcStore`: `firsttc[level] = tc;` gives `SearchAt` for
`firsttc.set! level tc`, the `tc` local holding `tc`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Refine (tv)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-- `x = rhs;` for an addressable `int` local. -/
theorem wp_localStore {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {x : ident} {b : block} (hx : PTree.get x e = some (b, tint))
    (harr : ∃ vals, ArrayAt m .Mint32 b 0 vals 1) {rhs : expr} {w : Int}
    (hr : Exec.evalExpr ge e le m rhs = some (.Vint (ir w))) (hty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 b 0 (fun _ => .Vint (ir w)) 1 → Unch m m' (· = b) →
      Alloc.KeepA m m' → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Evar x tint) rhs) Q e le m := by
  obtain ⟨vals, ha⟩ := harr
  obtain ⟨m', hst, harr', -⟩ := store_array ha (show 0 < 1 by decide) (.Vint (ir w)) rfl
  apply wp_assign_eval
  rw [hr]
  simp only [Exec.evalLvalue, Exec.lvalOfVar, hx, hty]
  simp only [ite_true, typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [show Ptrofs.unsigned Ptrofs.zero = elemOfs .Mint32 0 0 from rfl, hst]
  exact hQ m' (harr'.congr fun i hi => by simp [upd, show i = 0 by omega]) (Unch.store hst rfl)
    (Alloc.KeepA.storeArr ha hst) fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz

theorem Arrays.setFirsttc {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n}
    (h : Arrays m S ctx st) (hu : Unch m m' (· = S.bTC)) (hd : S.blocks.Pairwise (· ≠ ·))
    {ft : Array Int} (hft : ArrayAt m' .Mint32 S.bTC 0 (intsZ ft) (n + 2)) :
    Arrays m' S ctx { st with firsttc := ft } := by
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu (by sep_ne hd), h.ptn.unch hu (by sep_ne hd),
    h.orbits.unch hu (by sep_ne hd), ⟨aw, ha.unch hu (by sep_ne hd), har⟩,
    ⟨fw, hf.unch hu (by sep_ne hd), hfr⟩, ⟨wv, hwv.unch hu (by sep_ne hd)⟩,
    h.firstlab.unch hu (by sep_ne hd), h.canonlab.unch hu (by sep_ne hd),
    h.firstcode.unch hu (by sep_ne hd), h.canoncode.unch hu (by sep_ne hd), hft,
    h.canong.unch hu (by sep_ne hd), h.autos.unch hu (by sep_ne hd) (by sep_ne hd),
    ⟨h.graph.arr.unch hu (by sep_ne hd), h.graph.rep⟩⟩

/-- `firsttc[level] = tc;` -/
theorem wp_firsttcStore {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level : Nat} {tc : Int} {bc : block}
    (h : SearchAt m S ctx st pre nsp)
    (hE : PTree.get dense.id.«nauty:firsttc» e = none)
    (hec : PTree.get dense.id.«tc» e = some (bc, tint))
    (hcv : Mem.load .Mint32 m bc (zOfInt 0) = some (.Vint (ir tc)))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (ht1 : -1 ≤ tc) (ht2 : tc < n) (hn : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx { st with firsttc := st.firsttc.set! level tc } pre nsp →
      Unch m m' (· ∈ [S.bTC]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (Alloc.gat dense.id.«nauty:firsttc» (tv dense.id.level))
      (.Evar dense.id.«tc» tint)) Q e le m := by
  have hnl := h.nlt
  have hd := h.distinct
  refine wp_gstoreV hE Program.find_nautyFirsttc
    (h.dyns.firsttc.ptr (by have := h.dyns.capTC; omega)) h.arrays.firsttc (by omega)
    (tv dense.id.level) level (by omega) hlev rfl _ tc (eval_local hec hcv) rfl ?_
  intro m' harr hu hk hv
  have hU : Unch m m' (· ∈ [S.bTC]) := hu.mono fun z hz => by simp [hz]
  have hts := h.inv.firsttcSize
  refine hQ m' ?_ hU hv
  refine h.rebuild hU (fun z hz => by simp at hz; subst hz; simp [SLoc.wr, SLoc.wrV])
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hk | exact Keep.unch hu (by sep_ne hd))
    { h.scalars.unch hu (by sep_all hd) with } { h.stats.unch hu (by sep_ne hd) with }
    (h.arrays.setFirsttc hu hd (by rw [intsZ_set (by omega)]; exact harr)) ?_
  have i := h.inv
  exact { i with
    firsttcRange := fun j hj => by
      show -1 ≤ (st.firsttc.set! level tc)[j]! ∧ (st.firsttc.set! level tc)[j]! < n
      by_cases hjl : j = level
      · subst hjl; rw [Array.getElem!_set!_self _ _ _ (by omega)]; omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjl)]; exact i.firsttcRange j hj
    firsttcSize := by show (st.firsttc.set! level tc).size = n + 2; simp [hts] }

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

theorem ArraysG.setFirsttc {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {m₀ : mem} {st₀ : SearchState n (O.Canon n)}
    {pre nsp : Bool} (h : ArraysG D m S gl cl G st)
    (h₀ : SearchAtG D m₀ S gl cl G st₀ pre nsp) (hu : Unch m m' (· = S.bTC))
    {ft : Array Int} (hft : ArrayAt m' .Mint32 S.bTC 0 (intsZ ft) (n + 2)) :
    ArraysG D m' S gl cl G { st with firsttc := ft } := by
  have hd := h₀.lit
  obtain ⟨aw, ha, har⟩ := h.active
  obtain ⟨fw, hf, hfr⟩ := h.fixedpts
  obtain ⟨wv, hwv⟩ := h.workperm
  exact ⟨h.lab.unch hu (by sep_ne hd), h.ptn.unch hu (by sep_ne hd),
    h.orbits.unch hu (by sep_ne hd), ⟨aw, ha.unch hu (by sep_ne hd), har⟩,
    ⟨fw, hf.unch hu (by sep_ne hd), hfr⟩, ⟨wv, hwv.unch hu (by sep_ne hd)⟩,
    h.firstlab.unch hu (by sep_ne hd), h.canonlab.unch hu (by sep_ne hd),
    h.firstcode.unch hu (by sep_ne hd), h.canoncode.unch hu (by sep_ne hd), hft,
    D.canon_unch h.canong hu fun z hz e => h₀.canon_ne hz (.inr (.inr (.inl (by simp)))) e,
    h.autos.unch hu (by sep_ne hd) (by sep_ne hd),
    D.graph_unch h.graph hu fun z hz e => h₀.graph_ne hz (.inr (.inr (.inl (by simp)))) e⟩

/-- `firsttc[level] = tc;`, for `D`. -/
theorem wp_firsttcStoreG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    {level : Nat} {tc : Int} {bc : block}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hE : PTree.get dense.id.«nauty:firsttc» e = none)
    (hec : PTree.get dense.id.«tc» e = some (bc, tint))
    (hcv : Mem.load .Mint32 m bc (zOfInt 0) = some (.Vint (ir tc)))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level)))
    (ht1 : -1 ≤ tc) (ht2 : tc < n) (hn : level ≤ n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G { st with firsttc := st.firsttc.set! level tc } pre nsp →
      Unch m m' (· ∈ [S.bTC]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (Alloc.gat dense.id.«nauty:firsttc» (tv dense.id.level))
      (.Evar dense.id.«tc» tint)) Q e le m := by
  have hnl := h.nlt
  have hd := h.lit
  refine wp_gstoreV hE E.find_nautyFirsttc
    (h.dyns.firsttc.ptr (by have := h.dyns.capTC; omega)) h.arrays.firsttc (by omega)
    (tv dense.id.level) level (by omega) hlev rfl _ tc (eval_local hec hcv) rfl ?_
  intro m' harr hu hk hv
  have hU : Unch m m' (· ∈ [S.bTC]) := hu.mono fun z hz => by simp [hz]
  have hts := h.inv.firsttcSize
  refine hQ m' ?_ hU hv
  refine h.rebuild hU (fun z hz => by simp at hz; subst hz; exact .inr (.inl (by simp)))
    (fun z hz => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hk | exact Keep.unch hu (by sep_ne hd)) hv
    { h.scalars.unch hu (by sep_all hd) with } { h.stats.unch hu (by sep_ne hd) with }
    (h.arrays.setFirsttc h hu (by rw [intsZ_set (by omega)]; exact harr)) ?_
  have i := h.inv
  exact { i with
    firsttcRange := fun j hj => by
      show -1 ≤ (st.firsttc.set! level tc)[j]! ∧ (st.firsttc.set! level tc)[j]! < n
      by_cases hjl : j = level
      · subst hjl; rw [Array.getElem!_set!_self _ _ _ (by omega)]; omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjl)]; exact i.firsttcRange j hj
    firsttcSize := by show (st.firsttc.set! level tc).size = n + 2; simp [hts] }

end Generic

end NautyVerified.Proofs.Search

import NautyVerified.Proofs.Search.Processnode.Calls
import NautyVerified.Logic.Grow

/-!
# `processnode`'s comparison with the best leaf

`wp_updatecan`: `(*dispatch.updatecan)(g, canong, canonlab, samerows, m, n)`
leaves `canong` holding HexGraphIso's `updatecan`.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (Keep DynAt)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}

/-- `sr` holds `v`. -/
abbrev SrAt (m : mem) (bsr : block) (v : Int) : Prop :=
  ArrayAt m .Mint32 bsr (intOfZ (Ptrofs.unsigned Ptrofs.zero)) (fun _ => .Vint (ir v)) 1

/-- A pointer global. -/
theorem eval_gptr {e : env} {le : temp_env} {m : mem} {g : ident} {b : block} {v : val}
    {ty : type} (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some b)
    (hacc : access_mode ty = .By_value .Mint64) (h : PtrAt m b v) :
    Exec.evalExpr ge e le m (.Evar g ty) = some v := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg, Exec.derefLoc, hacc, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  exact h.load

theorem Keep.access' {m m' : mem} {b : block} (hk : Keep m m' b) {chunk : memory_chunk} {ofs : Z}
    {p : Common.Memtype.permission} (h : Mem.valid_access m chunk b ofs p) : Mem.valid_access m' chunk b ofs p :=
  ⟨fun o ho => hk.perm _ _ (h.1 o ho), h.2⟩

abbrev updatecanCall : statement :=
  .Scall none
    (.Ederef
      (.Efield (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr)) dense.id.«updatecan»
        (tptr (tfun [(tptr tulong), (tptr tulong), (tptr tint), tint, tint, tint] .Tvoid)))
      (tfun [(tptr tulong), (tptr tulong), (tptr tint), tint, tint, tint] .Tvoid))
    [(.Evar dense.id.«nauty:g» (tptr tulong)),
     (.Evar dense.id.«nauty:canong» (tptr tulong)),
     (.Evar dense.id.«nauty:canonlab» (tptr tint)),
     (.Evar dense.id.«nauty:samerows» tint),
     (.Evar dense.id.«nauty:m» tint),
     (.Evar dense.id.«nauty:n» tint)]

variable {n : Nat} {D : DispatchC ge O} {m₀ m₁ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
  {G : O.Gr n} {e : env} {bsr : block} {st : SearchState n (O.Canon n)} {nsp : Bool}

/-- A map of `0 .. n-1` onto itself, as the procedures take it. -/
theorem lab_inj {lab : Array Nat} (hl : ∀ i < n, lab[i]! < n) (hs : ∀ v < n, ∃ i < n, lab[i]! = v) :
    ∀ i < n, ∀ j < n, lab[i]! = lab[j]! → i = j :=
  fun i hi j hj he => surj_inj (f := fun i => lab[i]!) hl hs i j hi hj he

theorem wp_updatecan {f : function} {Q : Post} {le : temp_env} (C : Classifier O)
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (hcl : ∀ i < n, st.canonlab[i]! < n) (hcs : ∀ v < n, ∃ i < n, st.canonlab[i]! = v)
    (hfit : O.Fits G (O.rows st.canong) st.canonlab st.samerows)
    (hQ : ∀ m', PAt D m₀ m₁ m' S gl cl G bsr
        { st with canong := C.update G st.canong st.canonlab st.samerows } nsp →
      D.CanonRep m' cl S.bc S.cofs S.M (O.rows (C.update G st.canong st.canonlab st.samerows)) n →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Q.normal E0 e le m') :
    Wp xi ge f updatecanCall Q e le m := by
  have hs := h.search
  have hinv := hs.inv
  have hcCL : 0 < S.capCL := by have := hs.dyns.capCL; have := hs.n0; omega
  obtain ⟨fd, hfd, hty, hsat⟩ := D.updatecan_fn xi
  refine wp_call (vf := .Vptr D.updatecan Ptrofs.zero)
    (targs := [tptr tulong, tptr tulong, tptr tint, tint, tint, tint]) (tres := .Tvoid)
    (cc := cc_default) (vargs := [.Vptr S.bg S.gofs, .Vptr S.bc S.cofs, .Vptr S.bCL Ptrofs.zero,
      .Vint (ir st.samerows), .Vint (ir S.M), .Vint (ir n)]) fd _
    (hsat G gl S.bg S.gofs (O.rows st.canong) cl S.bc S.cofs S.bCL Ptrofs.zero st.canonlab
      st.samerows S.M) rfl
    (eval_dispatch (c.eg _ (by decide)) E.field_dUpdatecan rfl (by decide) (by decide)
      hs.fixed.dUpdatecan)
    ?_ hfd hty ?_ ?_
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) E.find_g rfl hs.fixed.g,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) E.find_canong rfl hs.fixed.canong,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) E.find_nautyCanonlab rfl
        ⟨hs.dyns.canonlab.ptr hcCL, hs.dyns.canonlab.bpW⟩,
      eval_gint (c.eg _ (by decide)) E.find_samerows hs.scalars.samerows,
      eval_gint (c.eg _ (by decide)) E.find_m hs.fixed.mm,
      eval_gint (c.eg _ (by decide)) E.find_n hs.fixed.nn, typeof, cop]
  · exact ⟨rfl, hs.ctx, hs.arrays.graph, hs.graphOk, hs.arrays.canong, hinv.canong,
      hs.arrays.canonlab, hinv.canonlabSize, hcl, hcs, lab_inj hcl hcs, hinv.samerows,
      h.sepGC c (by simp) (by simp [ArgBlock]), hfit⟩
  · rintro t r m' ⟨rfl, hcr, hok, hstep⟩
    have hout : ∀ z, z ∈ D.canonBlocks cl S.bc → z ∈ D.canonBlocks cl S.bc ∨ z = bsr :=
      fun z hz => .inl hz
    have hrows := C.rows_update G st.canong st.canonlab st.samerows
    have hcr' : D.CanonRep m' cl S.bc S.cofs S.M
        (O.rows (C.update G st.canong st.canonlab st.samerows)) n := by
      rw [hrows]; exact hcr
    have hsrw : ¬ (bsr ∈ D.canonBlocks cl S.bc ∨ bsr ∈ D.wglobs ∨ D.IsWork m bsr ∨
        ¬ Mem.valid_block m bsr) := by
      rintro (h1 | h1 | h1 | h1)
      · exact c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inr (.inl h1)))) rfl
      · exact c.ne_blocks
          (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inr (D.wglobs_sub _ h1))))))) rfl
      · exact h.work_ne c (.inl h1) rfl
      · exact h1 (h.grow1 _ c.valid1)
    refine hQ m' (h.call c hstep hout
      ((hs.scalars.unch hstep.unch fun z hz => h.stepNotE c hout (by revert z; simp)).cast rfl)
      ((hs.stats.unch hstep.unch (h.stepNotV c hout (.inl (by simp)))).cast rfl)
      (hs.arrays.setCanong hstep.unch (h.arraysW c hout) (fun z hz => h.stepNotG c hout hz)
        (D.canon_le hcr' hinv.samerows))
      { hinv with canong := by show O.StoreOk G (O.rows _); rw [hrows]; exact hok }
      (hstep.unch.access _ _ _ _ hsrw h.srW)) hcr' fun v hv => hv.unch hstep.unch hsrw

abbrev testcanlabCall : statement :=
  .Scall (some (idOf 705))
    (.Ederef
      (.Efield (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr)) dense.id.«testcanlab»
        (tptr (tfun [(tptr tulong), (tptr tulong), (tptr tint), (tptr tint), tint, tint] tint)))
      (tfun [(tptr tulong), (tptr tulong), (tptr tint), (tptr tint), tint, tint] tint))
    [(.Evar dense.id.«nauty:g» (tptr tulong)),
     (.Evar dense.id.«nauty:canong» (tptr tulong)),
     (.Etempvar dense.id.«lab» (tptr tint)),
     (.Eaddrof (.Evar dense.id.«sr» tint) (tptr tint)),
     (.Evar dense.id.«nauty:m» tint),
     (.Evar dense.id.«nauty:n» tint)]

theorem wp_testcanlab {f : function} {Q : Post} {le : temp_env} (c : PCtx D m₀ m₁ S gl cl e bsr)
    (h : PAt D m₀ m₁ m S gl cl G bsr st nsp) (hsr : st.samerows = n) {v0 : Int}
    (hs0 : SrAt m bsr v0) (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hQ : ∀ m', PAt D m₀ m₁ m' S gl cl G bsr st nsp →
      SrAt m' bsr ((O.testcanlab G (O.rows st.canong) st.lab).2 : Int) →
      Q.normal E0 e
        (PTree.set (idOf 705) (.Vint (ir (O.testcanlab G (O.rows st.canong) st.lab).1)) le) m') :
    Wp xi ge f testcanlabCall Q e le m := by
  have hs := h.search
  have hinv := hs.inv
  obtain ⟨fd, hfd, hty, hsat⟩ := D.testcanlab_fn xi
  refine wp_call (vf := .Vptr D.testcanlab Ptrofs.zero)
    (targs := [tptr tulong, tptr tulong, tptr tint, tptr tint, tint, tint]) (tres := tint)
    (cc := cc_default) (vargs := [.Vptr S.bg S.gofs, .Vptr S.bc S.cofs, .Vptr S.bl S.lofs,
      .Vptr bsr Ptrofs.zero, .Vint (ir S.M), .Vint (ir n)]) fd _
    (hsat G gl S.bg S.gofs (O.rows st.canong) cl S.bc S.cofs S.bl S.lofs st.lab bsr Ptrofs.zero
      S.M) rfl
    (eval_dispatch (c.eg _ (by decide)) E.field_dTestcanlab rfl (by decide) (by decide)
      hs.fixed.dTestcanlab)
    ?_ hfd hty ?_ ?_
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) E.find_g rfl hs.fixed.g,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) E.find_canong rfl hs.fixed.canong,
      eval_gint (c.eg _ (by decide)) E.find_m hs.fixed.mm,
      eval_gint (c.eg _ (by decide)) E.find_n hs.fixed.nn, typeof, cop]
    simp only [Exec.evalExpr, hlab, Exec.evalLvalue, Exec.lvalOfVar, c.esr, typeof, cop]
    rfl
  · refine ⟨rfl, hs.ctx, hs.arrays.graph, hs.graphOk, D.canon_le hs.arrays.canong (by omega),
      hinv.canong, hs.arrays.lab, hinv.labSize, hinv.labSmall, hinv.labSurj,
      lab_inj hinv.labSmall hinv.labSurj, ⟨_, hs0⟩, h.sepGC c ?_ (by simp [ArgBlock])⟩
    simpa using c.ne_blocks (SLoc.mem_blocksG_of _ (.inr (.inl (by simp))))
  · rintro t r m' ⟨rfl, rfl, harr, hstep⟩
    exact hQ m' (h.callSame c hstep (fun z hz => hz)
      (Keep.access' (hstep.keep bsr rfl (h.grow1 _ c.valid1)) h.srW)) harr

end NautyVerified.Proofs.Search.Processnode

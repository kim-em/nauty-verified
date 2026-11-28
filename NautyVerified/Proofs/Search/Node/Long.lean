import NautyVerified.Proofs.Search.Node.LoopSteps
import NautyVerified.Proofs.Prune.Long
import NautyVerified.Proofs.Search.Node.Prune

/-!
# The stored automorphism pairs as `longprune` reads them

`AutosAt.pairs`: the workspace words holding `st.autos` are `PairsAt` from
offset 0, the form `longpruneSpec` takes.

`wp_nodeLong`: `if (tv == tv1) { longprune(tcell, fixedpts, workspace, fmptr, M);
if (doschreier) pruneset(…); }` is HexGraphIso's `longprune` when `tv == tv1`
(`doschreier` is 0). `AutosAtG.pairs` and `wp_nodeLongG` are the same over
`SearchAtG D`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified.Source CompCert4Lean.Cfrontend.Ctypes
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Prune.Long (PairsAt)
open Hex.GraphIso.Nauty

theorem pairsAt_of {n : Nat} {ww : Nat → Lib.Integers.int64} {M : Nat} :
    ∀ (L : List (VSet n × VSet n)) (o : Nat),
      (∀ i < L.length, SetRep (fun w => bv64 (ww (o + 2 * M * i + w))) M L[i]!.1 ∧
        SetRep (fun w => bv64 (ww (o + 2 * M * i + M + w))) M L[i]!.2) →
      PairsAt ww M o L
  | [], _, _ => trivial
  | p :: L, o, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem!_cons_zero] at h0
    refine ⟨h0.1, h0.2, pairsAt_of L (o + M + M) fun i hi => ?_⟩
    have hs := h (i + 1) (by simp; omega)
    simp only [List.getElem!_cons_succ] at hs
    have e1 : (fun w => bv64 (ww (o + 2 * M * (i + 1) + w))) =
        fun w => bv64 (ww (o + M + M + 2 * M * i + w)) :=
      funext fun w => by congr 2; rw [Nat.mul_succ]; omega
    have e2 : (fun w => bv64 (ww (o + 2 * M * (i + 1) + M + w))) =
        fun w => bv64 (ww (o + M + M + 2 * M * i + M + w)) :=
      funext fun w => by congr 2; rw [Nat.mul_succ]; omega
    rw [e1, e2] at hs
    exact hs

theorem AutosAt.pairs {n : Nat} {m : mem} {S : SLoc} {autos : Array (VSet n × VSet n)}
    (h : AutosAt m S autos) :
    ∃ ww, ArrayAt m .Mint64 S.bws S.wb (longs ww) (2 * wsPairs * S.M) ∧
      PairsAt ww S.M 0 autos.toList := by
  obtain ⟨ww, ha, hr⟩ := h.arr
  refine ⟨ww, ha, pairsAt_of _ 0 fun i hi => ?_⟩
  have hi' : i < autos.size := by simpa using hi
  obtain ⟨h1, h2⟩ := hr i hi'
  have e : autos.toList[i]! = autos[i]! := by
    simp [getElem!_pos autos.toList i (by simpa using hi), getElem!_pos autos i hi']
  rw [e]
  simp only [Nat.zero_add]
  exact ⟨h1, h2⟩

theorem AutosAtG.pairs {ge : genv} [E : NautyEnv ge] {n : Nat} {m : mem} {S : SLoc} {autos : Array (VSet n × VSet n)}
    (h : AutosAtG m S autos) :
    ∃ ww, ArrayAt m .Mint64 S.bws S.wb (longs ww) (2 * wsPairs * S.M) ∧
      PairsAt ww S.M 0 autos.toList := by
  obtain ⟨ww, ha, hr⟩ := h.arr
  refine ⟨ww, ha, pairsAt_of _ 0 fun i hi => ?_⟩
  have hi' : i < autos.size := by simpa using hi
  obtain ⟨h1, h2⟩ := hr i hi'
  have e : autos.toList[i]! = autos[i]! := by
    simp [getElem!_pos autos.toList i (by simpa using hi), getElem!_pos autos i hi']
  rw [e]
  simp only [Nat.zero_add]
  exact ⟨h1, h2⟩

variable {xi : ExternalCalls}

/-- `pruneset(fixedpts, gp, &gens, tcell, M, n)`, never reached (`doschreier` is 0). -/
abbrev prunesetCall : statement :=
  .Scall none
    (.Evar dense.id.«pruneset»
      (tfun [tptr tulong, tptr (Tstruct dense.id.«schreierlevel» noattr),
        tptr (tptr (Tstruct dense.id.«permnodestruct» noattr)), tptr tulong, tint, tint] .Tvoid))
    [.Evar dense.id.«nauty:fixedpts» (tptr tulong),
     .Evar dense.id.«nauty:gp» (tptr (Tstruct dense.id.«schreierlevel» noattr)),
     .Eaddrof (.Evar dense.id.«nauty:gens» (tptr (Tstruct dense.id.«permnodestruct» noattr)))
       (tptr (tptr (Tstruct dense.id.«permnodestruct» noattr))),
     .Etempvar dense.id.«tcell» (tptr tulong), .Evar dense.id.«nauty:m» tint,
     .Evar dense.id.«nauty:n» tint]

/-- The `longprune` call. -/
abbrev longCall : statement :=
  .Scall none
    (.Evar dense.id.«longprune»
      (tfun [tptr tulong, tptr tulong, tptr tulong, tptr tulong, tint] .Tvoid))
    [.Etempvar dense.id.«tcell» (tptr tulong), .Evar dense.id.«nauty:fixedpts» (tptr tulong),
     .Evar dense.id.«nauty:workspace» (tptr tulong), .Evar dense.id.«nauty:fmptr» (tptr tulong),
     .Evar dense.id.«nauty:m» tint]

/-- `if (tv == tv1) { longprune(…); if (doschreier) pruneset(…); }` -/
abbrev longIf : statement :=
  .Sifthenelse (.Ebinop .Oeq (Refine.tv dense.id.«tv») (Refine.tv dense.id.«tv1») tint)
    (.Ssequence (Set.sk longCall)
      (Set.sk (.Sifthenelse (.Evar dense.id.«nauty:doschreier» tint) (Set.sk prunesetCall) .Sskip)))
    .Sskip

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

theorem wp_nodeLongG {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} (h : SearchAtG D m S gl cl G st pre nsp)
    (hge : ∀ x ∈ [dense.id.«longprune», dense.id.«nauty:fixedpts», dense.id.«nauty:workspace»,
      dense.id.«nauty:fmptr», dense.id.«nauty:m», dense.id.«nauty:doschreier»], PTree.get x e = none)
    {btc : block} (htl : PTree.get dense.id.tcell le = some (.Vptr btc Ptrofs.zero))
    {tw : Nat → Lib.Integers.int64} (htw : ArrayAt m .Mint64 btc 0 (longs tw) S.M)
    {cell : VSet n} (hrep : SetRep (fun w => bv64 (tw w)) S.M cell)
    (hbS : btc ∉ S.blocksG D gl cl) (hbW : ¬ IsWorkG D m btc)
    {v v1 : Nat} (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v)))
    (htv1 : PTree.get dense.id.«tv1» le = some (.Vint (ir v1))) (hv : v < n) (hv1 : v1 < n)
    (hQ : ∀ m' (tw' : Nat → Lib.Integers.int64), SearchAtG D m' S gl cl G st pre nsp →
      ArrayAt m' .Mint64 btc 0 (longs tw') S.M →
      SetRep (fun w => bv64 (tw' w)) S.M
        (if v == v1 then longprune cell st.fixedpts st.autos else cell) →
      Unch m m' (fun z => z = btc) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Alloc.Keep m m' btc → Q.normal E0 e le m') :
    Wp xi ge f longIf Q e le m := by
  have hnl := h.nlt
  have hM1 := h.M1
  have hMl := h.Mlt
  simp only [List.forall_mem_cons] at hge
  obtain ⟨g1, g2, g3, g4, g5, g6, -⟩ := hge
  apply wp_if_eval
  simp only [Exec.evalExpr, htv, htv1, typeof, cop]
  rw [ir_eq ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hvv : v = v1
  · subst hvv
    simp only [decide_true, ite_true]
    wp_step; wp_step; wp_step
    obtain ⟨ww, hww, hpairs⟩ := h.arrays.autos.pairs
    have hsz := h.arrays.autos.size
    obtain ⟨fw, hf, hfr⟩ := h.arrays.fixedpts
    have hfits := hww.fits
    have hb0 := hww.base_nonneg
    have hlen : (S.M + S.M) * st.autos.toList.length ≤ 2 * wsPairs * S.M := by
      simp only [Array.length_toList]
      have := Nat.mul_le_mul_left (S.M + S.M) hsz
      rw [show 2 * wsPairs * S.M = (S.M + S.M) * wsPairs by
        rw [Nat.mul_comm 2, Nat.mul_assoc, Nat.mul_comm wsPairs, ← Nat.two_mul]]
      exact this
    have hbot : ptrTo S.wb 8 0 = S.wofs := by
      simp only [ptrTo, Int.natCast_zero, Int.mul_zero, Int.add_zero, SLoc.wb, zOfInt_intOfZ]
      exact Ptrofs.repr_unsigned_proof _
    have htop : Ptrofs.repr (zOfInt (S.wb + 8 * (2 * (S.M : Int) * (st.autos.size : Int)))) =
        ptrTo S.wb 8 (0 + (S.M + S.M) * st.autos.toList.length) := by
      simp only [ptrTo, Array.length_toList, Nat.zero_add, show S.M + S.M = 2 * S.M by omega]
      push_cast; rfl
    have hfm := h.arrays.autos.fmptr
    refine wp_call (vf := .Vptr E.longpruneFn Ptrofs.zero)
      (targs := [tptr tulong, tptr tulong, tptr tulong, tptr tulong, tint])
      (tres := .Tvoid) (cc := Common.AST.cc_default) (.Internal dense.fn.longprune) _
      (Prune.Long.longprune_satisfies btc Ptrofs.zero S.bF Ptrofs.zero S.bws S.wb ww
        (2 * wsPairs * S.M) S.M 0 fw tw st.fixedpts cell st.autos.toList).grow rfl ?_ ?_
      (by simp [Common.Globalenvs.Genv.find_funct, E.funct_longpruneFn]) rfl
      ⟨by rw [hbot, ← htop], htw, hf, hww, hrep, hfr, hpairs,
        fun he => hbS (he ▸ SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inl (by simp)))))),
        fun he => hbS (he ▸ SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inl (by simp)))))),
        hM1, by omega, Nat.mul_pos (by decide) hM1, by omega⟩ ?_
    · simp only [Exec.evalExpr, Exec.lvalOfVar, g1, E.find_longpruneFn, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode]
    · have hF1 := h.dyns.fixedpts.ptr (by have := h.dyns.capF; omega)
      simp only [Exec.evalExprlist, Exec.evalExpr, htl, Exec.lvalOfVar, g2, g3, g4, g5,
        E.find_nautyFixedpts, E.find_workspace, E.find_fmptr, E.find_m, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode, Mem.loadv, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
        hF1, h.fixed.workspace.load, hfm.load, h.fixed.mm.load, typeof, cop, Alloc.Mptr_eq]
    rintro t _ m₂ ⟨⟨rfl, tw', harr₂, hr₂, hu₂, hka₂⟩, hg₂⟩
    have h₂ := h.unch hu₂ (fun z hz he => hbS (he ▸ hz)) (fun z hz he => hbW (he ▸ hz)) hg₂
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    apply wp_if_eval
    rw [eval_gint g6 E.find_doschreier h₂.fixed.doschreier]
    simp only [typeof, cop]
    rw [ite_eq_right (by decide)]
    apply wp_skip
    refine hQ m₂ tw' h₂ harr₂ ?_ hu₂ hg₂ (hka₂ btc)
    simpa using hr₂
  · simp only [Int.ofNat_inj, hvv, decide_false, Bool.false_eq_true, ite_false]
    apply wp_skip
    have : (v == v1) = false := by simpa using hvv
    exact hQ m tw h htw (by rw [this]; exact hrep) (Unch.refl _ _) (fun _ h => h) (Alloc.Keep.refl _ _)

end Generic

theorem wp_nodeLong {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    (h : SearchAt m S ctx st pre nsp)
    (hge : ∀ x ∈ [dense.id.«longprune», dense.id.«nauty:fixedpts», dense.id.«nauty:workspace»,
      dense.id.«nauty:fmptr», dense.id.«nauty:m», dense.id.«nauty:doschreier»], PTree.get x e = none)
    {btc : block} (htl : PTree.get dense.id.tcell le = some (.Vptr btc Ptrofs.zero))
    {tw : Nat → Lib.Integers.int64} (htw : ArrayAt m .Mint64 btc 0 (longs tw) S.M)
    {cell : VSet n} (hrep : SetRep (fun w => bv64 (tw w)) S.M cell)
    (hbS : btc ∉ S.blocks) (hbW : ¬ IsWork m btc)
    {v v1 : Nat} (htv : PTree.get dense.id.«tv» le = some (.Vint (ir v)))
    (htv1 : PTree.get dense.id.«tv1» le = some (.Vint (ir v1))) (hv : v < n) (hv1 : v1 < n)
    (hQ : ∀ m' (tw' : Nat → Lib.Integers.int64), SearchAt m' S ctx st pre nsp →
      ArrayAt m' .Mint64 btc 0 (longs tw') S.M →
      SetRep (fun w => bv64 (tw' w)) S.M
        (if v == v1 then longprune cell st.fixedpts st.autos else cell) →
      Unch m m' (fun z => z = btc) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Alloc.Keep m m' btc → Q.normal E0 e le m') :
    Wp xi ge f longIf Q e le m :=
  wp_nodeLongG h.toG hge htl htw hrep (fun e => hbS (SLoc.mem_blocksG.1 e))
    (fun e => hbW (isWork_dense.1 e)) htv htv1 hv hv1 fun m' tw' h' ha hr hu hg hk =>
    hQ m' tw' (h'.dense h.gw) ha hr hu hg hk

end NautyVerified.Proofs.Search

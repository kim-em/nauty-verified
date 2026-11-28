import NautyVerified.Proofs.Search.Processnode.PushPtn

/-!
# Recording an automorphism's pair

`wp_pushPerm`: `if (fmptr == worktop) fmptr -= 2*m; fmperm(workperm, fmptr,
fmptr + m, m, n); fmptr += 2*m;` with `workperm` holding the permutation `w` is
`pushAuto st (fmperm w n)`; `workperm` still holds `w`.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk longs)
open NautyVerified.Proofs.Alloc (Keep DynAt)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}
variable {n : Nat} {D : DispatchC ge O} {m₀ m₁ m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc}
  {G : O.Gr n} {e : env} {bsr : block} {st : SearchState n (O.Canon n)} {nsp : Bool}

abbrev fmpermCall : statement :=
  .Scall none
    (.Evar dense.id.«fmperm» (tfun [(tptr tint), (tptr tulong), (tptr tulong), tint, tint] .Tvoid))
    [(.Evar dense.id.«nauty:workperm» (tptr tint)),
     (.Evar dense.id.«nauty:fmptr» (tptr tulong)),
     (.Ebinop .Oadd (.Evar dense.id.«nauty:fmptr» (tptr tulong)) (.Evar dense.id.«nauty:m» tint)
       (tptr tulong)),
     (.Evar dense.id.«nauty:m» tint),
     (.Evar dense.id.«nauty:n» tint)]

kernel_rfl type_fmpermG : type_of_fundef (.Internal dense.fn.«fmperm») =
  tfun [tptr tint, tptr tulong, tptr tulong, tint, tint] .Tvoid

set_option maxHeartbeats 8000000 in
theorem wp_pushPerm {f : function} {Q : Post} {le : temp_env} {w : Array Nat} {rest : statement}
    (c : PCtx D m₀ m₁ S gl cl e bsr) (h : PAt D m₀ m₁ m S gl cl G bsr st nsp)
    (hw : ArrayAt m .Mint32 S.bWP 0 (ints w) n) (hwsz : w.size = n) (hws : ∀ i < n, w[i]! < n)
    (hwi : ∀ x y, x < n → y < n → w[x]! = w[y]! → x = y)
    (hQ : ∀ m', PAt D m₀ m₁ m' S gl cl G bsr (pushAuto st (Hex.GraphIso.Nauty.fmperm w n)) nsp →
      ArrayAt m' .Mint32 S.bWP 0 (ints w) n →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Wp xi ge f rest Q e le m') :
    Wp xi ge f (.Ssequence wrapC (.Ssequence (sk fmpermCall) (.Ssequence (sk advanceC) rest))) Q e le m := by
  have hs := h.search
  have hd := hs.lit
  have hinv := hs.inv
  have hM := hs.M1
  have hMl := hs.Mlt
  have hn0 := hs.n0
  have hnl := hs.nlt
  have hvm := h.valid c
  rw [pushAuto_eq _ _ hinv.wsCap] at hQ
  obtain ⟨ww, hws0, hrep⟩ := hs.arrays.autos.arr
  have hsz := hs.arrays.autos.size
  obtain ⟨cN, bN, dN, nN, -⟩ := hs.work.nautil
  have hcWP : 0 < S.capWP := by have := hs.dyns.capWP; omega
  generalize hk : slotOf st.autos.size = k
  have hk1 : k + 1 ≤ wsPairs := by
    rw [← hk]; unfold slotOf; by_cases hh : st.autos.size = wsPairs
    · rw [if_pos hh]; decide
    · rw [if_neg hh]; omega
  have hle : 2 * S.M * k + S.M + S.M ≤ 2 * wsPairs * S.M := by
    have h1 := Nat.mul_le_mul_left (2 * S.M) hk1
    rw [Nat.mul_succ] at h1; rw [wsT]; omega
  have mB : ∀ {z}, z ∈ S.litG → z ∈ S.blocksG D.toDispatchRep gl cl := fun hz => SLoc.mem_blocksG_lit hz
  wp_step
  refine wp_wrap hs (c.eg _ (by decide)) (c.eg _ (by decide)) (c.eg _ (by decide)) ?_
  intro m1 hp1 hu1 hv1
  rw [hk] at hp1
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  have hws1 := hws0.unch hu1 (by sep_ne hd)
  have hf0 := Prune.Long.slice_at hws1 (2 * S.M * k) S.M (by omega)
  have hm0 := Prune.Long.slice_at hws1 (2 * S.M * k + S.M) S.M (by omega)
  have hfit := hws0.fits
  have hbase := hws0.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hfit
  have hle' : ((2 * S.M * k + S.M + S.M : Nat) : Int) ≤ ((2 * wsPairs * S.M : Nat) : Int) :=
    Int.ofNat_le.2 hle
  have uf : intOfZ (Ptrofs.unsigned (ptrTo S.wb 8 (2 * S.M * k))) = S.wb + 8 * (2 * S.M * k : Nat) :=
    unsigned_ptrTo (by omega) (by omega)
  have um : intOfZ (Ptrofs.unsigned (ptrTo S.wb 8 (2 * S.M * k + S.M))) =
      S.wb + 8 * (2 * S.M * k + S.M : Nat) :=
    unsigned_ptrTo (by omega) (by omega)
  have hbws : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, 0 < cN → z ≠ bN := fun z hz hc e => nN hc (e ▸ hz)
  have dN1 := dN.keep hu1 (by sep_ne hd) (by sep_ne hd) fun hc => Keep.unch hu1 (fun e =>
    nN hc (e ▸ mB (by simp [SLoc.litG])))
  refine wp_call (vf := .Vptr E.fmpermFn Ptrofs.zero)
    (targs := [tptr tint, tptr tulong, tptr tulong, tint, tint]) (tres := .Tvoid)
    (cc := cc_default) (vargs := [.Vptr S.bWP Ptrofs.zero,
      .Vptr S.bws (ptrTo S.wb 8 (2 * S.M * k)), .Vptr S.bws (ptrTo S.wb 8 (2 * S.M * k + S.M)),
      .Vint (ir S.M), .Vint (ir n)]) _ _
    (Satisfies.grow (Fmperm.fmperm_satisfies S.bWP Ptrofs.zero S.bws (ptrTo S.wb 8 (2 * S.M * k))
      S.bws (ptrTo S.wb 8 (2 * S.M * k + S.M)) w n S.M
      (fun i => ww (2 * S.M * k + i)) (fun i => ww (2 * S.M * k + S.M + i)) cN bN)) rfl ?_ ?_
    (by simp [Genv.find_funct, E.funct_fmpermFn]) type_fmpermG ?_ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, c.eg _ (by decide : dense.id.«fmperm» ≠ dense.id.sr),
      E.find_fmpermFn, Exec.derefLoc, access_mode]
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) E.find_nautyWorkperm rfl
        ⟨by rw [hu1.load _ _ _ (by sep_ne hd)]; exact hs.dyns.workperm.ptr hcWP,
          hu1.access _ _ _ _ (by sep_ne hd) hs.dyns.workperm.bpW⟩,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) E.find_fmptr rfl hp1,
      eval_mcr (c.eg _ (by decide)) (c.eg _ (by decide)) hp1 (hs.fixed.mm.unch hu1 (by sep_ne hd)) hMl,
      eval_gint (c.eg _ (by decide)) E.find_m (hs.fixed.mm.unch hu1 (by sep_ne hd)),
      eval_gint (c.eg _ (by decide)) E.find_n (hs.fixed.nn.unch hu1 (by sep_ne hd)), typeof, cop]
  · have vWP := hv1 _ (hvm S.bWP (mB (by simp [SLoc.litG])))
    have vws := hv1 _ (hvm S.bws (mB (by simp [SLoc.litG])))
    refine ⟨rfl, hw.unch hu1 (by sep_ne hd), hf0, hm0, hs.tables.env.nautilBit.unch hu1 (by sep_ne hd),
      dN1, vWP, vws, vws, .inr (.inl (by rw [uf, um]; omega)), by sep_ne hd, by sep_ne hd, ?_, ?_,
      hwsz, hws, hwi, by omega, hM, by omega, hs.nM⟩
    · rintro z (rfl | rfl | rfl) <;> exact ⟨by sep_ne hd, by sep_ne hd, by sep_ne hd⟩
    · intro hc
      exact ⟨(hbws _ (mB (by simp [SLoc.litG])) hc).symm, (hbws _ (mB (by simp [SLoc.litG])) hc).symm,
        (hbws _ (mB (by simp [SLoc.litG])) hc).symm, (hbws _ (mB (by simp [SLoc.litG])) hc).symm⟩
  · rintro t r m2 ⟨⟨rfl, wf', wm', cap', b', hf', hm', hrf, hrm, hD', hcap, hrel, hu2, hr2, hkeep⟩, hv2⟩
    simp only [set_opttemp, seqPost, Post.after, E0_append]
    have vf1 : Mem.valid_block m1 E.fmptr := hv1 _ (hvm _ (mB (by simp [SLoc.litG])))
    have W2 : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, z ≠ S.bws → z ≠ E.nautilWorkpermSz →
        z ≠ E.nautilWorkperm →
        ¬ (z = S.bws ∨ z = S.bws ∨ z = E.nautilWorkpermSz ∨ z = E.nautilWorkperm ∨
          (0 < cN ∧ z = bN) ∨ (¬ Mem.valid_block m1 b' ∧ z = b')) := by
      rintro z hz h1 h2 h3 (e | e | e | e | ⟨hc, e⟩ | ⟨hnv, e⟩)
      · exact h1 e
      · exact h1 e
      · exact h2 e
      · exact h3 e
      · exact hbws z hz hc e
      · exact hnv (e ▸ hv1 _ (hvm z hz))
    have hp2 := hp1.unch hu2 (W2 _ (mB (by simp [SLoc.litG])) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
    have hmm2 := (hs.fixed.mm.unch hu1 (by sep_ne hd)).unch hu2
      (W2 _ (mB (by simp [SLoc.litG])) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
    wp_step; wp_step; wp_step
    refine wp_gptrSet (c.eg _ (by decide)) E.find_fmptr hp2.writable
      (eval_advance (c.eg _ (by decide)) (c.eg _ (by decide)) hp2 hmm2 hMl) rfl ?_
    intro m3 hp3 hu3 hv3
    simp only [seqPost, Post.after, E0_append]
    have nb3 : ¬ S.bws = E.fmptr := by sep_ne hd
    have cf : S.wb + 8 * ((2 * S.M * k : Nat) : Int) = S.wb + 8 * (2 * S.M * k) := by push_cast; rfl
    have cm : S.wb + 8 * ((2 * S.M * k + S.M : Nat) : Int) = S.wb + 8 * (2 * S.M * k + S.M) := by
      push_cast; rfl
    rw [uf, cf] at hf' hr2
    rw [um, cm] at hm' hr2
    have hkws : Keep m m3 S.bws :=
      ((Keep.unch hu1 (by sep_ne hd)).trans (hkeep _ (by simp))).trans (Keep.unch hu3 nb3)
    have hA := AutosAtG.push (m' := m3) hs.arrays.autos hM (pair := Hex.GraphIso.Nauty.fmperm w n)
      (by rw [hk]; exact hf'.unch hu3 nb3) (by rw [hk]; exact hm'.unch hu3 nb3) hrf hrm
      (by rw [hk]; exact ((Rest.unch hu1 (by sep_ne hd)).trans hr2).trans (Rest.unch hu3 nb3))
      hkws
      (by rw [hk]; exact hp3)
    let W := fun z => z = E.fmptr ∨ (z = S.bws ∨ z = S.bws ∨ z = E.nautilWorkpermSz ∨
      z = E.nautilWorkperm ∨ (0 < cN ∧ z = bN) ∨ (¬ Mem.valid_block m1 b' ∧ z = b'))
    have hu : Unch m m3 W :=
      ((hu1.mono fun z hz => .inl hz).trans (hu2.mono fun z hz => .inr hz)).trans
        (hu3.mono fun z hz => .inl hz)
    have hv : ∀ z, Mem.valid_block m z → Mem.valid_block m3 z := fun z hz => hv3 _ (hv2 _ (hv1 _ hz))
    have notW : ∀ z ∈ S.blocksG D.toDispatchRep gl cl,
        ¬ z ∈ [E.fmptr, S.bws, E.nautilWorkpermSz, E.nautilWorkperm] → ¬ W z := by
      intro z hz hn
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
      rintro (e | e)
      · exact hn.1 e
      · exact W2 z hz hn.2.1 hn.2.2.1 hn.2.2.2 e
    have nf3 : ¬ b' = E.fmptr := fun e => by
      rcases hrel with ⟨hcc, rfl⟩ | hnv
      · exact nN (by omega) (e ▸ mB (by simp [SLoc.litG]))
      · exact hnv (e ▸ vf1)
    have dN3 := hD'.keep hu3 (by sep_ne hd) (by sep_ne hd) fun _ => Keep.unch hu3 nf3
    have rel' : (cap' = cN ∧ b' = bN) ∨ ¬ Mem.valid_block m b' := by
      rcases hrel with h' | h'
      · exact .inl h'
      · exact .inr fun hv' => h' (hv1 _ hv')
    have hsrW : ¬ W bsr := fun hW' => by
      rcases hW' with e | e | e | e | e | ⟨hc, e⟩ | ⟨hnv, e⟩
      · exact c.ne_blocks (mB (by simp [SLoc.litG])) e.symm
      · exact c.ne_blocks (mB (by simp [SLoc.litG])) e.symm
      · exact c.ne_blocks (mB (by simp [SLoc.litG])) e.symm
      · exact c.ne_blocks (mB (by simp [SLoc.litG])) e.symm
      · exact c.ne_blocks (mB (by simp [SLoc.litG])) e.symm
      · exact h.work_ne c (.inr ⟨cN, hc, dN⟩) e.symm
      · exact hnv (e ▸ hv1 _ (h.grow1 _ c.valid1))
    have nS : ∀ z ∈ (scalarBlocks : List block), ¬ W z := fun z hz =>
      notW z (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl (by revert z; simp)))))))
        ((by sep_all hd : ∀ y ∈ (scalarBlocks : List block),
          ¬ y ∈ [E.fmptr, S.bws, E.nautilWorkpermSz, E.nautilWorkperm]) z hz)
    refine hQ m3 (PAt.nautil (L := [E.fmptr, S.bws]) c h (by simp) dN hu ?_ hv ?_ dN3 rel'
      ((hs.scalars.unch hu nS).cast rfl)
      ((hs.stats.unch hu (notW _ (mB (by simp [SLoc.litG])) (by sep_notin hd))).cast rfl)
      (hs.arrays.setAutos hu
        (fun z hz => notW z (by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
            rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              exact mB (by simp [SLoc.litG]))
          ((by sep_all hd : ∀ y ∈ [S.bl, S.bp, S.bo, S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC,
            S.bTC], ¬ y ∈ [E.fmptr, S.bws, E.nautilWorkpermSz, E.nautilWorkperm]) z hz))
        (fun z hz => notW z (SLoc.mem_blocksG_of _ (.inl hz)) (hs.graph_notin (by simp) z hz))
        (fun z hz => notW z (SLoc.mem_blocksG_of _ (.inr (.inr (.inl hz))))
          (hs.canon_notin (by simp) z hz)) hA)
      { hinv with }) (hw.unch hu (notW _ (mB (by simp [SLoc.litG])) (by sep_notin hd)))
      fun v hv' => hv'.unch hu hsrW
    · rintro z (rfl | rfl | rfl | rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩)
      · exact .inl (by simp)
      · exact .inl (by simp)
      · exact .inl (by simp)
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inr (.inl ⟨hc, rfl⟩)))
      · exact .inr (.inr (.inr (.inr fun hv' => hnv (hv1 _ hv'))))
    · intro z hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact hkws
        | exact Keep.unch hu (notW _ (mB (by simp [SLoc.litG])) (by sep_notin hd))

end NautyVerified.Proofs.Search.Processnode

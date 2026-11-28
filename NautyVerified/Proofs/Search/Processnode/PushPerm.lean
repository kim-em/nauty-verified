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
variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

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
theorem wp_pushPerm {f : function} {Q : Post} {le : temp_env} {w : Array Nat}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hw : ArrayAt m .Mint32 S.bWP 0 (ints w) n) (hwsz : w.size = n) (hws : ∀ i < n, w[i]! < n)
    (hwi : ∀ x y, x < n → y < n → w[x]! = w[y]! → x = y)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr (pushAuto st (Hex.GraphIso.Nauty.fmperm w n)) nsp →
      ArrayAt m' .Mint32 S.bWP 0 (ints w) n →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Q.normal E0 e le m') :
    Wp xi ge f (.Ssequence wrapC (.Ssequence (sk fmpermCall) (sk advanceC))) Q e le m := by
  have hs := h.search
  have hd := hs.distinct
  have hinv := hs.inv
  have hM := hs.M1
  have hMl := hs.Mlt
  have hn0 := hs.n0
  have hnl := hs.nlt
  have hvm : ∀ z ∈ S.blocks, Mem.valid_block m z := fun z hz => h.frame.2 _ (c.valid0 z hz)
  rw [pushAuto_eq _ _ hinv.wsCap] at hQ
  obtain ⟨ww, hws0, hrep⟩ := hs.arrays.autos.arr
  have hsz := hs.arrays.autos.size
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := hs.work.arr
  have hcWP : 0 < S.capWP := by have := hs.dyns.capWP; omega
  generalize hk : slotOf st.autos.size = k
  have hk1 : k + 1 ≤ wsPairs := by
    rw [← hk]; unfold slotOf; by_cases hh : st.autos.size = wsPairs
    · rw [if_pos hh]; decide
    · rw [if_neg hh]; omega
  have hle : 2 * S.M * k + S.M + S.M ≤ 2 * wsPairs * S.M := by
    have h1 := Nat.mul_le_mul_left (2 * S.M) hk1
    rw [Nat.mul_succ] at h1; rw [wsT]; omega
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
  have nW1 : ∀ z, z ≠ Block.fmptr → ¬ z = Block.fmptr := fun z h => h
  have dN1 := dN.keep hu1 (by sep_ne hd) (by sep_ne hd) fun hc => Keep.unch hu1 (fun e =>
    nN hc (e ▸ by simp [SLoc.blocks]))
  have hbws : ∀ z ∈ S.blocks, 0 < cN → z ≠ bN := fun z hz hc e => nN hc (e ▸ hz)
  refine wp_call (vf := .Vptr Block.fmpermFn Ptrofs.zero)
    (targs := [tptr tint, tptr tulong, tptr tulong, tint, tint]) (tres := .Tvoid)
    (cc := cc_default) (vargs := [.Vptr S.bWP Ptrofs.zero,
      .Vptr S.bws (ptrTo S.wb 8 (2 * S.M * k)), .Vptr S.bws (ptrTo S.wb 8 (2 * S.M * k + S.M)),
      .Vint (ir S.M), .Vint (ir n)]) _ _
    (Satisfies.grow (Fmperm.fmperm_satisfies S.bWP Ptrofs.zero S.bws (ptrTo S.wb 8 (2 * S.M * k))
      S.bws (ptrTo S.wb 8 (2 * S.M * k + S.M)) w n S.M
      (fun i => ww (2 * S.M * k + i)) (fun i => ww (2 * S.M * k + S.M + i)) cN bN)) rfl ?_ ?_
    (by simp [Genv.find_funct, funct_fmpermFn]) type_fmpermG ?_ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, c.eg _ (by decide : dense.id.«fmperm» ≠ dense.id.sr),
      find_fmpermFn, Exec.derefLoc, access_mode]
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) find_nautyWorkperm rfl
        ⟨by rw [hu1.load _ _ _ (by sep_ne hd)]; exact hs.dyns.workperm.ptr hcWP,
          hu1.access _ _ _ _ (by sep_ne hd) hs.dyns.workperm.bpW⟩,
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) find_fmptr rfl hp1,
      eval_mcr (c.eg _ (by decide)) (c.eg _ (by decide)) hp1 (hs.fixed.mm.unch hu1 (by sep_ne hd)) hMl,
      eval_gint (c.eg _ (by decide)) find_m (hs.fixed.mm.unch hu1 (by sep_ne hd)),
      eval_gint (c.eg _ (by decide)) find_n (hs.fixed.nn.unch hu1 (by sep_ne hd)), typeof, cop]
  · have vWP := hv1 _ (hvm S.bWP (by simp [SLoc.blocks]))
    have vws := hv1 _ (hvm S.bws (by simp [SLoc.blocks]))
    refine ⟨rfl, hw.unch hu1 (by sep_ne hd), hf0, hm0, hs.tables.nautilBit.unch hu1 (by sep_ne hd),
      dN1, vWP, vws, vws, .inr (.inl (by rw [uf, um]; omega)), by sep_ne hd, by sep_ne hd, ?_, ?_,
      hwsz, hws, hwi, by omega, hM, by omega, hs.nM⟩
    · rintro z (rfl | rfl | rfl) <;> exact ⟨by sep_ne hd, by sep_ne hd, by sep_ne hd⟩
    · intro hc
      exact ⟨(hbws _ (by simp [SLoc.blocks]) hc).symm, (hbws _ (by simp [SLoc.blocks]) hc).symm,
        (hbws _ (by simp [SLoc.blocks]) hc).symm, (hbws _ (by simp [SLoc.blocks]) hc).symm⟩
  · rintro t r m2 ⟨⟨rfl, wf', wm', cap', b', hf', hm', hrf, hrm, hD', hcap, hrel, hu2, hr2, hkeep⟩, hv2⟩
    simp only [set_opttemp, seqPost, Post.after, E0_append]
    have vf1 : Mem.valid_block m1 Block.fmptr := hv1 _ (hvm _ (by simp [SLoc.blocks]))
    have nb' : ∀ z, Mem.valid_block m1 z → ¬ (¬ Mem.valid_block m1 b' ∧ z = b') :=
      fun z hz ⟨hnv, e⟩ => hnv (e ▸ hz)
    have W2 : ∀ z ∈ S.blocks, z ≠ S.bws → z ≠ Block.nautilWorkpermSz → z ≠ Block.nautilWorkperm →
        ¬ (z = S.bws ∨ z = S.bws ∨ z = Block.nautilWorkpermSz ∨ z = Block.nautilWorkperm ∨
          (0 < cN ∧ z = bN) ∨ (¬ Mem.valid_block m1 b' ∧ z = b')) := by
      rintro z hz h1 h2 h3 (e | e | e | e | ⟨hc, e⟩ | e)
      · exact h1 e
      · exact h1 e
      · exact h2 e
      · exact h3 e
      · exact hbws z hz hc e
      · exact nb' z (hv1 _ (hvm z hz)) e
    have hp2 := hp1.unch hu2 (W2 _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
    have hmm2 := (hs.fixed.mm.unch hu1 (by sep_ne hd)).unch hu2
      (W2 _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))
    wp_step; wp_step
    refine wp_gptrSet (c.eg _ (by decide)) find_fmptr hp2.writable
      (eval_advance (c.eg _ (by decide)) (c.eg _ (by decide)) hp2 hmm2 hMl) rfl ?_
    intro m3 hp3 hu3 hv3
    have nb3 : ¬ S.bws = Block.fmptr := by sep_ne hd
    have cf : S.wb + 8 * ((2 * S.M * k : Nat) : Int) = S.wb + 8 * (2 * S.M * k) := by push_cast; rfl
    have cm : S.wb + 8 * ((2 * S.M * k + S.M : Nat) : Int) = S.wb + 8 * (2 * S.M * k + S.M) := by
      push_cast; rfl
    rw [uf, cf] at hf' hr2
    rw [um, cm] at hm' hr2
    have hA := AutosAt.push (m' := m3) hs.arrays.autos hM (pair := Hex.GraphIso.Nauty.fmperm w n)
      (by rw [hk]; exact hf'.unch hu3 nb3) (by rw [hk]; exact hm'.unch hu3 nb3) hrf hrm
      (by rw [hk]; exact ((Rest.unch hu1 (by sep_ne hd)).trans hr2).trans (Rest.unch hu3 nb3))
      (((Keep.unch hu1 (by sep_ne hd)).trans (hkeep _ (by simp))).trans (Keep.unch hu3 nb3))
      (by rw [hk]; exact hp3)
    let W := fun z => z = Block.fmptr ∨ (z = S.bws ∨ z = S.bws ∨ z = Block.nautilWorkpermSz ∨
      z = Block.nautilWorkperm ∨ (0 < cN ∧ z = bN) ∨ (¬ Mem.valid_block m1 b' ∧ z = b'))
    have hu : Unch m m3 W :=
      ((hu1.mono fun z hz => .inl hz).trans (hu2.mono fun z hz => .inr hz)).trans
        (hu3.mono fun z hz => .inl hz)
    have hv : ∀ z, Mem.valid_block m z → Mem.valid_block m3 z := fun z hz => hv3 _ (hv2 _ (hv1 _ hz))
    have notW : ∀ z ∈ S.blocks, z ≠ Block.fmptr → z ≠ S.bws → z ≠ Block.nautilWorkpermSz →
        z ≠ Block.nautilWorkperm → ¬ W z := by
      rintro z hz h0 h1 h2 h3 (e | e)
      · exact h0 e
      · exact W2 z hz h1 h2 h3 e
    have nf3 : ¬ b' = Block.fmptr := fun e => by
      rcases hrel with ⟨hcc, rfl⟩ | hnv
      · exact nN (by omega) (e ▸ by simp [SLoc.blocks])
      · exact hnv (e ▸ vf1)
    have dN3 := hD'.keep hu3 (by sep_ne hd) (by sep_ne hd) fun _ => Keep.unch hu3 nf3
    have rel' : (cap' = cN ∧ b' = bN) ∨ ¬ Mem.valid_block m b' := by
      rcases hrel with h' | h'
      · exact .inl h'
      · exact .inr fun hv' => h' (hv1 _ hv')
    have hWa : ∀ z, W z → (z ∈ S.blocks ∧ z ∉ [Block.naugraphWorkperm, Block.naugraphWorkpermSz,
        Block.naugraphWorkset, Block.naugraphWorksetSz, Block.naugraphBucket,
        Block.naugraphBucketSz]) ∨ (0 < cN ∧ z = bN) ∨ (z ∉ S.blocks ∧ ¬ IsWork m z) := by
      rintro z (rfl | rfl | rfl | rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩)
      · exact .inl ⟨by simp [SLoc.blocks], by decide⟩
      · exact .inl ⟨by simp [SLoc.blocks], by sep_notin hd⟩
      · exact .inl ⟨by simp [SLoc.blocks], by sep_notin hd⟩
      · exact .inl ⟨by simp [SLoc.blocks], by decide⟩
      · exact .inl ⟨by simp [SLoc.blocks], by decide⟩
      · exact .inr (.inl ⟨hc, rfl⟩)
      · exact .inr (.inr ⟨fun hz => hnv (hv1 _ (hvm _ hz)), fun hw' => hnv (hv1 _ hw'.valid)⟩)
    obtain ⟨hwm, hwk⟩ := SearchAt.afterN hs hvm dN hu hWa dN3 rel'
    have hsrW : ¬ W bsr := by
      rintro (e | e | e | e | e | ⟨hc, e⟩ | ⟨hnv, e⟩)
      · exact c.ne_blocks (by simp [SLoc.blocks]) e.symm
      · exact c.ne_blocks (by simp [SLoc.blocks]) e.symm
      · exact c.ne_blocks (by simp [SLoc.blocks]) e.symm
      · exact c.ne_blocks (by simp [SLoc.blocks]) e.symm
      · exact c.ne_blocks (by simp [SLoc.blocks]) e.symm
      · exact h.work_ne c (.inr (.inr (.inr ⟨cN, hc, dN⟩))) e.symm
      · exact hnv (e ▸ hv1 _ (h.grow1 _ c.valid1))
    refine hQ m3 (PAt.call c h hu ?_ ?_ hv hwm hwk
      ((hs.scalars.unch hu (by all_notW4 hd, notW)).cast rfl)
      ((hs.stats.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))).cast rfl)
      (hs.arrays.set hu (hs.arrays.lab.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))) (hs.arrays.ptn.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
        (hs.arrays.orbits.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))) (hs.arrays.active' hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
        (hs.arrays.fixedpts' hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))) (hs.arrays.workperm' hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
        (hs.arrays.firstlab.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))) (hs.arrays.canonlab.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
        (hs.arrays.firstcode.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))) (hs.arrays.canoncode.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
        (hs.arrays.firsttc.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))) (hs.arrays.canong.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
        hA (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
      { hinv with } (hu.access _ _ _ _ hsrW h.srW)) (hw.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd)))
      fun v hv' => hv'.unch hu hsrW
    · rintro z (rfl | rfl | rfl | rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩)
      · exact .inl (by simp [SLoc.wr, wrG, SLoc.wrV])
      · exact .inl (by simp [SLoc.wr, wrG, SLoc.wrV])
      · exact .inl (by simp [SLoc.wr, wrG, SLoc.wrV])
      · exact .inr (.inl (by decide))
      · exact .inr (.inl (by decide))
      · exact .inr (.inr (.inl (.inr (.inr (.inr ⟨cN, hc, dN⟩)))))
      · exact .inr (.inr (.inr (.inl fun hv' => hnv (hv1 _ hv'))))
    · intro z hz
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Keep.unch hu (notW _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) (by sep_ne hd))

end NautyVerified.Proofs.Search.Processnode

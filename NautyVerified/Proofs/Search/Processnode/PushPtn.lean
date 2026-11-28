import NautyVerified.Proofs.Search.Processnode.Push

/-!
# Recording the partition's pair

`wp_pushPtn`: `if (fmptr == worktop) fmptr -= 2*m; fmptn(lab, ptn, noncheaplevel,
fmptr, fmptr + m, m, n); fmptr += 2*m;` is `pushAuto st (fmptn lab ptn noncheaplevel n)`.
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
open NautyVerified.Proofs.Alloc (Keep)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

/-- `fmptr += 2 * m`. -/
abbrev advanceC : statement :=
  .Sassign (.Evar dense.id.«nauty:fmptr» (tptr tulong))
    (.Ebinop .Oadd (.Evar dense.id.«nauty:fmptr» (tptr tulong))
      (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint) (tptr tulong))

abbrev wrapC : statement :=
  Set.sk (.Sifthenelse
    (.Ebinop .Oeq (.Evar dense.id.«nauty:fmptr» (tptr tulong))
      (.Evar dense.id.«nauty:worktop» (tptr tulong)) tint)
    (Set.sk (.Sassign (.Evar dense.id.«nauty:fmptr» (tptr tulong))
      (.Ebinop .Osub (.Evar dense.id.«nauty:fmptr» (tptr tulong))
        (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint) (tptr tulong))))
    .Sskip)

abbrev fmptnCall : statement :=
  .Scall none
    (.Evar dense.id.«fmptn»
      (tfun [(tptr tint), (tptr tint), tint, (tptr tulong), (tptr tulong), tint, tint] .Tvoid))
    [(.Etempvar dense.id.lab (tptr tint)),
     (.Etempvar dense.id.ptn (tptr tint)),
     (.Evar dense.id.«nauty:noncheaplevel» tint),
     (.Evar dense.id.«nauty:fmptr» (tptr tulong)),
     (.Ebinop .Oadd (.Evar dense.id.«nauty:fmptr» (tptr tulong)) (.Evar dense.id.«nauty:m» tint)
       (tptr tulong)),
     (.Evar dense.id.«nauty:m» tint),
     (.Evar dense.id.«nauty:n» tint)]

theorem eval_advance {e : env} {le : temp_env} {m : mem} {S : SLoc} {k : Nat}
    (he1 : PTree.get dense.id.«nauty:fmptr» e = none) (he2 : PTree.get dense.id.«nauty:m» e = none)
    (hp : PtrAt m Block.fmptr (.Vptr S.bws (ptrTo S.wb 8 (2 * S.M * k))))
    (hm : IntAt m Block.m S.M) (hM : S.M < 33554432) :
    Exec.evalExpr ge e le m (.Ebinop .Oadd (.Evar dense.id.«nauty:fmptr» (tptr tulong))
      (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint) (tptr tulong)) =
      some (.Vptr S.bws (ptrTo S.wb 8 (2 * S.M * (k + 1)))) := by
  rw [Exec.evalExpr, eval_gptr he1 find_fmptr rfl hp, Exec.evalExpr, eval_ci, eval_gint he2 find_m hm]
  simp only [typeof, cop, ir_mul]
  rw [show (2 : Int) * (S.M : Int) = ((2 * S.M : Nat) : Int) by push_cast; rfl,
    Prune.Long.add_ptrTo8 _ _ _ _ (by omega), Nat.mul_succ]

theorem eval_mcr {e : env} {le : temp_env} {m : mem} {S : SLoc} {k : Nat}
    (he1 : PTree.get dense.id.«nauty:fmptr» e = none) (he2 : PTree.get dense.id.«nauty:m» e = none)
    (hp : PtrAt m Block.fmptr (.Vptr S.bws (ptrTo S.wb 8 (2 * S.M * k))))
    (hm : IntAt m Block.m S.M) (hM : S.M < 33554432) :
    Exec.evalExpr ge e le m (.Ebinop .Oadd (.Evar dense.id.«nauty:fmptr» (tptr tulong))
      (.Evar dense.id.«nauty:m» tint) (tptr tulong)) =
      some (.Vptr S.bws (ptrTo S.wb 8 (2 * S.M * k + S.M))) := by
  rw [Exec.evalExpr, eval_gptr he1 find_fmptr rfl hp, eval_gint he2 find_m hm]
  simp only [typeof, cop]
  rw [Prune.Long.add_ptrTo8 _ _ _ _ (by omega)]

kernel_rfl type_fmptnG : type_of_fundef (.Internal dense.fn.«fmptn») =
  tfun [tptr tint, tptr tint, tint, tptr tulong, tptr tulong, tint, tint] .Tvoid

set_option maxHeartbeats 4000000 in
theorem wp_pushPtn {f : function} {Q : Post} {le : temp_env} (c : PCtx m₀ m₁ S e bsr)
    (h : PAt m₀ m₁ m S ctx bsr st nsp) (hnc : 1 ≤ st.noncheaplevel)
    (hlab : PTree.get dense.id.lab le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs))
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr (pushAuto st (fmptn st.lab st.ptn st.noncheaplevel n)) nsp →
      (∀ v, SrAt m bsr v → SrAt m' bsr v) → Q.normal E0 e le m') :
    Wp xi ge f (.Ssequence wrapC (.Ssequence (sk fmptnCall) (sk advanceC))) Q e le m := by
  have hs := h.search
  have hd := hs.distinct
  have hinv := hs.inv
  have hM := hs.M1
  have hMl := hs.Mlt
  have hn0 := hs.n0
  have hnl := hs.nlt
  obtain ⟨-, -, a3, -, -, -, -, -, -, -, -, -⟩ := hinv.scalars
  rw [pushAuto_eq _ _ hinv.wsCap] at hQ
  obtain ⟨ww, hws, hrep⟩ := hs.arrays.autos.arr
  have hsz := hs.arrays.autos.size
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
  have hws1 := hws.unch hu1 (by sep_ne hd)
  have hf0 := Prune.Long.slice_at hws1 (2 * S.M * k) S.M (by omega)
  have hm0 := Prune.Long.slice_at hws1 (2 * S.M * k + S.M) S.M (by omega)
  have hfit := hws.fits
  have hbase := hws.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hfit
  have hle' : ((2 * S.M * k + S.M + S.M : Nat) : Int) ≤ ((2 * wsPairs * S.M : Nat) : Int) :=
    Int.ofNat_le.2 hle
  have uf : intOfZ (Ptrofs.unsigned (ptrTo S.wb 8 (2 * S.M * k))) = S.wb + 8 * (2 * S.M * k : Nat) :=
    unsigned_ptrTo (by omega) (by omega)
  have um : intOfZ (Ptrofs.unsigned (ptrTo S.wb 8 (2 * S.M * k + S.M))) =
      S.wb + 8 * (2 * S.M * k + S.M : Nat) :=
    unsigned_ptrTo (by omega) (by omega)
  refine wp_call (vf := .Vptr Block.fmptnFn Ptrofs.zero)
    (targs := [tptr tint, tptr tint, tint, tptr tulong, tptr tulong, tint, tint]) (tres := .Tvoid)
    (cc := cc_default) (vargs := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir st.noncheaplevel),
      .Vptr S.bws (ptrTo S.wb 8 (2 * S.M * k)), .Vptr S.bws (ptrTo S.wb 8 (2 * S.M * k + S.M)),
      .Vint (ir S.M), .Vint (ir n)]) _ _
    (Satisfies.grow (Fmptn.fmptn_satisfies S.bl S.lofs S.bp S.pofs S.bws (ptrTo S.wb 8 (2 * S.M * k))
      S.bws (ptrTo S.wb 8 (2 * S.M * k + S.M)) st.lab st.ptn n st.noncheaplevel S.M
      (fun i => ww (2 * S.M * k + i)) (fun i => ww (2 * S.M * k + S.M + i)))) rfl ?_ ?_
    (by simp [Genv.find_funct, funct_fmptnFn]) type_fmptnG ?_ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, c.eg _ (by decide : dense.id.«fmptn» ≠ dense.id.sr),
      find_fmptnFn, Exec.derefLoc, access_mode]
  · have e1 : Exec.evalExpr ge e le m1 (.Etempvar dense.id.lab (tptr tint)) = _ := hlab
    have e2 : Exec.evalExpr ge e le m1 (.Etempvar dense.id.ptn (tptr tint)) = _ := hptn
    simp only [Exec.evalExprlist, e1, e2,
      eval_gint (c.eg _ (by decide)) find_noncheaplevel
        (hs.scalars.noncheaplevel.unch hu1 (by sep_ne hd)),
      eval_gptr (ty := tptr tulong) (c.eg _ (by decide)) find_fmptr rfl hp1,
      eval_mcr (c.eg _ (by decide)) (c.eg _ (by decide)) hp1 (hs.fixed.mm.unch hu1 (by sep_ne hd)) hMl,
      eval_gint (c.eg _ (by decide)) find_m (hs.fixed.mm.unch hu1 (by sep_ne hd)),
      eval_gint (c.eg _ (by decide)) find_n (hs.fixed.nn.unch hu1 (by sep_ne hd)), typeof, cop]
  · have hpv := hinv.ptnVals
    refine ⟨rfl, hs.arrays.lab.unch hu1 (by sep_ne hd), hs.arrays.ptn.unch hu1 (by sep_ne hd), hf0, hm0,
      hs.tables.nautilBit.unch hu1 (by sep_ne hd),
      ⟨by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd, by sep_ne hd⟩,
      .inr (.inl (by rw [uf, um]; omega)), hinv.ptnSize, hinv.labSmall,
      fun x hx => by
        rcases hpv x hx with h' | h'
        · omega
        · rw [h']; decide,
      by have := hinv.ptnLast; omega, by omega, a3, hM, by omega, hs.nM⟩
  · rintro t r m2 ⟨⟨rfl, wf', wm', hf', hm', hrf, hrm, hu2, hr2, hk2⟩, hv2⟩
    simp only [set_opttemp, seqPost, Post.after, E0_append]
    have n2 : ¬ (Block.fmptr = S.bws ∨ Block.fmptr = S.bws) := by
      rintro (hh | hh) <;> exact absurd hh (by sep_ne hd)
    have hp2 := hp1.unch hu2 n2
    have hmm2 := (hs.fixed.mm.unch hu1 (by sep_ne hd)).unch hu2 (by
      rintro (hh | hh) <;> exact absurd hh (by sep_ne hd))
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
    have hA := AutosAt.push (m' := m3) hs.arrays.autos hM (pair := fmptn st.lab st.ptn st.noncheaplevel n)
      (by rw [hk]; exact hf'.unch hu3 nb3) (by rw [hk]; exact hm'.unch hu3 nb3) hrf hrm
      (by rw [hk]; exact ((Rest.unch hu1 (by sep_ne hd)).trans hr2).trans (Rest.unch hu3 nb3))
      (((Keep.unch hu1 (by sep_ne hd)).trans (hk2 _)).trans (Keep.unch hu3 nb3)) (by rw [hk]; exact hp3)
    have hu : Unch m m3 (· ∈ [S.bws, Block.fmptr]) :=
      ((hu1.mono fun z hz => by simp [hz]).trans (hu2.mono fun z hz => by
        rcases hz with hz | hz <;> simp [hz])).trans (hu3.mono fun z hz => by simp [hz])
    have hv : ∀ z, Mem.valid_block m z → Mem.valid_block m3 z := fun z hz => hv3 _ (hv2 _ (hv1 _ hz))
    refine hQ m3 (PAt.next c h hu (by simp [SLoc.wr, SLoc.wrV, wrG]) ?_ hv
      ((hs.scalars.unch hu (by sep_all hd)).cast rfl) ((hs.stats.unch hu (by sep_notin hd)).cast rfl)
      (hs.arrays.set hu (hs.arrays.lab.unch hu (by sep_notin hd)) (hs.arrays.ptn.unch hu (by sep_notin hd))
        (hs.arrays.orbits.unch hu (by sep_notin hd)) (hs.arrays.active' hu (by sep_notin hd))
        (hs.arrays.fixedpts' hu (by sep_notin hd)) (hs.arrays.workperm' hu (by sep_notin hd))
        (hs.arrays.firstlab.unch hu (by sep_notin hd)) (hs.arrays.canonlab.unch hu (by sep_notin hd))
        (hs.arrays.firstcode.unch hu (by sep_notin hd)) (hs.arrays.canoncode.unch hu (by sep_notin hd))
        (hs.arrays.firsttc.unch hu (by sep_notin hd)) (hs.arrays.canong.unch hu (by sep_notin hd))
        hA (by sep_notin hd))
      { hinv with }) fun v hv' => hv'.unch hu (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
        exact ⟨fun e => c.ne_blocks (by simp [SLoc.blocks]) e.symm,
          fun e => c.ne_blocks (by simp [SLoc.blocks]) e.symm⟩)
    intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ((Keep.unch hu1 (by sep_ne hd)).trans (hk2 _)).trans (Keep.unch hu3 (by sep_ne hd))

end NautyVerified.Proofs.Search.Processnode

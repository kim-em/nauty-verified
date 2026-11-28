import NautyVerified.Proofs.Search.Processnode.PushPerm

/-!
# Joining the orbits

`wp_orbjoin`: `t = orbjoin(orbits, workperm, n); stats->numorbits = t;` with
`workperm` holding `w` updates `orbits` and `numorbits` as HexGraphIso's
`orbjoin`.
-/

namespace NautyVerified.Proofs.Search.Processnode

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv)
open NautyVerified.Proofs.Alloc (Keep)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}
variable {n : Nat} {m₀ m₁ m : mem} {S : SLoc} {ctx : Ctx n} {e : env} {bsr : block}
  {st : Search n} {nsp : Bool}

kernel_rfl type_orbjoinG : type_of_fundef (.Internal dense.fn.«orbjoin») =
  tfun [tptr tint, tptr tint, tint] tint

theorem orbjoin_facts {o w : Array Nat} (hd : Orbit.Descending o n) (hw : ∀ i < n, w[i]! < n) :
    Orbit.Descending (orbjoin o w n).1 n ∧ (orbjoin o w n).2 ≤ n := by
  have h1 := joins_desc hd hw n (Nat.le_refl _)
  have h2 := compresses_desc h1 n (Nat.le_refl _)
  rw [← orbjoin_eq] at h2
  exact h2

set_option maxHeartbeats 4000000 in
theorem wp_orbjoin {f : function} {Q : Post} {le : temp_env} {t : ident} {w : Array Nat}
    (c : PCtx m₀ m₁ S e bsr) (h : PAt m₀ m₁ m S ctx bsr st nsp)
    (hw : ArrayAt m .Mint32 S.bWP 0 (ints w) n) (hws : ∀ i < n, w[i]! < n)
    (hQ : ∀ m', PAt m₀ m₁ m' S ctx bsr
        { st with orbits := (orbjoin st.orbits w n).1, numorbits := (orbjoin st.orbits w n).2 } nsp →
      ArrayAt m' .Mint32 S.bWP 0 (ints w) n → (∀ v, SrAt m bsr v → SrAt m' bsr v) →
      Q.normal E0 e (PTree.set t (.Vint (ir (orbjoin st.orbits w n).2)) le) m') :
    Wp xi ge f (.Ssequence
      (sk (.Scall (some t) (.Evar dense.id.«orbjoin» (tfun [(tptr tint), (tptr tint), tint] tint))
        [(.Evar dense.id.«nauty:orbits» (tptr tint)), (.Evar dense.id.«nauty:workperm» (tptr tint)),
         (.Evar dense.id.«nauty:n» tint)]))
      (.Sassign (statsF dense.id.numorbits tint) (tv t))) Q e le m := by
  have hs := h.search
  have hd := hs.distinct
  have hinv := hs.inv
  have hnl := hs.nlt
  have hcWP : 0 < S.capWP := by have := hs.dyns.capWP; have := hs.n0; omega
  obtain ⟨hdesc', hle'⟩ := orbjoin_facts hinv.orbitsDesc hws
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.orbjoinFn Ptrofs.zero)
    (targs := [tptr tint, tptr tint, tint]) (tres := tint)
    (cc := cc_default) (vargs := [.Vptr S.bo S.oofs, .Vptr S.bWP Ptrofs.zero, .Vint (ir n)]) _ _
    (Satisfies.grow (Orbjoin.orbjoin_satisfies S.bo S.oofs S.bWP Ptrofs.zero st.orbits w n)) rfl ?_ ?_
    (by simp [Genv.find_funct, funct_orbjoinFn]) type_orbjoinG
    ⟨rfl, hs.arrays.orbits, hw, by sep_ne hd, by omega, hws, hinv.orbitsDesc⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, c.eg _ (by decide : dense.id.«orbjoin» ≠ dense.id.sr),
      find_orbjoinFn, Exec.derefLoc, access_mode]
  · simp only [Exec.evalExprlist,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) find_orbits rfl hs.fixed.orbits,
      eval_gptr (ty := tptr tint) (c.eg _ (by decide)) find_nautyWorkperm rfl
        ⟨hs.dyns.workperm.ptr hcWP, hs.dyns.workperm.bpW⟩,
      eval_gint (c.eg _ (by decide)) find_n hs.fixed.nn, typeof, cop]
  rintro tr r m1 ⟨⟨rfl, rfl, ho1, hu1, hk1⟩, hv1⟩
  simp only [set_opttemp, seqPost, Post.after, E0_append]
  have hfit := hs.stats.fits
  have hu1' := hu1
  refine wp_statsStore (off := 12) (chunk := .Mint32) (c.eg _ (by decide)) fld_numorbits rfl
    (hs.fixed.stats.unch hu1 (by sep_ne hd)) (by decide) (by omega)
    (hu1.access _ _ _ _ (by sep_ne hd) hs.stats.numorbits.writable)
    (w := .Vint (ir (orbjoin st.orbits w n).2)) (w' := .Vint (ir (orbjoin st.orbits w n).2))
    (temps_gss _ _ _) rfl ?_
  intro m2 hst
  have hu2 : Unch m1 m2 (· = S.bst) := Unch.store hst rfl
  have hu : Unch m m2 (· ∈ [S.bo, S.bst]) :=
    (hu1.mono fun z hz => by simp [hz]).trans (hu2.mono fun z hz => by simp [hz])
  have hv : ∀ z, Mem.valid_block m z → Mem.valid_block m2 z :=
    fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ (hv1 _ hz)
  have sS := hs.stats.unch hu1 (by sep_ne hd)
  refine hQ m2 (PAt.next c h hu (by simp [SLoc.wr, SLoc.wrV]) ?_ hv
      ((hs.scalars.unch hu (by sep_all hd)).cast rfl)
      { (sS.fix.store hst (by first | omega | (simp only [csize32, csize64]; omega))) with
        numorbits := FieldAt.store_same hst sS.numorbits.writable
        numgenerators := sS.numgenerators.store_other hst (by simp only [csize32]; omega)
        numnodes := sS.numnodes.store_other hst (by simp only [csize32, csize64]; omega)
        numbadleaves := sS.numbadleaves.store_other hst (by simp only [csize32, csize64]; omega)
        maxlevel := fun hp => (sS.maxlevel hp).store_other hst (by simp only [csize32]; omega)
        maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ sS.maxlevelW
        tctotal := sS.tctotal.store_other hst (by simp only [csize32, csize64]; omega)
        canupdates := sS.canupdates.store_other hst (by simp only [csize32, csize64]; omega)
        fits := sS.fits }
      (hs.arrays.set hu (hs.arrays.lab.unch hu (by sep_notin hd)) (hs.arrays.ptn.unch hu (by sep_notin hd))
        (ho1.unch hu2 (by sep_ne hd)) (hs.arrays.active' hu (by sep_notin hd))
        (hs.arrays.fixedpts' hu (by sep_notin hd)) (hs.arrays.workperm' hu (by sep_notin hd))
        (hs.arrays.firstlab.unch hu (by sep_notin hd)) (hs.arrays.canonlab.unch hu (by sep_notin hd))
        (hs.arrays.firstcode.unch hu (by sep_notin hd)) (hs.arrays.canoncode.unch hu (by sep_notin hd))
        (hs.arrays.firsttc.unch hu (by sep_notin hd)) (hs.arrays.canong.unch hu (by sep_notin hd))
        (hs.arrays.autos.unch hu (by sep_notin hd) (by sep_notin hd)) (by sep_notin hd))
      { hinv with
        orbitsSmall := fun i hi => by
          show (orbjoin st.orbits w n).1[i]! < n
          have := hdesc'.2 i hi; omega
        orbitsSize := hdesc'.1
        numorbitsLe := hle'
        orbitsDesc := hdesc' }) (hw.unch hu (by sep_notin hd)) fun v hv' => hv'.unch hu (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
        exact ⟨fun e => c.ne_blocks (by simp [SLoc.blocks]) e.symm,
          fun e => c.ne_blocks (by simp [SLoc.blocks]) e.symm⟩)
  intro z hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (hk1 _).trans (Keep.unch hu2 (by sep_ne hd))

end NautyVerified.Proofs.Search.Processnode

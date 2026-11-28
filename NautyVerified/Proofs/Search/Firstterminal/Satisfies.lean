import NautyVerified.Proofs.Search.Firstterminal.Copy
import NautyVerified.Spec.Firstterminal

/-!
# `firstterminal` installs the first leaf

`firstterminal_satisfies`: nauty.c's `firstterminal` satisfies
`firstterminalSpec`, i.e. takes memory holding the search state `st` to memory
holding HexGraphIso's `firstterminal level st`.
-/

namespace NautyVerified.Proofs.Search.Firstterminal

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv ix)
open NautyVerified.Proofs.Alloc (gat Keep DynAt)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

/-- The temporaries on entry. -/
def entryTemps (S : SLoc) (level : Nat) : temp_env :=
  PTree.set dense.id.level (.Vint (ir level)) (PTree.set dense.id.lab (.Vptr S.bl S.lofs)
    (create_undef_temps dense.fn.«nauty:firstterminal».fn_temps))

set_option maxHeartbeats 4000000 in
theorem firstterminal_satisfies {xi : ExternalCalls} {n : Nat} (S : SLoc) (ctx : Ctx n)
    (st : Search n) (level : Nat) :
    Satisfies xi ge (.Internal dense.fn.«nauty:firstterminal») (firstterminalSpec S ctx st level) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps S level ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps S level, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, h, hl1, hln⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.«nauty:firstterminal».fn_body_eq, body_eq]
    simp only [body]
    have hd := h.distinct
    have hn := h.nlt
    have hlev : PTree.get dense.id.level (entryTemps S level) = some (.Vint (ir level)) := by
      simp (config := {decide := true}) only [entryTemps, temps_gss]
    have hlab : PTree.get dense.id.lab (entryTemps S level) = some (.Vptr S.bl S.lofs) := by
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have hfits := h.stats.fits
    -- `stats->maxlevel = level`
    wp_step; wp_step; wp_step
    refine wp_statsStore (S := S) (ty := tint) (chunk := .Mint32) (off := 40) rfl fld_maxlevel rfl
      h.fixed.stats (by decide) (by omega)
      h.stats.maxlevelW (show Exec.evalExpr ge empty_env _ _ (tv dense.id.level) = _ from hlev)
      (by simp only [typeof, cop]; rfl) ?_
    intro m1 hst1
    have c4 : csize .Mint32 = 4 := rfl
    have c8 : csize .Mint64 = 8 := rfl
    have hU1 : Unch m m1 (· ∈ [S.bst]) := (Unch.store hst1 rfl).mono fun z hz => by simp [hz]
    have sMax : FieldAt m1 .Mint32 S.bst (S.sb + 40) (.Vint (ir level)) :=
      FieldAt.store_same hst1 h.stats.maxlevelW
    have sOrb := h.stats.numorbits.store_other hst1 (.inl (by rw [c4]; omega))
    have sGen := h.stats.numgenerators.store_other hst1 (.inl (by rw [c4]; omega))
    have sNod := h.stats.numnodes.store_other hst1 (.inl (by rw [c8]; omega))
    have sBad := h.stats.numbadleaves.store_other hst1 (.inl (by rw [c8]; omega))
    have sTct := h.stats.tctotal.store_other hst1 (.inr (by rw [c4]; omega))
    have sCan := h.stats.canupdates.store_other hst1 (.inr (by rw [c4]; omega))
    have sFix := h.stats.fix.store hst1 (.inl (by omega))
    -- `eqlev_first = allsamelevel = gca_first = level`
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hlev, Refine.tv, typeof, cop]
    refine wp_gint (x := level) rfl find_eqlevFirst
      (h.scalars.eqlevFirst.unch hU1 (by sep_notin hd)).writable
      (by simp only [Exec.evalExpr, Refine.tv, temps_gss]) rfl ?_
    intro m2 iEF hu2 hv2
    have hU2 := hU1.snoc hu2
    fwd hd hu2 [sFix sMax sOrb sGen sNod sBad sTct sCan]
    simp only [seqPost, Post.after, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof, cop]
    refine wp_gint (x := level) rfl find_allsamelevel
      (h.scalars.allsamelevel.unch hU2 (by sep_notin hd)).writable
      (by simp only [Exec.evalExpr, Refine.tv, temps_gss]) rfl ?_
    intro m3 iAS hu3 hv3
    have hU3 := hU2.snoc hu3
    fwd hd hu3 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF]
    simp only [seqPost, Post.after, E0_append]
    refine wp_gint (x := level) rfl find_gcaFirst
      (h.scalars.gcaFirst.unch hU3 (by sep_notin hd)).writable
      (by simp only [Exec.evalExpr, Refine.tv, temps_gss]) rfl ?_
    intro m4 iGF hu4 hv4
    have hU4 := hU3.snoc hu4
    fwd hd hu4 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS]
    have hcFC : 0 < S.capFC := by have := h.dyns.capFC; omega
    have hcTC : 0 < S.capTC := by have := h.dyns.capTC; omega
    have hcFL : 0 < S.capFL := by have := h.dyns.capFL; have := h.n0; omega
    have hcCL : 0 < S.capCL := by have := h.dyns.capCL; have := h.n0; omega
    have hcCC : 0 < S.capCC := by have := h.dyns.capCC; omega
    let le4 := PTree.set (idOf 704) (.Vint (ir level)) (PTree.set (idOf 703) (.Vint (ir level))
      (entryTemps S level))
    have hlev4 : PTree.get dense.id.level le4 = some (.Vint (ir level)) := by
      simp (config := {decide := true}) only [le4, temps_gso]; exact hlev
    have hlab4 : PTree.get dense.id.lab le4 = some (.Vptr S.bl S.lofs) := by
      simp (config := {decide := true}) only [le4, temps_gso]; exact hlab
    have hl1v : ∀ mm, Exec.evalExpr ge empty_env le4 mm
        (.Ebinop .Oadd (tv dense.id.level) (ci 1 tint) tint) =
        some (.Vint (ir ((level + 1 : Nat) : Int))) := fun mm => by
      simp only [Exec.evalExpr, Refine.tv, hlev4, typeof, cop, ir_add]; push_cast; rfl
    -- `firstcode[level+1] = 077777`
    wp_step; wp_step; wp_step
    refine wp_gstoreS (le := le4) rfl find_nautyFirstcode
      (by rw [hU4.load _ _ _ (by sep_notin hd)]; exact h.dyns.firstcode.ptr hcFC)
      (h.arrays.firstcode.unch hU4 (by sep_notin hd)) (by omega) _ (level + 1) (by omega) (hl1v _) rfl
      (ci 32767 tint) 32767 (by decide) rfl (.inl rfl) ?_
    intro m5 aFC hu5 kFC hv5
    have hU5 := hU4.snoc hu5
    fwd hd hu5 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF]
    -- `firsttc[level+1] = -1`
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_gstoreV (le := le4) rfl find_nautyFirsttc
      (by rw [hU5.load _ _ _ (by sep_notin hd)]; exact h.dyns.firsttc.ptr hcTC)
      (h.arrays.firsttc.unch hU5 (by sep_notin hd)) (by omega) _ (level + 1) (by omega) (hl1v _) rfl
      (.Eunop .Oneg (ci 1 tint) tint) (-1) (by simp only [Exec.evalExpr, typeof, cop]; rfl) rfl ?_
    intro m6 aTC hu6 kTC hv6
    have hU6 := hU5.snoc hu6
    fwd hd hu6 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC]
    fwdK hd hu6 [kFC]
    -- `for (i = 0; i < n; ++i) firstlab[i] = lab[i]`
    simp only [seqPost, Post.after, E0_append]
    wp_step
    refine wp_copyInts (le := le4) (by omega) rfl rfl find_nautyFirstlab
      (by rw [hU6.load _ _ _ (by sep_notin hd)]; exact h.dyns.firstlab.ptr hcFL)
      (h.arrays.firstlab.unch hU6 (by sep_notin hd)) hlab4
      (h.arrays.lab.unch hU6 (by sep_notin hd)) (h.fixed.nn.unch hU6 (by sep_notin hd)) (by decide)
      (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) ?_
    intro le7 m7 aFL hu7 kFL hv7 ho7
    have hU7 := hU6.snoc hu7
    fwd hd hu7 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC aTC]
    fwdK hd hu7 [kFC kTC]
    have hlev7 : PTree.get dense.id.level le7 = some (.Vint (ir level)) := by
      rw [ho7 _ (by decide)]; exact hlev4
    have hlab7 : PTree.get dense.id.lab le7 = some (.Vptr S.bl S.lofs) := by
      rw [ho7 _ (by decide)]; exact hlab4
    -- `if (getcanon)`
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    apply wp_if_eval
    rw [eval_gint rfl find_getcanon (h.fixed.getcanon.unch hU7 (by sep_notin hd))]
    simp only [typeof, cop]
    rw [ite_eq_left (by decide)]
    -- `canonlevel = eqlev_canon = gca_canon = level`
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hlev7, Refine.tv, typeof, cop]
    refine wp_gint (x := level) rfl find_gcaCanon
      (h.scalars.gcaCanon.unch hU7 (by sep_notin hd)).writable
      (by simp only [Exec.evalExpr, Refine.tv, temps_gss]) rfl ?_
    intro m8 iGC hu8 hv8
    have hU8 := hU7.snoc hu8
    fwd hd hu8 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC aTC aFL]
    fwdK hd hu8 [kFC kTC kFL]
    simp only [seqPost, Post.after, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, Refine.tv, temps_gss, typeof, cop]
    refine wp_gint (x := level) rfl find_eqlevCanon
      (h.scalars.eqlevCanon.unch hU8 (by sep_notin hd)).writable
      (by simp only [Exec.evalExpr, Refine.tv, temps_gss]) rfl ?_
    intro m9 iEC hu9 hv9
    have hU9 := hU8.snoc hu9
    fwd hd hu9 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC aTC aFL iGC]
    fwdK hd hu9 [kFC kTC kFL]
    simp only [seqPost, Post.after, E0_append]
    refine wp_gint (x := level) rfl find_canonlevel
      (h.scalars.canonlevel.unch hU9 (by sep_notin hd)).writable
      (by simp only [Exec.evalExpr, Refine.tv, temps_gss]) rfl ?_
    intro m10 iCL hu10 hv10
    have hU10 := hU9.snoc hu10
    fwd hd hu10 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC aTC aFL iGC iEC]
    fwdK hd hu10 [kFC kTC kFL]
    -- `comp_canon = 0; samerows = 0`
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_gint (x := 0) rfl find_compCanon
      (h.scalars.compCanon.unch hU10 (by sep_notin hd)).writable
      (by simp only [Exec.evalExpr]) rfl ?_
    intro m11 iCC0 hu11 hv11
    have hU11 := hU10.snoc hu11
    fwd hd hu11 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC aTC aFL iGC iEC iCL]
    fwdK hd hu11 [kFC kTC kFL]
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_gint (x := 0) rfl find_samerows
      (h.scalars.samerows.unch hU11 (by sep_notin hd)).writable
      (by simp only [Exec.evalExpr]) rfl ?_
    intro m12 iSR hu12 hv12
    have hU12 := hU11.snoc hu12
    fwd hd hu12 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC aTC aFL iGC iEC iCL iCC0]
    fwdK hd hu12 [kFC kTC kFL]
    let le12 := PTree.set (idOf 706) (.Vint (ir level)) (PTree.set (idOf 705) (.Vint (ir level)) le7)
    have hlev12 : PTree.get dense.id.level le12 = some (.Vint (ir level)) := by
      simp (config := {decide := true}) only [le12, temps_gso]; exact hlev7
    have hlab12 : PTree.get dense.id.lab le12 = some (.Vptr S.bl S.lofs) := by
      simp (config := {decide := true}) only [le12, temps_gso]; exact hlab7
    -- `for (i = 0; i < n; ++i) canonlab[i] = lab[i]`
    simp only [seqPost, Post.after, E0_append]
    wp_step
    refine wp_copyInts (le := le12) (by omega) rfl rfl find_nautyCanonlab
      (by rw [hU12.load _ _ _ (by sep_notin hd)]; exact h.dyns.canonlab.ptr hcCL)
      (h.arrays.canonlab.unch hU12 (by sep_notin hd)) hlab12
      (h.arrays.lab.unch hU12 (by sep_notin hd)) (h.fixed.nn.unch hU12 (by sep_notin hd)) (by decide)
      (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) ?_
    intro le13 m13 aCL hu13 kCL hv13 ho13
    have hU13 := hU12.snoc hu13
    fwd hd hu13 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC aTC aFL iGC iEC iCL iCC0 iSR]
    fwdK hd hu13 [kFC kTC kFL]
    have hlev13 : PTree.get dense.id.level le13 = some (.Vint (ir level)) := by
      rw [ho13 _ (by decide)]; exact hlev12
    -- `for (i = 0; i <= level; ++i) canoncode[i] = firstcode[i]`
    have hinv := h.inv
    have hfcs : st.firstcode.size = n + 2 := hinv.firstcodeSize
    have hfc' : ArrayAt m13 .Mint16signed S.bFC 0
        (shorts (st.firstcode.set! (level + 1) 32767)) (n + 2) := by
      rw [shorts_set (by omega)]; exact aFC
    simp only [seqPost, Post.after, E0_append]
    wp_step
    refine wp_copyShorts (le := le13) (by omega) (by omega) rfl find_nautyCanoncode
      (by rw [hU13.load _ _ _ (by sep_notin hd)]; exact h.dyns.canoncode.ptr hcCC)
      (h.arrays.canoncode.unch hU13 (by sep_notin hd)) rfl find_nautyFirstcode
      (by rw [hU13.load _ _ _ (by sep_notin hd)]; exact h.dyns.firstcode.ptr hcFC)
      hfc' (fun j hj => by
        by_cases hjl : j = level + 1
        · subst hjl; rw [Array.getElem!_set!_self _ _ _ (by omega)]; decide
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjl)]; exact (hinv.codesSmall j hj).1)
      hlev13 (by sep_ne hd) (by sep_ne hd) (by sep_ne hd) ?_
    intro le14 m14 aCC hu14 kCC hv14 ho14
    have hU14 := hU13.snoc hu14
    fwd hd hu14 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC aTC aFL iGC iEC iCL iCC0 iSR aCL]
    fwdK hd hu14 [kFC kTC kFL kCL]
    have hlev14 : PTree.get dense.id.level le14 = some (.Vint (ir level)) := by
      rw [ho14 _ (by decide)]; exact hlev13
    -- `canoncode[level+1] = 077777`
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine wp_gstoreS (le := le14) rfl find_nautyCanoncode
      (by rw [hU14.load _ _ _ (by sep_notin hd)]; exact h.dyns.canoncode.ptr hcCC)
      aCC (by omega) _ (level + 1) (by omega)
      (by simp only [Exec.evalExpr, Refine.tv, hlev14, typeof, cop, ir_add]; push_cast; rfl) rfl
      (ci 32767 tint) 32767 (by decide) rfl (.inl rfl) ?_
    intro m15 aCC2 hu15 kCC2 hv15
    have hU15 := hU14.snoc hu15
    fwd hd hu15 [sFix sMax sOrb sGen sNod sBad sTct sCan iEF iAS iGF aFC aTC aFL iGC iEC iCL iCC0 iSR aCL]
    fwdK hd hu15 [kFC kTC kFL kCL]
    replace kCC := kCC.trans kCC2
    -- `stats->canupdates = 1`
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    refine wp_statsStore (S := S) (ty := tulong) (chunk := .Mint64) (off := 56) rfl fld_canupdates
      rfl (h.fixed.stats.unch hU15 (by sep_notin hd)) (by decide) (by omega) sCan.writable
      (show Exec.evalExpr ge empty_env le14 m15 (ci 1 tint) = some (.Vint (ir 1)) from rfl)
      (by simp only [typeof, cop, cast_int_long_ir (a := 1) ⟨by decide, by decide⟩]; rfl) ?_
    intro m16 hst16
    have hu16 : Unch m15 m16 (· = S.bst) := Unch.store hst16 rfl
    have hU16 := hU15.snoc hu16
    have sCan16 : FieldAt m16 .Mint64 S.bst (S.sb + 56) (.Vlong (lr ((1 : Nat) : Int))) :=
      FieldAt.store_same hst16 sCan.writable
    replace sMax := sMax.store_other hst16 (.inl (by rw [c4]; omega))
    replace sFix := sFix.store hst16 (.inl (by omega))
    replace sOrb := sOrb.store_other hst16 (.inl (by rw [c4]; omega))
    replace sGen := sGen.store_other hst16 (.inl (by rw [c4]; omega))
    replace sNod := sNod.store_other hst16 (.inl (by rw [c8]; omega))
    replace sBad := sBad.store_other hst16 (.inl (by rw [c8]; omega))
    replace sTct := sTct.store_other hst16 (.inl (by rw [c8]; omega))
    fwd hd hu16 [iEF iAS iGF aFC aTC aFL iGC iEC iCL iCC0 iSR aCL aCC2]
    fwdK hd hu16 [kFC kTC kFL kCL kCC]
    have hV : ∀ z, Mem.valid_block m z → Mem.valid_block m16 z := fun z hz =>
      Mem.store_valid_block_1 _ _ _ _ _ _ hst16 _ (hv15 _ (hv14 _ (hv13 _ (hv12 _ (hv11 _ (hv10 _
        (hv9 _ (hv8 _ (hv7 _ (hv6 _ (hv5 _ (hv4 _ (hv3 _ (hv2 _
          (Mem.store_valid_block_1 _ _ _ _ _ _ hst1 _ hz)))))))))))))))
    have hinv := h.inv
    have hccs : st.canoncode.size = n + 2 := hinv.canoncodeSize
    have htcs : st.firsttc.size = n + 2 := hinv.firsttcSize
    have hfcs : st.firstcode.size = n + 2 := hinv.firstcodeSize
    have hcs : codeSentinel = 32767 := rfl
    have hfc'small : ∀ i < n + 2, (st.firstcode.set! (level + 1) codeSentinel)[i]! < 32768 :=
      fun i hi => by
        by_cases hi' : i = level + 1
        · subst hi'; rw [Array.getElem!_set!_self _ _ _ (by omega), hcs]; decide
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hi')]; exact (hinv.codesSmall i hi).1
    refine ⟨m16, Nextelement.free_empty m16, rfl, ?_, ?_⟩
    · rw [firstterminal_eq]
      exact
        { fixed := h.fixed.unch hU16 (by sep_all hd)
          scalars := ⟨iGF, iGC, h.scalars.noncheaplevel.unch hU16 (by sep_notin hd), iAS, iEF, iEC,
            iCC0, iSR, iCL, h.scalars.stabvertex.unch hU16 (by sep_notin hd),
            h.scalars.cosetindex.unch hU16 (by sep_notin hd),
            h.scalars.needshortprune.unch hU16 (by sep_notin hd)⟩
          stats := ⟨sOrb, sGen, sNod, sBad, fun _ => sMax, sMax.writable, sTct, sCan16,
            h.stats.fits, sFix.perm, sFix.errstatus, sFix.grpsize1, sFix.grpsize2⟩
          arrays :=
            { lab := h.arrays.lab.unch hU16 (by sep_notin hd)
              ptn := h.arrays.ptn.unch hU16 (by sep_notin hd)
              orbits := h.arrays.orbits.unch hU16 (by sep_notin hd)
              active := let ⟨aw, ha, hr⟩ := h.arrays.active
                ⟨aw, ha.unch hU16 (by sep_notin hd), hr⟩
              fixedpts := let ⟨fw, hf, hr⟩ := h.arrays.fixedpts
                ⟨fw, hf.unch hU16 (by sep_notin hd), hr⟩
              workperm := let ⟨wv, hwv⟩ := h.arrays.workperm
                ⟨wv, hwv.unch hU16 (by sep_notin hd)⟩
              firstlab := aFL
              canonlab := aCL
              firstcode := by rw [shorts_set (by omega), hcs]; exact aFC
              canoncode := aCC2.congr fun j hj => by
                simp only [upd, shorts]
                by_cases hjl : j = level + 1
                · subst hjl
                  rw [ite_eq_left rfl, Array.getElem!_set!_self _ _ _ (by rw [ccCopy_size]; omega),
                    hcs]
                · rw [ite_eq_right hjl]
                  simp only [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjl),
                    ccCopy_get _ _ _ (show level + 1 ≤ st.canoncode.size by omega)]
                  split <;> rfl
              firsttc := by rw [intsZ_set (by omega)]; exact aTC
              canong := ⟨by
                obtain ⟨cw, ha, -⟩ := h.arrays.canong.arr
                exact ⟨cw, ha.unch hU16 (by sep_notin hd), fun v hv => absurd hv (Nat.not_lt_zero _)⟩⟩
              autos := h.arrays.autos.unch hU16 (by sep_notin hd) (by sep_notin hd)
              graph := ⟨h.arrays.graph.arr.unch hU16 (by sep_notin hd), h.arrays.graph.rep⟩ }
          dyns :=
            { h.dyns with
              active := h.dyns.active.keep hU16 (by sep_notin hd) (by sep_notin hd)
                fun _ => Keep.unch hU16 (by sep_notin hd)
              fixedpts := h.dyns.fixedpts.keep hU16 (by sep_notin hd) (by sep_notin hd)
                fun _ => Keep.unch hU16 (by sep_notin hd)
              workperm := h.dyns.workperm.keep hU16 (by sep_notin hd) (by sep_notin hd)
                fun _ => Keep.unch hU16 (by sep_notin hd)
              firstlab := h.dyns.firstlab.keep hU16 (by sep_notin hd) (by sep_notin hd)
                fun _ => (Keep.unch hU6 (by sep_notin hd)).trans kFL
              canonlab := h.dyns.canonlab.keep hU16 (by sep_notin hd) (by sep_notin hd)
                fun _ => (Keep.unch hU12 (by sep_notin hd)).trans kCL
              firstcode := h.dyns.firstcode.keep hU16 (by sep_notin hd) (by sep_notin hd)
                fun _ => (Keep.unch hU4 (by sep_notin hd)).trans kFC
              canoncode := h.dyns.canoncode.keep hU16 (by sep_notin hd) (by sep_notin hd)
                fun _ => (Keep.unch hU13 (by sep_notin hd)).trans kCC
              firsttc := h.dyns.firsttc.keep hU16 (by sep_notin hd) (by sep_notin hd)
                fun _ => (Keep.unch hU5 (by sep_notin hd)).trans kTC }
          work := h.work.unch hU16 (by sep_all hd) fun z hz hm => h.work_not hz (by
            clear hz; revert hm; revert z; simp [SLoc.blocks])
          tables := h.tables.unch hU16 (by sep_all hd)
          distinct := hd
          inv :=
            { hinv with
              codesSmall := fun i hi => ⟨hfc'small i hi, by
                by_cases hi' : i = level + 1
                · subst hi'
                  rw [Array.getElem!_set!_self _ _ _ (by rw [ccCopy_size]; omega), hcs]; decide
                · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hi'), ccCopy_get _ _ _ (by omega)]
                  split
                  · exact hfc'small i hi
                  · exact (hinv.codesSmall i hi).2⟩
              firsttcRange := fun i hi => by
                by_cases hi' : i = level + 1
                · subst hi'; rw [Array.getElem!_set!_self _ _ _ (by omega)]
                  have := h.n0; omega
                · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hi')]; exact hinv.firsttcRange i hi
              samerows := Nat.zero_le n
              firstlabSize := hinv.labSize
              canonlabSize := hinv.labSize
              firstcodeSize := by simp [hfcs]
              canoncodeSize := by simp [ccCopy_size, hccs]
              firsttcSize := by simp [htcs]
              scalars := by
                obtain ⟨-, -, a3, -, -, -, -, -, -, -, a11, a12⟩ := hinv.scalars
                have := h.nlt
                exact ⟨by simp; omega, by simp; omega, a3, by simp; omega, by simp; omega,
                  by simp, by simp; omega, by simp, by simp, by simp; omega, a11, a12⟩
              maxlevelLe := by simp only []; omega }
          n0 := h.n0, nlt := h.nlt, nM := h.nM, M1 := h.M1, Mlt := h.Mlt }
    · exact ⟨hU16.mono fun z hz => .inl ⟨by revert hz; revert z; simp [SLoc.blocks], by revert hz; revert z; sep_all hd,
          by revert hz; revert z; sep_all hd⟩, hV⟩

end NautyVerified.Proofs.Search.Firstterminal

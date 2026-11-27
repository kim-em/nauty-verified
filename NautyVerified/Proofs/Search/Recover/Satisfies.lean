import NautyVerified.Proofs.Search.Recover.Syntax
import NautyVerified.Spec.Recover

/-!
# `recover` restores the partition and the levels

`recover_satisfies`: nauty.c's `recover` satisfies `recoverSpec`: it takes
memory holding `st` to memory holding HexGraphIso's
`recover nautyInf level st`.
-/

namespace NautyVerified.Proofs.Search.Recover

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv ix)
open NautyVerified.Proofs.Alloc (Keep DynAt)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- The temporaries on entry. -/
def entryTemps (S : SLoc) (level : Nat) : temp_env :=
  PTree.set dense.id.level (.Vint (ir level)) (PTree.set dense.id.ptn (.Vptr S.bp S.pofs)
    (create_undef_temps dense.fn.«nauty:recover».fn_temps))

/-- The rescan loop: `ptn` becomes the fold of `reopen`. -/
theorem wp_rescan {Q : Post} {le : temp_env} {m : mem} {S : SLoc} {n level : Nat}
    {p : Array Nat} (hn : n < 1073741824) (hps : p.size = n)
    (hpv : ∀ j < n, p[j]! ≤ n + 1 ∨ p[j]! = nautyInf) (hlev : level < 2147483648)
    (hptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs))
    (hlv : PTree.get dense.id.level le = some (.Vint (ir level)))
    (harr : ArrayAt m .Mint32 S.bp S.pb (ints p) n) (hN : IntAt m Block.n n)
    (hbn : S.bp ≠ Block.n)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 S.bp S.pb (ints ((List.range n).foldl
        (reopen nautyInf level) p)) n → Unch m m' (· = S.bp) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi ge dense.fn.«nauty:recover» (forLoopC dense.id.i
      (.Ebinop .Olt (tv dense.id.i) (.Evar dense.id.«nauty:n» tint) tint)
      (sk (.Sifthenelse (.Ebinop .Ogt (ix dense.id.ptn (tv dense.id.i)) (tv dense.id.level) tint)
        (sk (.Sassign (ix dense.id.ptn (tv dense.id.i)) (ci 2000000002 tint))) .Sskip)))
      Q empty_env le m := by
  let F := fun k => (List.range k).foldl (reopen nautyInf level) p
  let Inv := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k ≤ n ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
    (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) ∧
    ArrayAt m' .Mint32 S.bp S.pb (ints (F k)) n ∧ Unch m m' (· = S.bp) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  let Mid := fun (k : Nat) (le' : temp_env) (m' : mem) =>
    k < n ∧ PTree.get dense.id.i le' = some (.Vint (ir k)) ∧
    (∀ x, x ≠ dense.id.i → PTree.get x le' = PTree.get x le) ∧
    ArrayAt m' .Mint32 S.bp S.pb (ints (F (k + 1))) n ∧ Unch m m' (· = S.bp) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z)
  refine wp_forLoopC (Inv := Inv) (Mid := Mid) dense.id.i _ rfl _ n (by omega) ?_ ?_ ?_ ?_ ?_
  · rintro k le' m' ⟨hk, hi, -, -, hu, -⟩
    refine ⟨hk, hi, ?_⟩
    rw [Exec.evalExpr, eval_gint (e := empty_env) (le := le') rfl find_n (hN.unch hu (Ne.symm hbn)),
      show Exec.evalExpr ge empty_env le' m' (tv dense.id.i) = _ from hi]
    simp only [typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp
  · exact ⟨Nat.zero_le _, temps_gss _ _ _, fun x hx => temps_gso _ _ hx, harr, Unch.refl _ _,
      fun _ h => h⟩
  · rintro k le' m' hk ⟨-, hi, ho, ha, hu, hv⟩
    obtain ⟨hFs, hFv⟩ : (F k).size = n ∧ ∀ j < n, (F k)[j]! ≤ n + 1 ∨ (F k)[j]! = nautyInf :=
      reopen_fold (level := level) hps hpv k
    have hp' : PTree.get dense.id.ptn le' = some (.Vptr S.bp S.pofs) := by
      rw [ho _ (by decide)]; exact hptn
    have hl' : PTree.get dense.id.level le' = some (.Vint (ir level)) := by
      rw [ho _ (by decide)]; exact hlv
    have hpe := eval_at (ge := ge) (e := empty_env) ha (by omega) dense.id.ptn hp' (tv dense.id.i) k hk
      hi rfl
    have hsmall : (F k)[k]! < 2147483648 := by
      rcases hFv k hk with h | h
      · omega
      · rw [h]; decide
    have hF1 : F (k + 1) = reopen nautyInf level (F k) k := by
      simp only [F, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hpe, show Exec.evalExpr ge empty_env le' m' (tv dense.id.level) = _ from hl']
    simp only [ints, typeof, cop]
    rw [ir_lt (a := (level : Int)) (b := ((F k)[k]! : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hgt : level < (F k)[k]!
    · rw [ite_eq_left (by simpa using hgt)]
      wp_step; wp_step
      refine wp_storeV ha (by omega) dense.id.ptn hp' (tv dense.id.i) k hk hi rfl
        (ci 2000000002 tint) 2000000002 rfl rfl ?_
      intro m'' ha' hu' hv'
      refine ⟨rfl, hk, hi, ho, ?_, hu.trans hu', fun z hz => hv' z (hv z hz)⟩
      rw [hF1, reopen, ite_eq_left hgt, ints_set (by omega)]
      exact ha'
    · rw [ite_eq_right (by simpa using hgt)]
      apply wp_skip
      refine ⟨rfl, hk, hi, ho, ?_, hu, hv⟩
      rw [hF1, reopen, ite_eq_right hgt]
      exact ha
  · rintro k le' m' ⟨hk, hi, ho, ha, hu, hv⟩
    exact ⟨hi, hk, temps_gss _ _ _, fun x hx => by rw [temps_gso _ _ hx, ho x hx], ha, hu, hv⟩
  · rintro le' m' ⟨-, -, ho, ha, hu, hv⟩
    exact hQ le' m' ha hu hv ho

set_option maxHeartbeats 4000000 in
theorem recover_satisfies {n : Nat} (S : SLoc) (ctx : Ctx n) (st : Search n) (level : Nat)
    (pre : Bool) :
    Satisfies xi ge (.Internal dense.fn.«nauty:recover») (recoverSpec S ctx st level pre) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps S level ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps S level, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, h, hln⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.«nauty:recover».fn_body_eq, body_eq]
    simp only [body]
    have hd := h.distinct
    have hn := h.nlt
    have hinv := h.inv
    obtain ⟨-, -, a3, -, a5, a6, a7, a8, a9, -, -, -⟩ := hinv.scalars
    have hlev : PTree.get dense.id.level (entryTemps S level) = some (.Vint (ir level)) := by
      simp (config := {decide := true}) only [entryTemps, temps_gss]
    have hptn : PTree.get dense.id.ptn (entryTemps S level) = some (.Vptr S.bp S.pofs) := by
      simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]
    have hpv : ∀ j < n, st.ptn[j]! ≤ n + 1 ∨ st.ptn[j]! = nautyInf := hinv.ptnVals
    -- the rescan
    wp_step
    refine wp_rescan (S := S) hn hinv.ptnSize hpv (by omega) hptn hlev h.arrays.ptn h.fixed.nn
      (by sep_ne hd) ?_
    intro le1 m1 aP hu1 hv1 ho1
    have hU1 : Unch m m1 (· ∈ [S.bp]) := hu1.mono fun z hz => by simp [hz]
    have hlev1 : PTree.get dense.id.level le1 = some (.Vint (ir level)) := by
      rw [ho1 _ (by decide)]; exact hlev
    have hcmp : ∀ (mm : mem) (g : ident) (b : block) (v : Nat), Genv.find_symbol ge.genv_genv g = some b →
        IntAt mm b v → v < 2147483648 →
        Exec.evalExpr ge empty_env le1 mm (.Ebinop .Olt (tv dense.id.level) (.Evar g tint) tint) =
          some (Val.of_bool (decide (level < v))) := by
      intro mm g b v hg hI hv
      rw [Exec.evalExpr, eval_gint (e := empty_env) (le := le1) rfl hg hI,
        show Exec.evalExpr ge empty_env le1 mm (tv dense.id.level) = _ from hlev1]
      simp only [typeof, cop]
      rw [ir_lt (a := (level : Int)) (b := (v : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      simp
    -- `if (level < noncheaplevel) noncheaplevel = level + 1`
    simp only [seqPost, Post.after, E0_append]
    wp_step
    refine wp_clamp rfl find_noncheaplevel (h.scalars.noncheaplevel.unch hU1 (by sep_notin hd))
      (hcmp _ _ _ _ find_noncheaplevel (h.scalars.noncheaplevel.unch hU1 (by sep_notin hd)) a3) rfl
      (x := (level : Int) + 1)
      (by simp only [Exec.evalExpr, Refine.tv, hlev1, typeof, cop, ir_add]) rfl ?_
    intro m2 iNC hu2 hv2
    have hU2 := hU1.snoc hu2
    fwd hd hu2 [aP]
    -- `if (level < eqlev_first) eqlev_first = level`
    simp only [seqPost, Post.after, E0_append]
    wp_step
    refine wp_clamp rfl find_eqlevFirst (h.scalars.eqlevFirst.unch hU2 (by sep_notin hd))
      (hcmp _ _ _ _ find_eqlevFirst (h.scalars.eqlevFirst.unch hU2 (by sep_notin hd)) a5) rfl
      (x := (level : Int)) hlev1 rfl ?_
    intro m3 iEF hu3 hv3
    have hU3 := hU2.snoc hu3
    fwd hd hu3 [aP iNC]
    -- `if (getcanon)`
    wp_step; wp_step
    apply wp_if_eval
    rw [eval_gint rfl find_getcanon (h.fixed.getcanon.unch hU3 (by sep_notin hd))]
    simp only [typeof, cop]
    rw [ite_eq_left (by decide)]
    -- `if (level < gca_canon) gca_canon = level`
    wp_step
    refine wp_clamp rfl find_gcaCanon (h.scalars.gcaCanon.unch hU3 (by sep_notin hd))
      (hcmp _ _ _ _ find_gcaCanon (h.scalars.gcaCanon.unch hU3 (by sep_notin hd))
        hinv.scalars.2.1) rfl
      (x := (level : Int)) hlev1 rfl ?_
    intro m4 iGC hu4 hv4
    have hU4 := hU3.snoc hu4
    fwd hd hu4 [aP iNC iEF]
    -- the end, from the last clamp's two cells
    let c : Prop := (level : Int) ≤ st.eqlevCanon
    have fin : ∀ mf, IntAt mf Block.eqlevCanon (if c then (level : Int) else st.eqlevCanon) →
        IntAt mf Block.compCanon (if c then 0 else st.compCanon) →
        Unch m4 mf (· ∈ [Block.compCanon, Block.eqlevCanon]) →
        (∀ z, Mem.valid_block m4 z → Mem.valid_block mf z) →
        ∃ m', Mem.free_list mf (blocks_of_env ge empty_env) = some m' ∧
          (recoverSpec S ctx st level pre).post [.Vptr S.bp S.pofs, .Vint (ir level)] m E0 .Vundef m' := by
      intro mf iEC iCC huf hvf
      have hUf : Unch m mf (· ∈ [Block.compCanon, Block.eqlevCanon, Block.gcaCanon,
          Block.eqlevFirst, Block.noncheaplevel, S.bp]) :=
        (hU4.sub (by simp)).trans (huf.sub (by simp))
      have iNC' := iNC.unch huf (by sep_notin hd)
      have iEF' := iEF.unch huf (by sep_notin hd)
      have iGC' := iGC.unch huf (by sep_notin hd)
      have aP' := aP.unch huf (by sep_notin hd)
      obtain ⟨hFs, hFv⟩ := reopen_fold (level := level) hinv.ptnSize hpv n
      refine ⟨mf, Nextelement.free_empty mf, rfl, ?_, ?_⟩
      · simp only [Hex.GraphIso.Nauty.recover]
        rw [recoverLevels_upd, recoverPtn_eq]
        exact
          { fixed := h.fixed.unch hUf (by sep_all hd)
            scalars :=
              ⟨h.scalars.gcaFirst.unch hUf (by sep_notin hd),
               show IntAt mf _ ((if level < st.gcaCanon then level else st.gcaCanon : Nat) : Int) from
                 IntAt.ite_nat iGC',
               show IntAt mf _ ((if level < st.noncheaplevel then level + 1 else st.noncheaplevel :
                   Nat) : Int) by
                 by_cases hc : level < st.noncheaplevel
                 · simp only [hc, decide_true, ite_true] at iNC' ⊢; push_cast; exact iNC'
                 · simp only [hc, decide_false, Bool.false_eq_true, ite_false] at iNC' ⊢; exact iNC',
               h.scalars.allsamelevel.unch hUf (by sep_notin hd),
               show IntAt mf _ ((if level < st.eqlevFirst then level else st.eqlevFirst : Nat) : Int) from
                 IntAt.ite_nat iEF',
               iEC, iCC,
               h.scalars.samerows.unch hUf (by sep_notin hd),
               h.scalars.canonlevel.unch hUf (by sep_notin hd),
               h.scalars.stabvertex.unch hUf (by sep_notin hd),
               h.scalars.cosetindex.unch hUf (by sep_notin hd),
               h.scalars.needshortprune.unch hUf (by sep_notin hd)⟩
            stats := ⟨h.stats.numorbits.unch hUf (by sep_notin hd),
              h.stats.numgenerators.unch hUf (by sep_notin hd),
              h.stats.numnodes.unch hUf (by sep_notin hd),
              h.stats.numbadleaves.unch hUf (by sep_notin hd),
              fun hp => (h.stats.maxlevel hp).unch hUf (by sep_notin hd),
              hUf.access _ _ _ _ (by sep_notin hd) h.stats.maxlevelW,
              h.stats.tctotal.unch hUf (by sep_notin hd),
              h.stats.canupdates.unch hUf (by sep_notin hd), h.stats.fits⟩
            arrays :=
              { lab := h.arrays.lab.unch hUf (by sep_notin hd)
                ptn := aP'
                orbits := h.arrays.orbits.unch hUf (by sep_notin hd)
                active := let ⟨aw, ha, hr⟩ := h.arrays.active
                  ⟨aw, ha.unch hUf (by sep_notin hd), hr⟩
                fixedpts := let ⟨fw, hf, hr⟩ := h.arrays.fixedpts
                  ⟨fw, hf.unch hUf (by sep_notin hd), hr⟩
                workperm := h.arrays.workperm.unch hUf (by sep_notin hd)
                firstlab := h.arrays.firstlab.unch hUf (by sep_notin hd)
                canonlab := h.arrays.canonlab.unch hUf (by sep_notin hd)
                firstcode := h.arrays.firstcode.unch hUf (by sep_notin hd)
                canoncode := h.arrays.canoncode.unch hUf (by sep_notin hd)
                firsttc := h.arrays.firsttc.unch hUf (by sep_notin hd)
                canong := h.arrays.canong.unch hUf (by sep_notin hd)
                autos := h.arrays.autos.unch hUf (by sep_notin hd) (by sep_notin hd)
                graph := ⟨h.arrays.graph.arr.unch hUf (by sep_notin hd), h.arrays.graph.rep⟩ }
            dyns := h.dyns.unch hUf (by sep_all hd)
            work := h.work.unch hUf (by sep_all hd) fun z hz hm => h.work_not hz (by
              clear hz; revert hm; revert z; simp [SLoc.blocks])
            tables := h.tables.unch hUf (by sep_all hd)
            distinct := hd
            inv :=
              { hinv with
                ptnSize := hFs
                ptnVals := hFv
                ptnLast := by
                  rw [reopen_fold_le (show st.ptn[n - 1]! ≤ level by rw [hinv.ptnLast]; omega)]
                  exact hinv.ptnLast
                scalars := by
                  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hinv.scalars
                  refine ⟨b1, ?_, ?_, b4, ?_, ?_, ?_, ?_, ?_, b10, b11, b12⟩ <;> dsimp only <;>
                    split <;> (try simp only [Int.ofNat_eq_natCast]) <;> omega }
            n0 := h.n0, nlt := h.nlt, nM := h.nM, M1 := h.M1, Mlt := h.Mlt }
      · exact ⟨hUf.mono fun z hz => .inl (by revert hz; revert z; simp [SLoc.blocks]),
          fun z hz => hvf _ (hv4 _ (hv3 _ (hv2 _ (hv1 _ hz))))⟩
    -- `if (level <= eqlev_canon) { eqlev_canon = level; comp_canon = 0; }`
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, eval_gint (e := empty_env) (le := le1) rfl find_eqlevCanon
      (h.scalars.eqlevCanon.unch hU4 (by sep_notin hd)),
      show Exec.evalExpr ge empty_env le1 m4 (tv dense.id.level) = _ from hlev1]
    simp only [typeof, cop]
    rw [ir_lt (a := st.eqlevCanon) (b := (level : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hc : (level : Int) ≤ st.eqlevCanon
    · rw [ite_eq_left (by simp; omega)]
      wp_step; wp_step; wp_step
      refine wp_gint (x := level) rfl find_eqlevCanon
        (h.scalars.eqlevCanon.unch hU4 (by sep_notin hd)).writable hlev1 rfl ?_
      intro m5 i5 hu5 hv5
      simp only [seqPost, Post.after, E0_append]
      wp_step; wp_step
      refine wp_gint (x := 0) rfl find_compCanon
        ((h.scalars.compCanon.unch hU4 (by sep_notin hd)).unch hu5 (by sep_ne hd)).writable
        (by simp only [Exec.evalExpr]) rfl ?_
      intro m6 i6 hu6 hv6
      simp only [E0_append]
      exact fin m6 (by rw [ite_eq_left hc]; exact i5.unch hu6 (by sep_ne hd)) (by rw [ite_eq_left hc]; exact i6)
        (((Unch.refl m4 (· ∈ ([] : List block))).snoc hu5).snoc hu6)
        (fun z hz => hv6 _ (hv5 _ hz))
    · rw [ite_eq_right (by simp; omega)]
      apply wp_skip
      exact fin m4 (by rw [ite_eq_right hc]; exact h.scalars.eqlevCanon.unch hU4 (by sep_notin hd))
        (by rw [ite_eq_right hc]; exact h.scalars.compCanon.unch hU4 (by sep_notin hd))
        (Unch.refl _ _) (fun _ h => h)

end NautyVerified.Proofs.Search.Recover

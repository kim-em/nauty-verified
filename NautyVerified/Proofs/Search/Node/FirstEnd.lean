import NautyVerified.Proofs.Search.Node.FirstLoop

/-!
# The end of `firstpathnode0`'s sweep

After the child loop, `firstpathnode0` runs
`MULTIPLY(stats->grpsize1, stats->grpsize2, index)`, decrements `allsamelevel`
when every vertex of the target cell was in `tv1`'s orbit and `allsamelevel`
is `level + 1` (HexGraphIso's `afterSweep true`), skips the marker and
`userlevelproc` (`domarkers` is 0, `userlevelproc` is `NULL`), and returns
`level - 1`.

`SearchAt.storeLow`: a store into `statsblk` below offset 12 (the group size
`grpsize1`, `grpsize2`) keeps `SearchAt`. `wp_fpnGrp`: the `MULTIPLY`.
`wp_fpnEnd`: the whole end.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open Hex.GraphIso Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}

/-- A store into `statsblk` below offset 12 keeps `SearchAt`, given the group
size afterwards. -/
theorem SearchAt.storeLow {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    (h : SearchAt m S ctx st pre nsp) {c : memory_chunk} {off : Int} {w : val}
    (hst : Mem.store c m S.bst (zOfInt (S.sb + off)) w = some m') (hoff : off + csize c ≤ 12)
    (g1 : ∃ x, FieldAt m' .Mfloat64 S.bst S.sb (.Vfloat x))
    (g2 : ∃ i, FieldAt m' .Mint32 S.bst (S.sb + 8) (.Vint i)) :
    SearchAt m' S ctx st pre nsp := by
  have hu : Unch m m' (· = S.bst) := Unch.store hst rfl
  have hd := h.distinct
  have hs := h.stats
  exact
    { fixed := h.fixed.unch hu (by sep_all hd)
      scalars := { h.scalars.unch hu (by sep_all hd) with }
      stats :=
        { numorbits := hs.numorbits.store_other hst (by omega)
          numgenerators := hs.numgenerators.store_other hst (by omega)
          numnodes := hs.numnodes.store_other hst (by omega)
          numbadleaves := hs.numbadleaves.store_other hst (by omega)
          maxlevel := fun hp => (hs.maxlevel hp).store_other hst (by omega)
          maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hs.maxlevelW
          tctotal := hs.tctotal.store_other hst (by omega)
          canupdates := hs.canupdates.store_other hst (by omega)
          fits := hs.fits
          perm := fun o ho => Mem.perm_store_1 _ _ _ _ _ _ hst _ _ _ _ (hs.perm o ho)
          errstatus := hs.errstatus.store_other hst (by omega)
          grpsize1 := g1
          grpsize2 := g2 }
      arrays := { h.arrays.unch hu (by sep_all hd) with }
      dyns := h.dyns.unch hu (by sep_all hd)
      work := h.work.unch hu (by sep_all hd) fun z hz hm => h.work_not hz (by
        rw [hm]; simp [SLoc.blocks])
      tables := h.tables.unch hu (by sep_all hd)
      distinct := hd
      inv := { h.inv with }
      n0 := h.n0, nlt := h.nlt, nM := h.nM, M1 := h.M1, Mlt := h.Mlt }

/-- `t718 = stats->grpsize1 * index; stats->grpsize1 = t718;` and the
normalisation `if (t718 >= 1e10) { grpsize1 /= 1e10; grpsize2 += 10; }`. -/
abbrev fpnGrp : statement :=
  .Ssequence
    (.Ssequence
      (Set.sk (.Sset (idOf 718) (.Ecast (.Ebinop .Omul (statsF dense.id.«grpsize1» tdouble)
        (Refine.tv dense.id.«index») tdouble) tdouble)))
      (.Sassign (statsF dense.id.«grpsize1» tdouble) (.Etempvar (idOf 718) tdouble)))
    Firstpathnode.grpsize

set_option maxHeartbeats 4000000 in
theorem wp_fpnGrp {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hge : PTree.get dense.id.«nauty:stats» e = none) {idx : Nat}
    (hidx : PTree.get dense.id.«index» le = some (.Vint (ir idx)))
    (hQ : ∀ le' m', SearchAt m' S ctx st pre nsp → Unch m m' (· = S.bst) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 718 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f fpnGrp Q e le m := by
  have hfit := h.stats.fits
  obtain ⟨x, hx⟩ := h.stats.grpsize1
  obtain ⟨i, hi⟩ := h.stats.grpsize2
  have hx' : FieldAt m .Mfloat64 S.bst (S.sb + 0) (.Vfloat x) := by simpa using hx
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, Exec.evalExpr, eval_statsF hge field_statsGrpsize1 rfl h.fixed.stats (by decide) (by omega) hx']
  simp only [Exec.evalExpr, Refine.tv, hidx, typeof, Cfrontend.Cop.sem_binary_operation,
    Cfrontend.Cop.sem_mul, Cfrontend.Cop.sem_binarith, Cfrontend.Cop.classify_binarith,
    Cfrontend.Cop.binarith_type, Cfrontend.Cop.sem_cast, Cfrontend.Cop.classify_cast]
  have hw0 := hx.writable
  rw [show S.sb = S.sb + 0 by omega] at hw0
  refine wp_statsStore (off := 0) (chunk := .Mfloat64) hge field_statsGrpsize1 rfl h.fixed.stats
    (by decide) (by omega) hw0 (by rw [Exec.evalExpr, temps_gss]) rfl ?_
  intro m₁ hs₁
  have hy₁ := FieldAt.store_same hs₁ hw0
  have c64 : csize .Mfloat64 = 8 := rfl
  have c32 : csize .Mint32 = 4 := rfl
  have hi₁ : FieldAt m₁ .Mint32 S.bst (S.sb + 8) (.Vint i) := hi.store_other hs₁ (by right; omega)
  have hy₁' := hy₁
  rw [Int.add_zero] at hy₁'
  have h₁ := h.storeLow hs₁ (by decide) ⟨_, hy₁'⟩ ⟨i, hi₁⟩
  have hu₁ : Unch m m₁ (· = S.bst) := Unch.store hs₁ rfl
  have hg₁ := fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hs₁ z hz
  simp only [Firstpathnode.grpsize]
  refine Processnode.wp_ifB (by
    simp only [Exec.evalExpr, temps_gss, typeof, Cfrontend.Cop.sem_binary_operation,
      Cfrontend.Cop.sem_cmp, Cfrontend.Cop.classify_cmp, Cfrontend.Cop.sem_binarith,
      Cfrontend.Cop.classify_binarith, Cfrontend.Cop.binarith_type, Cfrontend.Cop.sem_cast,
      Cfrontend.Cop.classify_cast, Cfrontend.Ctypes.typeconv, Cfrontend.Ctypes.remove_attributes,
      Cfrontend.Ctypes.change_attributes]
    rfl) rfl ?_
  split
  · have hw1 := hy₁.writable
    wp_step; wp_step; wp_step
    refine wp_statsStore (off := 0) (chunk := .Mfloat64) hge field_statsGrpsize1 rfl h₁.fixed.stats
      (by decide) (by omega) hw1 (by
        rw [Exec.evalExpr, eval_statsF hge field_statsGrpsize1 rfl h₁.fixed.stats (by decide)
          (by omega) hy₁]
        simp only [Exec.evalExpr, typeof, Cfrontend.Cop.sem_binary_operation,
          Cfrontend.Cop.sem_div, Cfrontend.Cop.sem_binarith, Cfrontend.Cop.classify_binarith,
          Cfrontend.Cop.binarith_type, Cfrontend.Cop.sem_cast, Cfrontend.Cop.classify_cast,
          Val.load_result]
        rfl) rfl ?_
    intro m₂ hs₂
    have hy₂ := FieldAt.store_same hs₂ hw1
    have hi₂ : FieldAt m₂ .Mint32 S.bst (S.sb + 8) (.Vint i) := hi₁.store_other hs₂ (by right; omega)
    have hy₂' := hy₂
    rw [Int.add_zero] at hy₂'
    have h₂ := h₁.storeLow hs₂ (by decide) ⟨_, hy₂'⟩ ⟨i, hi₂⟩
    have hu₂ : Unch m₁ m₂ (· = S.bst) := Unch.store hs₂ rfl
    have hg₂ := fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hs₂ z hz
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    refine wp_statsStore (off := 8) (chunk := .Mint32) hge field_statsGrpsize2 rfl h₂.fixed.stats
      (by decide) (by omega) hi₂.writable (by
        rw [Exec.evalExpr, eval_statsF hge field_statsGrpsize2 rfl h₂.fixed.stats (by decide)
          (by omega) hi₂]
        simp only [Exec.evalExpr, typeof, cop]
        rfl) rfl ?_
    intro m₃ hs₃
    have hy₃ : FieldAt m₃ .Mfloat64 S.bst (S.sb + 0) _ := hy₂.store_other hs₃ (by left; omega)
    have hi₃ := FieldAt.store_same hs₃ hi₂.writable
    rw [Int.add_zero] at hy₃
    have h₃ := h₂.storeLow hs₃ (by decide) ⟨_, hy₃⟩
      ⟨_, (hi₃ : FieldAt m₃ .Mint32 S.bst (S.sb + 8) (.Vint _))⟩
    exact hQ _ m₃ h₃ ((hu₁.trans hu₂).trans (Unch.store hs₃ rfl))
      (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hs₃ z (hg₂ z (hg₁ z hz)))
      (fun x hx => temps_gso _ _ hx)
  · apply wp_skip
    exact hQ _ m₁ h₁ hu₁ hg₁ (fun x hx => temps_gso _ _ hx)


namespace Firstpathnode

open CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Refine (tv)

/-- After `MULTIPLY`: the `allsamelevel` update. -/
abbrev lastAllsame : statement :=
  (.Ssequence
    (sk allsame)
    (.Sifthenelse
      (tv (idOf 719))
      (sk
        (.Sassign
          (.Evar dense.id.«nauty:allsamelevel» tint)
          (.Ebinop .Osub
            (.Evar dense.id.«nauty:allsamelevel» tint)
            (ci 1 tint)
            tint)))
      .Sskip))

/-- The marker, `userlevelproc`, the return. -/
abbrev lastRet : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Evar dense.id.«nauty:domarkers» tint)
        (sk
          (.Scall none
            (.Evar dense.id.«nauty:writemarker»
              (tfun
                [tint, tint, tint, tint, tint, tint]
                .Tvoid))
            [(tv dense.id.«level»),
             (tv dense.id.«tv1»),
             (tv dense.id.«index»),
             (.Evar dense.id.«tcellsize» tint),
             (.Efield
               (.Ederef
                 (.Evar dense.id.«nauty:stats»
                   (tptr (Tstruct dense.id.«_1024» noattr)))
                 (Tstruct dense.id.«_1024» noattr))
               dense.id.«numorbits»
               tint),
             (.Evar dense.id.«numcells» tint)]))
        .Sskip))
    (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .One
            (.Evar dense.id.«nauty:userlevelproc»
              (tptr
                (tfun
                  [(tptr tint),
                   (tptr tint),
                   tint,
                   (tptr tint),
                   (tptr (Tstruct dense.id.«_1024» noattr)),
                   tint,
                   tint,
                   tint,
                   tint,
                   tint,
                   tint]
                  .Tvoid)))
            (.Ecast (ci 0 tint) (tptr .Tvoid))
            tint)
          (sk
            (.Scall none
              (.Ederef
                (.Evar dense.id.«nauty:userlevelproc»
                  (tptr
                    (tfun
                      [(tptr tint),
                       (tptr tint),
                       tint,
                       (tptr tint),
                       (tptr (Tstruct dense.id.«_1024» noattr)),
                       tint,
                       tint,
                       tint,
                       tint,
                       tint,
                       tint]
                      .Tvoid)))
                (tfun
                  [(tptr tint),
                   (tptr tint),
                   tint,
                   (tptr tint),
                   (tptr (Tstruct dense.id.«_1024» noattr)),
                   tint,
                   tint,
                   tint,
                   tint,
                   tint,
                   tint]
                  .Tvoid))
              [(.Etempvar dense.id.«lab» (tptr tint)),
               (.Etempvar dense.id.«ptn» (tptr tint)),
               (tv dense.id.«level»),
               (.Evar dense.id.«nauty:orbits» (tptr tint)),
               (.Evar dense.id.«nauty:stats»
                 (tptr (Tstruct dense.id.«_1024» noattr))),
               (tv dense.id.«tv1»),
               (tv dense.id.«index»),
               (.Evar dense.id.«tcellsize» tint),
               (.Evar dense.id.«numcells» tint),
               (tv dense.id.«childcount»),
               (.Evar dense.id.«nauty:n» tint)]))
          .Sskip))
      (sk
        (.Sreturn
          (some
            (.Ebinop .Osub (tv dense.id.«level») (ci 1 tint) tint))))))

abbrev last : statement := .Ssequence lastAllsame lastRet

end Firstpathnode

/-- `userlevelproc != NULL` when it is `NULL`. -/
theorem ne_null [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (ce : Cfrontend.Ctypes.composite_env) (m : mem) (t : Cfrontend.Ctypes.type) :
    Cfrontend.Cop.sem_binary_operation ce .One Vnullptr (tptr t)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
      (tptr .Tvoid) m = some (Val.of_bool false) := rfl

theorem SearchAt.setAllsame {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    (h : SearchAt m S ctx st pre nsp) (hU : Unch m m' (· ∈ [Block.allsamelevel])) {v : Nat}
    (iA : IntAt m' Block.allsamelevel (v : Int)) (hv : v < 2147483648) :
    SearchAt m' S ctx { st with allsamelevel := v } pre nsp := by
  have sc := h.scalars
  refine h.setScalars hU (fun z hz => by simp at hz; subst hz; decide)
    ⟨sc.gcaFirst.unch hU (by decide), sc.gcaCanon.unch hU (by decide),
      sc.noncheaplevel.unch hU (by decide), iA, sc.eqlevFirst.unch hU (by decide),
      sc.eqlevCanon.unch hU (by decide), sc.compCanon.unch hU (by decide),
      sc.samerows.unch hU (by decide), sc.canonlevel.unch hU (by decide),
      sc.stabvertex.unch hU (by decide), sc.cosetindex.unch hU (by decide),
      sc.needshortprune.unch hU (by decide)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, -, s5⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, hv, s5⟩ }

set_option maxHeartbeats 4000000 in
/-- `if (domarkers) …; if (userlevelproc != NULL) …; return level - 1;` -/
theorem wp_fpnRet {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (g2 : PTree.get dense.id.«nauty:domarkers» e = none)
    (g3 : PTree.get dense.id.«nauty:userlevelproc» e = none) {level : Nat}
    (hfr : f.fn_return = tint) (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hQ : match Mem.free_list m (blocks_of_env ge e) with
      | some m'' => Q.ret E0 (.Vint (ir ((level : Int) - 1))) m''
      | none => False) :
    Wp xi ge f Firstpathnode.lastRet Q e le m := by
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [eval_gint g2 find_domarkers h.fixed.domarkers]
  simp only [typeof]
  rw [show Cfrontend.Cop.bool_val (.Vint (ir 0)) tint m = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, g3, find_userlevelproc, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.userlevelproc.load, typeof]
  rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
    (tptr .Tvoid) m = some (.Vlong (Lib.Integers.Int64.repr
      (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0))))) from rfl]
  dsimp only
  rw [ne_null]
  dsimp only
  rw [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step
  apply wp_return_some_eval
  simp only [Exec.evalExpr, Refine.tv, hlev, typeof, cop, hfr]
  rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl, ir_sub]
  exact hQ

set_option maxHeartbeats 4000000 in
/-- `if (tcellsize == index && allsamelevel == level + 1) --allsamelevel;`: `afterSweep true`. -/
theorem wp_fpnAllsame {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (g1 : PTree.get dense.id.«nauty:allsamelevel» e = none)
    {level idx tcsize : Nat} {bz : block}
    (hez : PTree.get dense.id.«tcellsize» e = some (bz, tint))
    (hzv : Mem.load .Mint32 m bz (zOfInt 0) = some (.Vint (ir tcsize)))
    (hidx : PTree.get dense.id.«index» le = some (.Vint (ir idx)))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hz : tcsize ≤ n) (hi : idx ≤ n + 1) (hl : level ≤ n)
    (hQ : ∀ le' m', SearchAt m' S ctx (afterSweep true level tcsize idx st) pre nsp →
      Unch m m' (· ∈ [Block.allsamelevel]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 719 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f Firstpathnode.lastAllsame Q e le m := by
  have hnl := h.nlt
  obtain ⟨-, -, -, has, -⟩ := h.inv.scalars
  have hcast : ∀ b : Bool, Cfrontend.Cop.sem_cast (Val.of_bool b) tint tbool m =
      some (Val.of_bool b) := fun b => by cases b <;> rfl
  have tail : ∀ (le' : temp_env) (b : Bool), PTree.get (idOf 719) le' = some (Val.of_bool b) →
      (∀ x, x ≠ idOf 719 → PTree.get x le' = PTree.get x le) →
      afterSweep true level tcsize idx st =
        (if b then { st with allsamelevel := st.allsamelevel - 1 } else st) →
      (b = true → 1 ≤ st.allsamelevel) →
      Wp xi ge f (.Sifthenelse (Refine.tv (idOf 719))
        (Set.sk (.Sassign (.Evar dense.id.«nauty:allsamelevel» tint)
          (.Ebinop .Osub (.Evar dense.id.«nauty:allsamelevel» tint) (ci 1 tint) tint))) .Sskip)
        Q e le' m := by
    intro le' b h719 hle' hcc hb1
    apply wp_if_eval
    simp only [Exec.evalExpr, Refine.tv, h719, typeof]
    cases b
    · rw [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      apply wp_skip
      exact hQ le' m (by rw [hcc]; exact h) (Unch.refl _ _) (fun _ h => h) hle'
    · rw [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m = some true from rfl]
      simp only [ite_true]
      have h1 := hb1 rfl
      wp_step; wp_step
      refine wp_gint g1 find_allsamelevel h.scalars.allsamelevel.writable
        (x := ((st.allsamelevel - 1 : Nat) : Int))
        (by
          rw [Exec.evalExpr, eval_gint g1 find_allsamelevel h.scalars.allsamelevel]
          simp only [Exec.evalExpr, typeof, cop]
          rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl, ir_sub]
          congr 3; omega) rfl ?_
      intro m' iA hu hv
      have hU : Unch m m' (· ∈ [Block.allsamelevel]) := hu.mono fun z hz => by simp [hz]
      refine hQ le' m' ?_ hU hv hle'
      rw [hcc]
      exact h.setAllsame hU iA (by omega)
  wp_step
  wp_step; wp_step
  refine Processnode.wp_ifB (Processnode.eval_eqI (x := (tcsize : Int)) (y := (idx : Int))
    (eval_local hez hzv) (by simp [Exec.evalExpr, Refine.tv, hidx]) rfl rfl
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
  by_cases hb : tcsize = idx
  · rw [decide_eq_true (by omega)]
    simp only [ite_true]
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, Processnode.eval_eqI (x := (st.allsamelevel : Int)) (y := ((level + 1 : Nat) : Int))
      (eval_gint g1 find_allsamelevel h.scalars.allsamelevel)
      (by simp only [Exec.evalExpr, Refine.tv, hlev, typeof, cop]; simp) rfl rfl
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp only [typeof, hcast]
    have key := tail _ (decide ((st.allsamelevel : Int) = ((level + 1 : Nat) : Int))) (temps_gss _ _ _)
      (fun x hx => temps_gso _ _ hx)
      (by
        unfold afterSweep
        by_cases ha : st.allsamelevel = level + 1
        · simp [hb, ha]
        · simp [hb, ha]; intro h'; omega)
      (by intro hd; simp at hd; omega)
    simpa only [E0_append] using key
  · rw [decide_eq_false (by omega)]
    simp only [Bool.false_eq_true, ite_false]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    have key := tail (PTree.set (idOf 719) (.Vint (Lib.Integers.Int.repr (zOfInt 0))) le) false
      (by rw [temps_gss]; rfl) (fun x hx => temps_gso _ _ hx)
      (by unfold afterSweep; simp [hb]) (by simp)
    simpa only [E0_append] using key

set_option maxHeartbeats 4000000 in
/-- The rest of the node after `MULTIPLY` is `afterSweep true`, then `return level - 1`. -/
theorem wp_fpnLast {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} (h : SearchAt m S ctx st pre nsp)
    (hge : ∀ x ∈ [dense.id.«nauty:allsamelevel», dense.id.«nauty:domarkers»,
      dense.id.«nauty:userlevelproc»], PTree.get x e = none)
    {level idx tcsize : Nat} {bz : block} (hfr : f.fn_return = tint)
    (hez : PTree.get dense.id.«tcellsize» e = some (bz, tint))
    (hzv : Mem.load .Mint32 m bz (zOfInt 0) = some (.Vint (ir tcsize)))
    (hidx : PTree.get dense.id.«index» le = some (.Vint (ir idx)))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hz : tcsize ≤ n) (hi : idx ≤ n + 1) (hl : level ≤ n)
    (hQ : ∀ m', SearchAt m' S ctx (afterSweep true level tcsize idx st) pre nsp →
      Unch m m' (· ∈ [Block.allsamelevel]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret E0 (.Vint (ir ((level : Int) - 1))) m''
      | none => False) :
    Wp xi ge f Firstpathnode.last Q e le m := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hge
  obtain ⟨g1, g2, g3⟩ := hge
  wp_step
  refine wp_fpnAllsame h g1 hez hzv hidx hlev hz hi hl ?_
  intro le' m' h' hu hv hle
  simp only [seqPost, Post.after, E0_append]
  exact wp_fpnRet h' g2 g3 hfr (by rw [hle _ (by decide)]; exact hlev) (hQ m' h' hu hv)

/-! ### For any dispatch representation -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- `SearchAt.storeLow` for `D`. -/
theorem SearchAtG.storeLow {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) {c : memory_chunk} {off : Int} {w : val}
    (hst : Mem.store c m S.bst (zOfInt (S.sb + off)) w = some m') (hoff : off + csize c ≤ 12)
    (g1 : ∃ x, FieldAt m' .Mfloat64 S.bst S.sb (.Vfloat x))
    (g2 : ∃ i, FieldAt m' .Mint32 S.bst (S.sb + 8) (.Vint i)) :
    SearchAtG D m' S gl cl G st pre nsp := by
  have hu : Unch m m' (· = S.bst) := Unch.store hst rfl
  have hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z :=
    fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz
  have hd := h.lit
  have hs := h.stats
  refine h.rebuild (L := [S.bst]) (hu.mono fun z hz => by simp [hz]) (by simp)
    (fun z hz => Alloc.Keep.unch hu (by revert z hz; sep_all hd)) hv
    { h.scalars.unch hu (by sep_all hd) with }
    { numorbits := hs.numorbits.store_other hst (by omega)
      numgenerators := hs.numgenerators.store_other hst (by omega)
      numnodes := hs.numnodes.store_other hst (by omega)
      numbadleaves := hs.numbadleaves.store_other hst (by omega)
      maxlevel := fun hp => (hs.maxlevel hp).store_other hst (by omega)
      maxlevelW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ hs.maxlevelW
      tctotal := hs.tctotal.store_other hst (by omega)
      canupdates := hs.canupdates.store_other hst (by omega)
      fits := hs.fits
      perm := fun o ho => Mem.perm_store_1 _ _ _ _ _ _ hst _ _ _ _ (hs.perm o ho)
      errstatus := hs.errstatus.store_other hst (by omega)
      grpsize1 := g1
      grpsize2 := g2 }
    { h.arrays.unch hu (by sep_all hd) (fun z hz e => h.graph_ne hz (.inl (by simp)) e)
      (fun z hz e => h.canon_ne hz (.inr (.inl (by simp))) e) with }
    { h.inv with }

set_option maxHeartbeats 4000000 in
/-- `wp_fpnGrp` for `D`. -/
theorem wp_fpnGrpG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hge : PTree.get dense.id.«nauty:stats» e = none) {idx : Nat}
    (hidx : PTree.get dense.id.«index» le = some (.Vint (ir idx)))
    (hQ : ∀ le' m', SearchAtG D m' S gl cl G st pre nsp → Unch m m' (· = S.bst) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 718 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f fpnGrp Q e le m := by
  have hfit := h.stats.fits
  obtain ⟨x, hx⟩ := h.stats.grpsize1
  obtain ⟨i, hi⟩ := h.stats.grpsize2
  have hx' : FieldAt m .Mfloat64 S.bst (S.sb + 0) (.Vfloat x) := by simpa using hx
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, Exec.evalExpr, eval_statsF hge E.field_statsGrpsize1 rfl h.fixed.stats
    (by decide) (by omega) hx']
  simp only [Exec.evalExpr, Refine.tv, hidx, typeof, Cfrontend.Cop.sem_binary_operation,
    Cfrontend.Cop.sem_mul, Cfrontend.Cop.sem_binarith, Cfrontend.Cop.classify_binarith,
    Cfrontend.Cop.binarith_type, Cfrontend.Cop.sem_cast, Cfrontend.Cop.classify_cast]
  have hw0 := hx.writable
  rw [show S.sb = S.sb + 0 by omega] at hw0
  refine wp_statsStore (off := 0) (chunk := .Mfloat64) hge E.field_statsGrpsize1 rfl h.fixed.stats
    (by decide) (by omega) hw0 (by rw [Exec.evalExpr, temps_gss]) rfl ?_
  intro m₁ hs₁
  have hy₁ := FieldAt.store_same hs₁ hw0
  have c64 : csize .Mfloat64 = 8 := rfl
  have c32 : csize .Mint32 = 4 := rfl
  have hi₁ : FieldAt m₁ .Mint32 S.bst (S.sb + 8) (.Vint i) := hi.store_other hs₁ (by right; omega)
  have hy₁' := hy₁
  rw [Int.add_zero] at hy₁'
  have h₁ := h.storeLow hs₁ (by decide) ⟨_, hy₁'⟩ ⟨i, hi₁⟩
  have hu₁ : Unch m m₁ (· = S.bst) := Unch.store hs₁ rfl
  have hg₁ := fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hs₁ z hz
  simp only [Firstpathnode.grpsize]
  refine Processnode.wp_ifB (by
    simp only [Exec.evalExpr, temps_gss, typeof, Cfrontend.Cop.sem_binary_operation,
      Cfrontend.Cop.sem_cmp, Cfrontend.Cop.classify_cmp, Cfrontend.Cop.sem_binarith,
      Cfrontend.Cop.classify_binarith, Cfrontend.Cop.binarith_type, Cfrontend.Cop.sem_cast,
      Cfrontend.Cop.classify_cast, Cfrontend.Ctypes.typeconv, Cfrontend.Ctypes.remove_attributes,
      Cfrontend.Ctypes.change_attributes]
    rfl) rfl ?_
  split
  · have hw1 := hy₁.writable
    wp_step; wp_step; wp_step
    refine wp_statsStore (off := 0) (chunk := .Mfloat64) hge E.field_statsGrpsize1 rfl
      h₁.fixed.stats (by decide) (by omega) hw1 (by
        rw [Exec.evalExpr, eval_statsF hge E.field_statsGrpsize1 rfl h₁.fixed.stats (by decide)
          (by omega) hy₁]
        simp only [Exec.evalExpr, typeof, Cfrontend.Cop.sem_binary_operation,
          Cfrontend.Cop.sem_div, Cfrontend.Cop.sem_binarith, Cfrontend.Cop.classify_binarith,
          Cfrontend.Cop.binarith_type, Cfrontend.Cop.sem_cast, Cfrontend.Cop.classify_cast,
          Val.load_result]
        rfl) rfl ?_
    intro m₂ hs₂
    have hy₂ := FieldAt.store_same hs₂ hw1
    have hi₂ : FieldAt m₂ .Mint32 S.bst (S.sb + 8) (.Vint i) := hi₁.store_other hs₂ (by right; omega)
    have hy₂' := hy₂
    rw [Int.add_zero] at hy₂'
    have h₂ := h₁.storeLow hs₂ (by decide) ⟨_, hy₂'⟩ ⟨i, hi₂⟩
    have hu₂ : Unch m₁ m₂ (· = S.bst) := Unch.store hs₂ rfl
    have hg₂ := fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hs₂ z hz
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    refine wp_statsStore (off := 8) (chunk := .Mint32) hge E.field_statsGrpsize2 rfl h₂.fixed.stats
      (by decide) (by omega) hi₂.writable (by
        rw [Exec.evalExpr, eval_statsF hge E.field_statsGrpsize2 rfl h₂.fixed.stats (by decide)
          (by omega) hi₂]
        simp only [Exec.evalExpr, typeof, cop]
        rfl) rfl ?_
    intro m₃ hs₃
    have hy₃ : FieldAt m₃ .Mfloat64 S.bst (S.sb + 0) _ := hy₂.store_other hs₃ (by left; omega)
    have hi₃ := FieldAt.store_same hs₃ hi₂.writable
    rw [Int.add_zero] at hy₃
    have h₃ := h₂.storeLow hs₃ (by decide) ⟨_, hy₃⟩
      ⟨_, (hi₃ : FieldAt m₃ .Mint32 S.bst (S.sb + 8) (.Vint _))⟩
    exact hQ _ m₃ h₃ ((hu₁.trans hu₂).trans (Unch.store hs₃ rfl))
      (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hs₃ z (hg₂ z (hg₁ z hz)))
      (fun x hx => temps_gso _ _ hx)
  · apply wp_skip
    exact hQ _ m₁ h₁ hu₁ hg₁ (fun x hx => temps_gso _ _ hx)

theorem SearchAtG.setAllsame {m m' : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
    {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp) (hU : Unch m m' (· ∈ [E.allsamelevel]))
    (hv : ∀ z, Mem.valid_block m z → Mem.valid_block m' z) {v : Nat}
    (iA : IntAt m' E.allsamelevel (v : Int)) (hv2 : v < 2147483648) :
    SearchAtG D m' S gl cl G { st with allsamelevel := v } pre nsp := by
  have sc := h.scalars
  refine h.setScalars hU (fun z hz => by simp at hz; subst hz; simp) hv
    ⟨sc.gcaFirst.unch hU (by sep_notin h.lit), sc.gcaCanon.unch hU (by sep_notin h.lit),
      sc.noncheaplevel.unch hU (by sep_notin h.lit), iA, sc.eqlevFirst.unch hU (by sep_notin h.lit),
      sc.eqlevCanon.unch hU (by sep_notin h.lit), sc.compCanon.unch hU (by sep_notin h.lit),
      sc.samerows.unch hU (by sep_notin h.lit), sc.canonlevel.unch hU (by sep_notin h.lit),
      sc.stabvertex.unch hU (by sep_notin h.lit), sc.cosetindex.unch hU (by sep_notin h.lit),
      sc.needshortprune.unch hU (by sep_notin h.lit)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, s3, -, s5⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, s3, hv2, s5⟩ }

set_option maxHeartbeats 4000000 in
/-- `wp_fpnRet` for `D`. -/
theorem wp_fpnRetG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (g2 : PTree.get dense.id.«nauty:domarkers» e = none)
    (g3 : PTree.get dense.id.«nauty:userlevelproc» e = none) {level : Nat}
    (hfr : f.fn_return = tint) (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hQ : match Mem.free_list m (blocks_of_env ge e) with
      | some m'' => Q.ret E0 (.Vint (ir ((level : Int) - 1))) m''
      | none => False) :
    Wp xi ge f Firstpathnode.lastRet Q e le m := by
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [eval_gint g2 E.find_domarkers h.fixed.domarkers]
  simp only [typeof]
  rw [show Cfrontend.Cop.bool_val (.Vint (ir 0)) tint m = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, g3, E.find_userlevelproc, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.userlevelproc.load, typeof]
  rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint
    (tptr .Tvoid) m = some (.Vlong (Lib.Integers.Int64.repr
      (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0))))) from rfl]
  dsimp only
  rw [ne_null]
  dsimp only
  rw [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step
  apply wp_return_some_eval
  simp only [Exec.evalExpr, Refine.tv, hlev, typeof, cop, hfr]
  rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl, ir_sub]
  exact hQ

set_option maxHeartbeats 4000000 in
/-- `wp_fpnAllsame` for `D`: HexGraphIso's `afterSweep true`. -/
theorem wp_fpnAllsameG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (g1 : PTree.get dense.id.«nauty:allsamelevel» e = none)
    {level idx tcsize : Nat} {bz : block}
    (hez : PTree.get dense.id.«tcellsize» e = some (bz, tint))
    (hzv : Mem.load .Mint32 m bz (zOfInt 0) = some (.Vint (ir tcsize)))
    (hidx : PTree.get dense.id.«index» le = some (.Vint (ir idx)))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hz : tcsize ≤ n) (hi : idx ≤ n + 1) (hl : level ≤ n)
    (hQ : ∀ le' m', SearchAtG D m' S gl cl G (afterSweep true level tcsize idx st) pre nsp →
      Unch m m' (· ∈ [E.allsamelevel]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 719 → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp xi ge f Firstpathnode.lastAllsame Q e le m := by
  have hnl := h.nlt
  obtain ⟨-, -, -, has, -⟩ := h.inv.scalars
  have hcast : ∀ b : Bool, Cfrontend.Cop.sem_cast (Val.of_bool b) tint tbool m =
      some (Val.of_bool b) := fun b => by cases b <;> rfl
  have tail : ∀ (le' : temp_env) (b : Bool), PTree.get (idOf 719) le' = some (Val.of_bool b) →
      (∀ x, x ≠ idOf 719 → PTree.get x le' = PTree.get x le) →
      afterSweep true level tcsize idx st =
        (if b then { st with allsamelevel := st.allsamelevel - 1 } else st) →
      (b = true → 1 ≤ st.allsamelevel) →
      Wp xi ge f (.Sifthenelse (Refine.tv (idOf 719))
        (Set.sk (.Sassign (.Evar dense.id.«nauty:allsamelevel» tint)
          (.Ebinop .Osub (.Evar dense.id.«nauty:allsamelevel» tint) (ci 1 tint) tint))) .Sskip)
        Q e le' m := by
    intro le' b h719 hle' hcc hb1
    apply wp_if_eval
    simp only [Exec.evalExpr, Refine.tv, h719, typeof]
    cases b
    · rw [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      apply wp_skip
      exact hQ le' m (by rw [hcc]; exact h) (Unch.refl _ _) (fun _ h => h) hle'
    · rw [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m = some true from rfl]
      simp only [ite_true]
      have h1 := hb1 rfl
      wp_step; wp_step
      refine wp_gint g1 E.find_allsamelevel h.scalars.allsamelevel.writable
        (x := ((st.allsamelevel - 1 : Nat) : Int))
        (by
          rw [Exec.evalExpr, eval_gint g1 E.find_allsamelevel h.scalars.allsamelevel]
          simp only [Exec.evalExpr, typeof, cop]
          rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl, ir_sub]
          congr 3; omega) rfl ?_
      intro m' iA hu hv
      have hU : Unch m m' (· ∈ [E.allsamelevel]) := hu.mono fun z hz => by simp [hz]
      refine hQ le' m' ?_ hU hv hle'
      rw [hcc]
      exact h.setAllsame hU hv iA (by omega)
  wp_step
  wp_step; wp_step
  refine Processnode.wp_ifB (Processnode.eval_eqI (x := (tcsize : Int)) (y := (idx : Int))
    (eval_local hez hzv) (by simp [Exec.evalExpr, Refine.tv, hidx]) rfl rfl
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩) rfl ?_
  by_cases hb : tcsize = idx
  · rw [decide_eq_true (by omega)]
    simp only [ite_true]
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, Processnode.eval_eqI (x := (st.allsamelevel : Int)) (y := ((level + 1 : Nat) : Int))
      (eval_gint g1 E.find_allsamelevel h.scalars.allsamelevel)
      (by simp only [Exec.evalExpr, Refine.tv, hlev, typeof, cop]; simp) rfl rfl
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp only [typeof, hcast]
    have key := tail _ (decide ((st.allsamelevel : Int) = ((level + 1 : Nat) : Int))) (temps_gss _ _ _)
      (fun x hx => temps_gso _ _ hx)
      (by
        unfold afterSweep
        by_cases ha : st.allsamelevel = level + 1
        · simp [hb, ha]
        · simp [hb, ha]; intro h'; omega)
      (by intro hd; simp at hd; omega)
    simpa only [E0_append] using key
  · rw [decide_eq_false (by omega)]
    simp only [Bool.false_eq_true, ite_false]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    have key := tail (PTree.set (idOf 719) (.Vint (Lib.Integers.Int.repr (zOfInt 0))) le) false
      (by rw [temps_gss]; rfl) (fun x hx => temps_gso _ _ hx)
      (by unfold afterSweep; simp [hb]) (by simp)
    simpa only [E0_append] using key

set_option maxHeartbeats 4000000 in
/-- `wp_fpnLast` for `D`. -/
theorem wp_fpnLastG {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)} {pre nsp : Bool}
    (h : SearchAtG D m S gl cl G st pre nsp)
    (hge : ∀ x ∈ [dense.id.«nauty:allsamelevel», dense.id.«nauty:domarkers»,
      dense.id.«nauty:userlevelproc»], PTree.get x e = none)
    {level idx tcsize : Nat} {bz : block} (hfr : f.fn_return = tint)
    (hez : PTree.get dense.id.«tcellsize» e = some (bz, tint))
    (hzv : Mem.load .Mint32 m bz (zOfInt 0) = some (.Vint (ir tcsize)))
    (hidx : PTree.get dense.id.«index» le = some (.Vint (ir idx)))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hz : tcsize ≤ n) (hi : idx ≤ n + 1) (hl : level ≤ n)
    (hQ : ∀ m', SearchAtG D m' S gl cl G (afterSweep true level tcsize idx st) pre nsp →
      Unch m m' (· ∈ [E.allsamelevel]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret E0 (.Vint (ir ((level : Int) - 1))) m''
      | none => False) :
    Wp xi ge f Firstpathnode.last Q e le m := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hge
  obtain ⟨g1, g2, g3⟩ := hge
  wp_step
  refine wp_fpnAllsameG h g1 hez hzv hidx hlev hz hi hl ?_
  intro le' m' h' hu hv hle
  simp only [seqPost, Post.after, E0_append]
  exact wp_fpnRetG h' g2 g3 hfr (by rw [hle _ (by decide)]; exact hlev) (hQ m' h' hu hv)

end Generic

end NautyVerified.Proofs.Search

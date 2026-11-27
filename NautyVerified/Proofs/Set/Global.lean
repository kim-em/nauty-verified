import NautyVerified.Proofs.Set.Add
import NautyVerified.Proofs.Alloc.Global

/-!
# Set macros on a static set pointer

nauty's `DYNALLSTAT` sets (`workset` in naugraph.c) are reached through a
pointer global `g`, reloaded at each use. `emptySetG g m es t` is
`EMPTYSET(g, m)` and `addElementG g bitId a` is `ADDELEMENT(g, a)` reading the
`bit` table `bitId` (each translation unit has its own copy). The lemmas take
the global's block `bg`, holding `Vptr ba ofs`, and the set's block `ba`
distinct from it; besides `Unch` and `Outside` they give `Keep` for `ba`, so a
`DynAt` for the set survives.
-/

namespace NautyVerified.Proofs.Set

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Alloc (Keep)

variable {xi : ExternalCalls}

/-- `(set *) g`. -/
abbrev gpvC (g : Common.AST.ident) : expr := .Ecast (.Evar g (tptr tulong)) (tptr tulong)

/-- `EMPTYSET(g, m)` for a pointer global `g`. -/
abbrev emptySetG (g m es t : Common.AST.ident) : statement :=
  .Ssequence
    (sk (.Sset es (.Ebinop .Oadd (gpvC g) (.Etempvar m tint) (tptr tulong))))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Ogt (pv es) (gpvC g) tint) .Sskip .Sbreak))
        (.Ssequence
          (.Ssequence
            (sk (.Sset t (.Ecast (.Ebinop .Osub (pv es) (ci 1 tint) (tptr tulong)) (tptr tulong))))
            (.Sset es (pv t)))
          (.Sassign (.Ederef (pv t) tulong) (ci 0 tint))))
      .Sskip)

/-- `g[a >> 6]` for a pointer global `g`. -/
abbrev setWordG (g : Common.AST.ident) (a : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar g (tptr tulong)) (.Ebinop .Oshr a (ci 6 tint) tint) (tptr tulong)) tulong

/-- `ADDELEMENT(g, a)` for a pointer global `g`, with the `bit` table `bitId`. -/
abbrev addElementG (g bitId : Common.AST.ident) (a : expr) : statement :=
  sk (.Sassign (setWordG g a)
    (.Ebinop .Oor (setWordG g a)
      (.Ederef (.Ebinop .Oadd (.Evar bitId (tarray tulong 64))
        (.Ebinop .Oand a (ci 63 tint) tint) (tptr tulong)) tulong) tulong))

/-- Reading the pointer global `g`. -/
theorem eval_gptr {e : env} {le : temp_env} {m : mem} {g : Common.AST.ident} {bg ba : block}
    {ofs : ptrofs} (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr ba ofs)) :
    Exec.evalExpr ge e le m (.Evar g (tptr tulong)) = some (.Vptr ba ofs) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg]
  simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp]

theorem wp_emptySetG {g mv es tmp : Common.AST.ident} (het : es ≠ tmp) {f : function} {Q : Post}
    {e : env} {le : temp_env} {m : mem} {bg ba : block} {ofs : ptrofs} {vals : Nat → val} {M : Nat}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr ba ofs)) (hbg : bg ≠ ba)
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) vals M) (hM : 0 < M)
    (hM2 : M < 2147483648) (hm : PTree.get mv le = some (.Vint (ir M)))
    (hQ : ∀ le' m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs fun _ => lr 0) M →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * M) →
      Keep m m' ba →
      (∀ k, k ≠ es → k ≠ tmp → PTree.get k le' = PTree.get k le) → Q.normal E0 e le' m') :
    Wp xi ge f (emptySetG g mv es tmp) Q e le m := by
  have hf := harr.fits
  have hb := harr.base_nonneg
  have h8 : csize .Mint64 = 8 := rfl
  rw [h8] at hf
  simp only [emptySetG, sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg, Exec.derefLoc, Cfrontend.Ctypes.access_mode,
    Mem.loadv, Alloc.Mptr_eq, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp, hm,
    typeof, cop]
  rw [add_ptrTo ofs _ M (by omega), sizeof_tulong]
  simp only [E0_append]
  let base := intOfZ (Ptrofs.unsigned ofs)
  refine wp_loop (I := fun k t e' le' m' => t = E0 ∧ e = e' ∧ k ≤ M ∧
      PTree.get es le' = some (.Vptr ba (ptrTo base 8 k)) ∧
      ArrayAt m' .Mint64 ba base (clearedFromV vals k) M ∧ Unch m m' (· = ba) ∧
      Outside m m' ba base (base + 8 * M) ∧ Keep m m' ba ∧
      ∀ k', k' ≠ es → k' ≠ tmp → PTree.get k' le' = PTree.get k' le)
    (J := fun k t e' le' m' => ∃ k' < k, t = E0 ∧ e = e' ∧ k' ≤ M ∧
      PTree.get es le' = some (.Vptr ba (ptrTo base 8 k')) ∧
      ArrayAt m' .Mint64 ba base (clearedFromV vals k') M ∧ Unch m m' (· = ba) ∧
      Outside m m' ba base (base + 8 * M) ∧ Keep m m' ba ∧
      ∀ k'', k'' ≠ es → k'' ≠ tmp → PTree.get k'' le' = PTree.get k'' le) ?_ ?_ (n := M)
    ⟨rfl, rfl, Nat.le_refl _, temps_gss _ _ _, by
      refine ⟨hb, by rw [h8]; omega, fun i hi => ?_, fun i hi => harr.writable i hi⟩
      simp only [clearedFromV, ite_eq_left hi]; exact harr.load i hi,
      Unch.refl _ _, Outside.refl _ _ _ _, Alloc.Keep.refl _ _, fun k' hk _ => temps_gso _ _ hk⟩
  · rintro k t e' le' m' ⟨rfl, rfl, hk, hes, harr', hu, hout, hkp, hother⟩
    have hp' : Mem.load .Mint64 m' bg (zOfInt 0) = some (.Vptr ba ofs) := by
      rw [hu.load _ _ _ hbg]; exact hp
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, Exec.lvalOfVar, hge, hg, Exec.derefLoc, Cfrontend.Ctypes.access_mode,
      Mem.loadv, Alloc.Mptr_eq, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp', hes,
      typeof, cop]
    rw [cmplu_ptrTo harr' hM hk rfl]
    simp only [Option.map, cop]
    rcases k with _ | j
    · rw [ite_eq_right (by decide)]
      apply wp_break
      have h0 : clearedFromV vals 0 = longs fun _ => lr 0 := by funext w; simp [clearedFromV, longs]
      rw [h0] at harr'
      exact hQ le' m' harr' hu hout hkp hother
    · rw [ite_eq_left (by simp)]
      apply wp_skip
      simp only [E0_append]
      wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hes, typeof, cop, sub_ptrTo8]
      simp only [E0_append]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss, E0_append]
      have hj : j < M := by omega
      have hu8 : intOfZ (Ptrofs.unsigned (ptrTo base 8 j)) = base + 8 * j := by
        apply unsigned_ptrTo <;> omega
      obtain ⟨m'', hst, harr'', -⟩ := store_array harr' hj (.Vlong (lr 0)) rfl
      apply wp_assign_eval
      simp only [Exec.evalLvalue, Exec.evalExpr, temps_gss, temps_gso _ _ het.symm, typeof, cop,
        Exec.assignLoc, Cfrontend.Ctypes.access_mode,
        cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
      show match Mem.store .Mint64 m' ba (Ptrofs.unsigned _) _ with
        | some m' => _ | none => False
      rw [show Ptrofs.unsigned (ptrTo base 8 j) = elemOfs .Mint64 base j by
        rw [← zOfInt_intOfZ (Ptrofs.unsigned _), hu8]; rfl, hst]
      refine ⟨j, by omega, trivial, trivial, by omega, ?_, ?_, hu.trans (Unch.store hst rfl),
        hout.trans (Outside.store harr' hj hst (Int.le_refl _) (by rw [h8]; exact Int.le_refl _)),
        hkp.trans (Alloc.Keep.store hst (by simp only [elemOfs, intOfZ_zOfInt, h8]; omega)), ?_⟩
      · rfl
      · rw [← clearedFromV_succ]; exact harr''
      · intro k'' h1 h2
        rw [temps_gso _ _ h1, temps_gso _ _ h2, hother _ h1 h2]
  · rintro k t e' le' m' ⟨k', hk', h⟩
    apply wp_skip
    exact ⟨k', hk', by simpa using h⟩

/-- `ADDELEMENT(g, a)`: word `c / 64` of the set at `g` gets bit `c % 64`. -/
theorem wp_addElementG {g bitId : Common.AST.ident} {a : expr} {f : function} {Q : Post} {e : env}
    {le : temp_env} {m : mem} {bg ba bitB : block} {ofs : ptrofs} {ws : Nat → Lib.Integers.int64}
    {M c : Nat}
    (hge : PTree.get g e = none) (hg : Genv.find_symbol ge.genv_genv g = some bg)
    (hp : Mem.load .Mint64 m bg (zOfInt 0) = some (.Vptr ba ofs))
    (harr : ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs ws) M)
    (hM : M < 2147483648)
    (htc : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < 64 * M) (hc2 : c < 2147483648)
    (hbe : PTree.get bitId e = none) (hbg : Genv.find_symbol ge.genv_genv bitId = some bitB)
    (hbit : BitTable m bitB)
    (hQ : ∀ m', ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned ofs)) (longs (addW ws c)) M →
      Unch m m' (· = ba) →
      Outside m m' ba (intOfZ (Ptrofs.unsigned ofs)) (intOfZ (Ptrofs.unsigned ofs) + 8 * M) →
      Keep m m' ba → Q.normal E0 e le m') :
    Wp xi ge f (addElementG g bitId a) Q e le m := by
  have hw : c / 64 < M := by omega
  have hb : c % 64 < 64 := Nat.mod_lt _ (by decide)
  have h6 : Lib.Integers.Int.ltu (ir 6) Lib.Integers.Int.iwordsize = true := by decide
  have hshr : Lib.Integers.Int.shr (ir c) (ir 6) = ir ((c / 64 : Nat) : Int) := by
    rw [ir_shr6 ⟨by omega, by omega⟩]; congr 1
  have hand : Lib.Integers.Int.and (ir c) (ir 63) = ir ((c % 64 : Nat) : Int) := by
    rw [ir_and63 (by omega) (by omega)]; congr 1
  have hbaddr : Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong)) (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int))))) =
      elemOfs .Mint64 0 (c % 64) := by
    apply addr_elem _ _ .Mint64 rfl (base := 0) (by decide) (by omega)
    have h8 : csize .Mint64 = 8 := rfl
    rw [h8]; omega
  obtain ⟨m', hst, harr', -⟩ := store_array harr hw
    (.Vlong (Int64.or (ws (c / 64)) (lr ((2 ^ (63 - c % 64) : Nat) : Int)))) rfl
  simp only [addElementG, setWordG, sk]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hge, hg, hbe, hbg, htc, hty]
  simp only [Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hp]
  simp only [typeof, cop, h6, hshr, hand, ite_true]
  simp only [Exec.assignLoc, cop]
  have hl1 := load_array harr hw (addr_word harr hw hM)
  have hl2 : Mem.loadv .Mint64 m (.Vptr bitB (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv tulong))
      (Ptrofs.of_ints (ir ((c % 64 : Nat) : Int)))))) =
      some (.Vlong (lr ((2 ^ (63 - c % 64) : Nat) : Int))) := by
    show Mem.load _ _ _ _ = _
    rw [hbaddr]; exact hbit _ hb
  rw [hbaddr, hbit _ hb, addr_word harr hw hM, harr.load _ hw]
  simp only [longs, cop, Cfrontend.Ctypes.access_mode]
  simp only [Mem.storev]
  rw [addr_word harr hw hM, hst]
  rw [longs_upd] at harr'
  have hb0 := harr.base_nonneg
  exact hQ m' harr' (Unch.store hst rfl) (Outside.store harr hw hst (Int.le_refl _)
    (by rw [show csize .Mint64 = 8 from rfl]; exact Int.le_refl _))
    (Alloc.Keep.store hst (by simp only [elemOfs, intOfZ_zOfInt, show csize .Mint64 = 8 from rfl]; omega))

end NautyVerified.Proofs.Set

import NautyVerified.Proofs.Alloc.Dyn

/-!
# `DYNALLOC1` with a size read from memory

`wp_dynalloc1G` is `wp_dynalloc1'` for a size expression that may read
memory (nauty.c sizes its arrays by the globals `m` and `n`): it need only
evaluate the same in memories that differ from the current one in the
capacity global and the old array.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs

variable {xi : ExternalCalls}

theorem wp_dynalloc1G {e : env} {f : function} {Q : Post} {le : temp_env} {m : mem}
    {gs gp t1 t2 msg : Common.AST.ident} {elt : Cfrontend.Ctypes.type} {msgLen : Int}
    {bs bp b : block} {c cap n : Nat}
    (hgs : Genv.find_symbol ge.genv_genv gs = some bs)
    (hgp : Genv.find_symbol ge.genv_genv gp = some bp)
    (hc : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv elt) = c)
    (hD : DynAt m bp bs c cap b)
    {szE : expr} (hx : ∀ m', Unch m m' (fun z => z = bs ∨ (0 < cap ∧ z = b)) →
      Exec.evalExpr ge e le m' szE = some (.Vint (ir n)))
    (hty : typeof szE = tint) (hn : n < 2147483648) (hcn : c * n < 2 ^ 62)
    (hQ : ∀ le' m' cap' b', DynAt m' bp bs c cap' b' → n ≤ cap' →
      Unch m m' (fun z => z = bs ∨ z = bp ∨ (0 < cap ∧ z = b) ∨ (¬ Mem.valid_block m b' ∧ z = b')) →
      ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ k, k ≠ t1 → k ≠ t2 → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m')
    (hnil : NoShadow e := by exact NautyVerified.Proofs.Alloc.noShadow_empty) :
    Wp xi ge f (dynalloc1 gs gp elt szE t1 t2 msg msgLen) Q e le m := by
  have hnil1 := hnil _ _ hgs
  have hnil2 := hnil _ _ hgp
  have hnil3 := hnil _ _ find_free
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hx m (Unch.refl _ _), hty]
  simp only [Exec.lvalOfVar, hnil1, hnil2, hnil3, hgs, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, typeof, cop, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hD.capLd,
    cast_int_long_ir (a := n) ⟨by omega, by omega⟩]
  have hcap := hD.capLt
  rw [ltu_lr (a := cap) (b := n) (by omega) (by omega)]
  by_cases hnc : cap < n
  · rw [ite_eq_left (by simpa using hnc)]
    wp_step
    refine wp_freeOld (hnil := hnil) hgs hgp hD ?_
    intro m1 hu1 hnb1
    have hnS : ∀ z, (z = bs ∨ z = bp) → ¬ (0 < cap ∧ z = b) := by
      rintro z (rfl | rfl) ⟨hp, rfl⟩
      · exact (hD.bne hp).1 rfl
      · exact (hD.bne hp).2 rfl
    have hbsW1 := hu1.access _ _ _ _ (hnS bs (.inl rfl)) hD.bsW
    have hbpW1 := hu1.access _ _ _ _ (hnS bp (.inr rfl)) hD.bpW
    obtain ⟨m2, hst2⟩ := Mem.valid_access_store _ _ _ _ (.Vlong (lr n)) hbsW1
    wp_step; wp_step; wp_step
    apply wp_assign_eval
    simp only [Exec.evalLvalue, hx m1 (hu1.mono fun z hz => .inr hz), hty]
    simp only [Exec.lvalOfVar, hnil1, hnil2, hnil3, hgs, typeof, cop,
      Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
      cast_int_long_ir (a := n) ⟨by omega, by omega⟩, hst2]
    have hsz : Vptrofs (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv elt)) = .Vlong (lr c) := by
      rw [show Cfrontend.Ctypes.sizeof ge.genv_cenv elt = zOfInt c by
        rw [← hc, zOfInt_intOfZ], vptrofs_lr]
    wp_step; wp_step; wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr Block.zalloc Ptrofs.zero) (targs := [tulong]) (tres := tptr .Tvoid)
      (cc := Common.AST.cc_default) _ (zallocSpec (n * c)) (zalloc_satisfies _) rfl
      (by simp [Exec.evalExpr, Exec.lvalOfVar, hnil1, hnil2, hnil3, hnil _ _ find_zalloc, find_zalloc, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode])
      (by simp only [Exec.evalExprlist, Exec.evalExpr,
            hx m2 ((hu1.mono fun z hz => .inr hz).trans (Unch.store hst2 (.inl rfl))), hty]
          simp [typeof, cop, hsz,
        cast_int_long_ir (a := n) ⟨by omega, by omega⟩, lr_mul])
      (by simp [Common.Globalenvs.Genv.find_funct, funct_zalloc]) rfl
      ⟨rfl, by rw [Nat.mul_comm]; exact hcn⟩ ?_
    rintro t v m3 ⟨rfl, b', rfl, hfr, -⟩
    simp only [set_opttemp, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    have hbsW2 := Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _ hbsW1
    have hbpW2 := Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _ hbpW1
    have hbs' : bs ≠ b' := fun h => hfr.new (h ▸ valid_of_access hbsW2)
    have hbp' : bp ≠ b' := fun h => hfr.new (h ▸ valid_of_access hbpW2)
    have hbsW3 := hfr.unch.access _ _ _ _ hbs' hbsW2
    have hbpW3 := hfr.unch.access _ _ _ _ hbp' hbpW2
    obtain ⟨m4, hst4⟩ := Mem.valid_access_store _ _ _ _ (.Vptr b' Ptrofs.zero) hbpW3
    apply wp_assign_eval
    simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hnil1, hnil2, hnil3, hgp, temps_gss, typeof, cop,
      Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev, Mptr_eq,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hst4]
    have hvp : Mem.valid_pointer m4 b' (zOfInt (-1)) = true :=
      (Mem.valid_pointer_nonempty_perm m4 b' _).2 (Mem.perm_implies _ _ _ _ _ _
        (Mem.perm_store_1 _ _ _ _ _ _ hst4 _ _ _ _ (hfr.perm (-1) (by decide) (by omega)))
        (.perm_any_N _))
    have hcmp : Val.cmplu_bool (Mem.valid_pointer m4) .Ceq (.Vptr b' Ptrofs.zero)
        (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (ir 0)))) = some false := by
      unfold Val.cmplu_bool
      show (if _ && _ && (Mem.valid_pointer m4 b' _ || Mem.valid_pointer m4 b' (zOfInt (-1))) then _ else _) = _
      rw [hvp, Bool.or_true]
      rfl
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop, hcmp, Option.map]
    simp only [cop, Bool.false_eq_true, ite_false]
    apply wp_skip
    have hD' : DynAt m4 bp bs c n b' :=
      { capLd := by
          rw [Mem.load_store_other _ _ _ _ _ _ hst4 _ _ _ (.inl hD.ne), hfr.unch.load _ _ _ hbs',
            Mem.load_store_same _ _ _ _ _ _ hst2]
          rfl
        bsW := Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _ hbsW3
        bpW := Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _ hbpW3
        ptr := fun _ => by rw [Mem.load_store_same _ _ _ _ _ _ hst4]; rfl
        mal := fun _ =>
          { hdr := by
              rw [Mem.load_store_other _ _ _ _ _ _ hst4 _ _ _ (.inl hbp'.symm), hfr.hdr, Nat.mul_comm]
            perm := fun o h1 h2 => Mem.perm_store_1 _ _ _ _ _ _ hst4 _ _ _ _
              (hfr.perm o h1 (by rw [Nat.mul_comm]; exact h2))
            small := hcn }
        ne := hD.ne
        bne := fun _ => ⟨hbs'.symm, hbp'.symm⟩
        small := hcn
        capLt := hn }
    have hnew : ¬ Mem.valid_block m b' := by
      intro hv
      apply hfr.new
      apply Mem.store_valid_block_1 _ _ _ _ _ _ hst2
      unfold Mem.valid_block at hv ⊢
      rw [hnb1]; exact hv
    have hgrow : ∀ z, Mem.valid_block m z → Mem.valid_block m4 z := fun z hz => by
      apply Mem.store_valid_block_1 _ _ _ _ _ _ hst4
      apply hfr.grow
      apply Mem.store_valid_block_1 _ _ _ _ _ _ hst2
      unfold Mem.valid_block at hz ⊢
      rw [hnb1]; exact hz
    refine hQ _ m4 n b' hD' (Nat.le_refl _) ?_ (.inr hnew) hgrow ?_
    · exact (((hu1.mono fun z hz => .inr (.inr (.inl hz))).trans
        (Unch.store hst2 (.inl rfl))).trans (hfr.unch.mono fun z hz => .inr (.inr (.inr ⟨hz ▸ hnew, hz⟩)))).trans
        (Unch.store hst4 (.inr (.inl rfl)))
    · intro k h1 h2
      rw [temps_gso _ _ h2, temps_gso _ _ h1]
  · rw [ite_eq_right (by simpa using hnc)]
    apply wp_skip
    exact hQ le m cap b hD (by omega) (Unch.refl _ _) (.inl ⟨rfl, rfl⟩) (fun _ h => h) (fun _ _ _ => rfl)

end NautyVerified.Proofs.Alloc

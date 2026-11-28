import NautyVerified.Proofs.Alloc.Dyn

/-!
# `DYNFREE`

`DYNFREE(name, name_sz)` is `if (name) FREES(name); name = NULL; name_sz = 0;`
(`dynfree`). `wp_dynfree`: from `DynAt` (which records `NULL` at capacity 0,
so the test frees exactly an allocated block), the pair ends at capacity 0
with a `NULL` pointer, and only the two globals and the old block change.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- `name = NULL; name_sz = 0;` -/
abbrev nullPair (gp gs : Common.AST.ident) (elt : Cfrontend.Ctypes.type) : statement :=
  .Ssequence (sk (.Sassign (.Evar gp (tptr elt)) (.Ecast (ci 0 tint) (tptr .Tvoid))))
    (sk (.Sassign (.Evar gs tulong) (ci 0 tint)))

/-- `DYNFREE(gp, gs)` for elements of type `elt`, as SimplExpr writes it. -/
abbrev dynfree (gp gs : Common.AST.ident) (elt : Cfrontend.Ctypes.type) : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Evar gp (tptr elt))
      (sk (.Scall none (.Evar Source.dense.id.free (tfun [tptr .Tvoid] .Tvoid)) [.Evar gp (tptr elt)]))
      .Sskip))
    (nullPair gp gs elt)

theorem dynAt_zero {m : mem} {bp bs : block} {c : Nat} (hne : bs ≠ bp)
    (hcap : Mem.load .Mint64 m bs (zOfInt 0) = some (.Vlong (lr 0)))
    (hptr : Mem.load .Mint64 m bp (zOfInt 0) = some Vnullptr)
    (hbs : Mem.valid_access m .Mint64 bs (zOfInt 0) .Writable)
    (hbp : Mem.valid_access m .Mint64 bp (zOfInt 0) .Writable) (b : block) :
    DynAt m bp bs c 0 b :=
  { capLd := hcap, bsW := hbs, bpW := hbp, ptr := fun h => absurd h (Nat.lt_irrefl 0),
    mal := fun h => absurd h (Nat.lt_irrefl 0), ne := hne, bne := fun h => absurd h (Nat.lt_irrefl 0),
    small := by omega, capLt := by omega, null := fun _ => hptr }

theorem wp_nullPair {e : env} {f : function} {Q : Post} {le : temp_env} {m : mem}
    {gs gp : Common.AST.ident} {elt : Cfrontend.Ctypes.type} {bs bp : block}
    (hgs : Genv.find_symbol ge.genv_genv gs = some bs)
    (hgp : Genv.find_symbol ge.genv_genv gp = some bp) (hne : bs ≠ bp)
    (hbs : Mem.valid_access m .Mint64 bs (zOfInt 0) .Writable)
    (hbp : Mem.valid_access m .Mint64 bp (zOfInt 0) .Writable)
    (hQ : ∀ m', (∀ c b', DynAt m' bp bs c 0 b') → Unch m m' (fun z => z = bs ∨ z = bp) →
      Mem.nextblock m' = Mem.nextblock m → Q.normal E0 e le m')
    (hnil : NoShadow e := by exact NautyVerified.Proofs.Alloc.noShadow_empty) :
    Wp xi ge f (nullPair gp gs elt) Q e le m := by
  have hnil1 := hnil _ _ hgs
  have hnil2 := hnil _ _ hgp
  obtain ⟨m1, hst1⟩ := Mem.valid_access_store _ _ _ _ Vnullptr hbp
  wp_step; wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hnil1, hnil2, hgp, typeof, cop,
    Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev, Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  rw [show Cfrontend.Cop.sem_cast (.Vlong (Int64.repr (Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
    (tptr .Tvoid) (tptr elt) m = some Vnullptr from rfl]
  simp only [hst1]
  have hbs1 := Mem.store_valid_access_1 _ _ _ _ _ _ hst1 _ _ _ _ hbs
  obtain ⟨m2, hst2⟩ := Mem.valid_access_store _ _ _ _ (.Vlong (lr 0)) hbs1
  simp only [E0_append]
  wp_step; wp_step
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hnil1, hgs, typeof, cop,
    Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev, Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  rw [show Cfrontend.Cop.cast_int_long Cfrontend.Ctypes.Signed (Lib.Integers.Int.repr (zOfInt 0)) =
    lr 0 from rfl]
  simp only [hst2]
  have hu : Unch m m2 (fun z => z = bs ∨ z = bp) :=
    ((Unch.store hst1 rfl).mono fun _ h => .inr h.symm).trans ((Unch.store hst2 rfl).mono fun _ h => .inl h.symm)
  refine hQ m2 (fun c b' => dynAt_zero hne ?_ ?_ (Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _ hbs1)
    (Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _
      (Mem.store_valid_access_1 _ _ _ _ _ _ hst1 _ _ _ _ hbp)) b') hu ?_
  · rw [Mem.load_store_same _ _ _ _ _ _ hst2]; rfl
  · rw [Mem.load_store_other _ _ _ _ _ _ hst2 _ _ _ (.inl (Ne.symm hne)), Mem.load_store_same _ _ _ _ _ _ hst1]
    rfl
  · rw [Mem.nextblock_store _ _ _ _ _ _ hst2, Mem.nextblock_store _ _ _ _ _ _ hst1]

/-- `DYNFREE(gp, gs)`. -/
theorem wp_dynfree {e : env} {f : function} {Q : Post} {le : temp_env} {m : mem}
    {gs gp : Common.AST.ident} {elt : Cfrontend.Ctypes.type} {bs bp b : block} {c cap : Nat}
    (hgs : Genv.find_symbol ge.genv_genv gs = some bs)
    (hgp : Genv.find_symbol ge.genv_genv gp = some bp)
    (hD : DynAt m bp bs c cap b)
    (hQ : ∀ m', (∀ c' b', DynAt m' bp bs c' 0 b') →
      Unch m m' (fun z => z = bs ∨ z = bp ∨ (0 < cap ∧ z = b)) →
      Mem.nextblock m' = Mem.nextblock m → Q.normal E0 e le m')
    (hnil : NoShadow e := by exact NautyVerified.Proofs.Alloc.noShadow_empty) :
    Wp xi ge f (dynfree gp gs elt) Q e le m := by
  have hnil1 := hnil _ _ hgs
  have hnil2 := hnil _ _ hgp
  have hnil3 := hnil _ _ find_free
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, hnil2, hgp, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, typeof, Mem.loadv, Mptr_eq,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl]
  by_cases h0 : cap = 0
  · subst h0
    rw [hD.null rfl]
    simp only [show bool_val Vnullptr (tptr elt) m = some false from rfl, Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    exact wp_nullPair hgs hgp hD.ne hD.bsW hD.bpW (fun m' hD' hu hnb => by
      simpa using hQ m' hD' (hu.mono fun z hz => by rcases hz with h | h; exact .inl h; exact .inr (.inl h)) hnb) hnil
  · have hpos : 0 < cap := by omega
    have hmal := hD.mal hpos
    have hwv : Mem.weak_valid_pointer m b (zOfInt 0) = true := by
      have h := hmal.perm (-1) (by decide) (by omega)
      have hv := (Mem.valid_pointer_nonempty_perm m b _).2
        (Mem.perm_implies _ _ _ _ _ _ h (.perm_any_N _))
      unfold Mem.weak_valid_pointer
      show (Mem.valid_pointer m b _ || Mem.valid_pointer m b (zOfInt (-1))) = true
      rw [hv, Bool.or_true]
    rw [hD.ptr hpos]
    simp only [cop, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hwv, ite_true]
    wp_step; wp_step
    refine wp_call (vf := .Vptr Block.free Ptrofs.zero) _ (freeSpec b (c * cap)) (free_satisfies b _) rfl
      (by simp [Exec.evalExpr, Exec.lvalOfVar, hnil1, hnil2, hnil3, find_free, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode])
      (by simp [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, hnil1, hnil2, hnil3, hgp, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode, Mem.loadv, Mptr_eq,
        show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hD.ptr hpos, typeof, cop])
      (by simp [Common.Globalenvs.Genv.find_funct, funct_free]) rfl ⟨rfl, hmal⟩ ?_
    rintro t v m1 ⟨rfl, rfl, hu, hnb⟩
    simp only [seqPost, Post.after, E0_append, set_opttemp]
    have hbs' : ¬ bs = b := fun h => (hD.bne hpos).1 h.symm
    have hbp' : ¬ bp = b := fun h => (hD.bne hpos).2 h.symm
    refine wp_nullPair hgs hgp hD.ne (hu.access _ _ _ _ hbs' hD.bsW)
      (hu.access _ _ _ _ hbp' hD.bpW) (fun m' hD' hu' hnb' => ?_) hnil
    simpa using hQ m' hD' ((hu.mono fun z hz => .inr (.inr ⟨hpos, hz⟩)).trans
      (hu'.mono fun z hz => by rcases hz with h | h; exact .inl h; exact .inr (.inl h))) (hnb'.trans hnb)

end NautyVerified.Proofs.Alloc

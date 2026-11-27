import NautyVerified.Proofs.Alloc.Zero
import NautyVerified.Proofs.Alloc.Free

/-!
# nauty's `DYNALLSTAT` arrays

A `DYNALLSTAT(type, name, name_sz)` pair is a static pointer `name` and a
static capacity `name_sz`. `DynAt m gp gs c cap b`: the capacity global `gs`
holds `cap`, and when `cap > 0` the pointer global `gp` points to block `b`,
allocated by `malloc` for `c * cap` bytes (`c` the element size).
`malloced_array`: such a block holds an array of `cap` elements (values
unknown); `DYNALLOC1` (`wp_dynalloc1`) re-establishes `DynAt` with capacity
at least the size asked for.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs

/-- The first `k` elements of a `malloc`ed block of at least `c * k` bytes
form an array, whatever their values. -/
theorem malloced_array {m : mem} {b : block} {N : Nat} (h : Malloced m b N) (chunk : memory_chunk)
    (c : Nat) (hc : csize chunk = c) (ha : intOfZ (align_chunk chunk) = c) (k : Nat)
    (hk : c * k ≤ N) : ∃ vals, ArrayAt m chunk b 0 vals k := by
  have hcpos := csize_pos chunk
  have hofs : ∀ i : Nat, elemOfs chunk 0 i = zOfInt ((c * i : Nat) : Int) := fun i => by
    simp only [elemOfs, hc]; congr 1; push_cast; omega
  have hle : ∀ i, i < k → c * i + c ≤ N := fun i hi => by
    have := Nat.mul_le_mul_left c (show i + 1 ≤ k by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  have hva : ∀ i, i < k → Mem.valid_access m chunk b (elemOfs chunk 0 i) .Writable := fun i hi => by
    rw [hofs]
    refine ⟨fun o ho => ?_, ⟨zOfInt i, by
      apply intOfZ_injective
      simp only [intOfZ_mul, intOfZ_zOfInt, ha]; push_cast; rw [Int.mul_comm]⟩⟩
    have h1 : ((c * i : Nat) : Int) ≤ intOfZ o := by
      have := ho.1; change intOfZ _ ≤ intOfZ _ at this; rwa [intOfZ_zOfInt] at this
    have h2 : intOfZ o < ((c * i : Nat) : Int) + c := by
      have := ho.2; change intOfZ _ < intOfZ _ at this
      rwa [intOfZ_add, intOfZ_zOfInt, show intOfZ (size_chunk chunk) = c from hc] at this
    have := h.perm (intOfZ o) (by omega) (by have := hle i hi; omega)
    rw [zOfInt_intOfZ] at this
    exact Mem.perm_implies _ _ _ _ _ _ this (.perm_F_any _)
  refine ⟨fun i => (Mem.load chunk m b (elemOfs chunk 0 i)).getD .Vundef,
    ⟨Int.le_refl _, ?_, fun i hi => ?_, hva⟩⟩
  · rw [hc]
    have := h.small
    have : ((c * k : Nat) : Int) = (c : Int) * k := by push_cast; rfl
    omega
  · obtain ⟨v, hv⟩ := Mem.valid_access_load _ _ _ _
      (Mem.valid_access_implies _ _ _ _ _ _ (hva i hi) .perm_W_R)
    rw [hv]; rfl

abbrev sk (s : statement) : statement := .Ssequence .Sskip s

/-- `DYNALLOC1(elt, gp, gs, sz, msg)`, as SimplExpr writes it, with temporaries
`t1` (the allocator's result) and `t2` (its cast). -/
abbrev dynalloc1 (gs gp : Common.AST.ident) (elt : Cfrontend.Ctypes.type) (szE : expr) (t1 t2 msg : Common.AST.ident)
    (msgLen : Int) : statement :=
  sk (.Sifthenelse (.Ebinop .Ogt (.Ecast szE tulong) (.Evar gs tulong) tint)
    (.Ssequence
      (sk (.Sifthenelse (.Evar gs tulong)
        (sk (.Scall none (.Evar Source.dense.id.free (tfun [tptr .Tvoid] .Tvoid))
          [.Evar gp (tptr elt)]))
        .Sskip))
      (.Ssequence
        (sk (.Sassign (.Evar gs tulong) szE))
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (sk (.Scall (some t1) (.Evar Source.dense.id.nauty_zalloc (tfun [tulong] (tptr .Tvoid)))
                [.Ebinop .Omul (.Ecast szE tulong) (.Ecast (.Esizeof elt tulong) tulong) tulong]))
              (.Sset t2 (.Ecast (.Ecast (.Etempvar t1 (tptr .Tvoid)) (tptr elt)) (tptr elt))))
            (.Sassign (.Evar gp (tptr elt)) (.Etempvar t2 (tptr elt))))
          (.Sifthenelse (.Ebinop .Oeq (.Etempvar t2 (tptr elt)) (.Ecast (ci 0 tint) (tptr .Tvoid)) tint)
            (sk (.Scall none (.Evar Source.dense.id.alloc_error (tfun [tptr tschar] .Tvoid))
              [.Evar msg (tarray tschar msgLen)]))
            .Sskip))))
    .Sskip)

/-- A `DYNALLSTAT` pair: the capacity global (block `bs`) holds `cap`; when
`cap > 0` the pointer global (block `bp`) points to a block `b` that `malloc`
made for `c * cap` bytes. -/
structure DynAt (m : mem) (bp bs : block) (c cap : Nat) (b : block) : Prop where
  capLd : Mem.load .Mint64 m bs (zOfInt 0) = some (.Vlong (lr cap))
  bsW : Mem.valid_access m .Mint64 bs (zOfInt 0) .Writable
  bpW : Mem.valid_access m .Mint64 bp (zOfInt 0) .Writable
  ptr : 0 < cap → Mem.load .Mint64 m bp (zOfInt 0) = some (.Vptr b Ptrofs.zero)
  mal : 0 < cap → Malloced m b (c * cap)
  ne : bs ≠ bp
  bne : 0 < cap → b ≠ bs ∧ b ≠ bp
  small : c * cap < 2 ^ 62
  capLt : cap < 2147483648

theorem valid_of_access {m : mem} {chunk : memory_chunk} {b : block} {ofs : Z} {p : permission}
    (h : Mem.valid_access m chunk b ofs p) : Mem.valid_block m b := by
  have : 0 < intOfZ (size_chunk chunk) := csize_pos chunk
  exact Mem.perm_valid_block _ _ _ _ _ (h.1 ofs ⟨by change intOfZ _ ≤ intOfZ _; omega, by
    change intOfZ _ < intOfZ _; simp only [intOfZ_add]; omega⟩)

variable {xi : ExternalCalls}

theorem Mptr_eq : Mptr = .Mint64 := rfl

theorem lr_mul (a b : Nat) : Lib.Integers.Int64.mul (lr a) (lr b) = lr (a * b) := by
  apply bv64_inj.1
  simp only [bv64_mul, bv64_repr, intOfZ_zOfInt, ← BitVec.ofInt_mul]

theorem eq_lr_zero {k : Nat} (hk : k < 2 ^ 63) :
    Lib.Integers.Int64.eq (lr k) Lib.Integers.Int64.zero = decide (k = 0) := by
  rw [bv64_eq, bv64_zero]
  apply decide_eq_decide.2
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [toNat_lr hk] at this
    simpa using this
  · intro h; subst h; rfl

/-- `if (name_sz) free(name);` -/
theorem wp_freeOld {f : function} {Q : Post} {le : temp_env} {m : mem}
    {gs gp : Common.AST.ident} {elt : Cfrontend.Ctypes.type} {bs bp b : block} {c cap : Nat}
    (hgs : Genv.find_symbol ge.genv_genv gs = some bs)
    (hgp : Genv.find_symbol ge.genv_genv gp = some bp)
    (hD : DynAt m bp bs c cap b)
    (hQ : ∀ m1, Unch m m1 (fun z => 0 < cap ∧ z = b) → Mem.nextblock m1 = Mem.nextblock m →
      Q.normal E0 empty_env le m1) :
    Wp xi ge f (sk (.Sifthenelse (.Evar gs tulong)
        (sk (.Scall none (.Evar Source.dense.id.free (tfun [tptr .Tvoid] .Tvoid))
          [.Evar gp (tptr elt)]))
        .Sskip)) Q empty_env le m := by
  have hnil : ∀ i, PTree.get i (empty_env : env) = none := fun _ => rfl
  have hcap := hD.capLt
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, Exec.lvalOfVar, hnil, hgs, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, typeof, cop, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hD.capLd, eq_lr_zero (k := cap) (by omega)]
  by_cases h0 : cap = 0
  · rw [ite_eq_right (by simp [h0])]
    apply wp_skip
    exact hQ m (Unch.refl _ _) rfl
  · rw [ite_eq_left (by simp [h0])]
    have hpos : 0 < cap := by omega
    wp_step; wp_step
    refine wp_call (vf := .Vptr Block.free Ptrofs.zero) _ (freeSpec b (c * cap)) (free_satisfies b _) rfl
      (by simp [Exec.evalExpr, Exec.lvalOfVar, hnil, find_free, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode])
      (by simp [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, hnil, hgp, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode, Mem.loadv, Mptr_eq,
        show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hD.ptr hpos, typeof, cop])
      (by simp [Common.Globalenvs.Genv.find_funct, funct_free]) rfl ⟨rfl, hD.mal hpos⟩ ?_
    rintro t v m1 ⟨rfl, rfl, hu, hnb⟩
    exact hQ m1 (hu.mono fun z hz => ⟨hpos, hz⟩) hnb

theorem wp_dynalloc1' {f : function} {Q : Post} {le : temp_env} {m : mem}
    {gs gp t1 t2 msg : Common.AST.ident} {elt : Cfrontend.Ctypes.type} {msgLen : Int}
    {bs bp b : block} {c cap n : Nat}
    (hgs : Genv.find_symbol ge.genv_genv gs = some bs)
    (hgp : Genv.find_symbol ge.genv_genv gp = some bp)
    (hc : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv elt) = c)
    (hD : DynAt m bp bs c cap b)
    {szE : expr} (hx : ∀ m', Exec.evalExpr ge empty_env le m' szE = some (.Vint (ir n)))
    (hty : typeof szE = tint) (hn : n < 2147483648) (hcn : c * n < 2 ^ 62)
    (hQ : ∀ le' m' cap' b', DynAt m' bp bs c cap' b' → n ≤ cap' →
      Unch m m' (fun z => z = bs ∨ z = bp ∨ (0 < cap ∧ z = b) ∨ (¬ Mem.valid_block m b' ∧ z = b')) →
      ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ k, k ≠ t1 → k ≠ t2 → PTree.get k le' = PTree.get k le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f (dynalloc1 gs gp elt szE t1 t2 msg msgLen) Q empty_env le m := by
  have hnil : ∀ i, PTree.get i (empty_env : env) = none := fun _ => rfl
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hx, hty]
  simp only [Exec.lvalOfVar, hnil, hgs, Exec.derefLoc,
    Cfrontend.Ctypes.access_mode, typeof, cop, Mem.loadv,
    show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hD.capLd,
    cast_int_long_ir (a := n) ⟨by omega, by omega⟩]
  have hcap := hD.capLt
  rw [ltu_lr (a := cap) (b := n) (by omega) (by omega)]
  by_cases hnc : cap < n
  · rw [ite_eq_left (by simpa using hnc)]
    wp_step
    refine wp_freeOld hgs hgp hD ?_
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
    simp only [Exec.evalLvalue, hx, hty]
    simp only [Exec.lvalOfVar, hnil, hgs, typeof, cop,
      Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl,
      cast_int_long_ir (a := n) ⟨by omega, by omega⟩, hst2]
    have hsz : Vptrofs (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv elt)) = .Vlong (lr c) := by
      rw [show Cfrontend.Ctypes.sizeof ge.genv_cenv elt = zOfInt c by
        rw [← hc, zOfInt_intOfZ], vptrofs_lr]
    wp_step; wp_step; wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr Block.zalloc Ptrofs.zero) (targs := [tulong]) (tres := tptr .Tvoid)
      (cc := Common.AST.cc_default) _ (zallocSpec (n * c)) (zalloc_satisfies _) rfl
      (by simp [Exec.evalExpr, Exec.lvalOfVar, hnil, find_zalloc, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode])
      (by simp only [Exec.evalExprlist, Exec.evalExpr, hx, hty]
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
    simp only [Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar, hnil, hgp, temps_gss, typeof, cop,
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

/-- `wp_dynalloc1'` for a size held in a temporary. -/
theorem wp_dynalloc1 {f : function} {Q : Post} {le : temp_env} {m : mem}
    {gs gp x t1 t2 msg : Common.AST.ident} {elt : Cfrontend.Ctypes.type} {msgLen : Int}
    {bs bp b : block} {c cap n : Nat}
    (hgs : Genv.find_symbol ge.genv_genv gs = some bs)
    (hgp : Genv.find_symbol ge.genv_genv gp = some bp)
    (hc : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv elt) = c)
    (hD : DynAt m bp bs c cap b)
    (hx : PTree.get x le = some (.Vint (ir n))) (hn : n < 2147483648) (hcn : c * n < 2 ^ 62)
    (hQ : ∀ le' m' cap' b', DynAt m' bp bs c cap' b' → n ≤ cap' →
      Unch m m' (fun z => z = bs ∨ z = bp ∨ (0 < cap ∧ z = b) ∨ (¬ Mem.valid_block m b' ∧ z = b')) →
      ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ k, k ≠ t1 → k ≠ t2 → PTree.get k le' = PTree.get k le) →
      Q.normal E0 empty_env le' m') :
    Wp xi ge f (dynalloc1 gs gp elt (.Etempvar x tint) t1 t2 msg msgLen) Q empty_env le m :=
  wp_dynalloc1' (msgLen := msgLen) hgs hgp hc hD (fun _ => hx) rfl hn hcn hQ

end NautyVerified.Proofs.Alloc

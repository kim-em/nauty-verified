import NautyVerified.Program.Env
import NautyVerified.Proofs.Alloc.Keep

/-!
# `DYNFREE`

`DYNFREE(name, name_sz)` is `if (name) FREES(name); name = NULL; name_sz = 0;`
(`dynfree`). `wp_dynfree`: from `DynAt` (which records `NULL` at capacity 0,
so the test frees exactly an allocated block), the pair ends at capacity 0
with a `NULL` pointer, and only the two globals and the old block change.
-/

namespace NautyVerified.Proofs.Alloc

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

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
  have hnil3 := hnil _ _ E.find_free
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
    refine wp_call (vf := .Vptr E.free Ptrofs.zero) _ (freeSpec b (c * cap)) (free_satisfies b _) rfl
      (by simp [Exec.evalExpr, Exec.lvalOfVar, hnil1, hnil2, hnil3, E.find_free, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode])
      (by simp [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, hnil1, hnil2, hnil3, hgp, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode, Mem.loadv, Mptr_eq,
        show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hD.ptr hpos, typeof, cop])
      (by simp [Common.Globalenvs.Genv.find_funct, E.funct_free]) rfl ⟨rfl, hmal⟩ ?_
    rintro t v m1 ⟨rfl, rfl, hu, hnb⟩
    simp only [seqPost, Post.after, E0_append, set_opttemp]
    have hbs' : ¬ bs = b := fun h => (hD.bne hpos).1 h.symm
    have hbp' : ¬ bp = b := fun h => (hD.bne hpos).2 h.symm
    refine wp_nullPair hgs hgp hD.ne (hu.access _ _ _ _ hbs' hD.bsW)
      (hu.access _ _ _ _ hbp' hD.bpW) (fun m' hD' hu' hnb' => ?_) hnil
    simpa using hQ m' hD' ((hu.mono fun z hz => .inr (.inr ⟨hpos, hz⟩)).trans
      (hu'.mono fun z hz => by rcases hz with h | h; exact .inl h; exact .inr (.inl h))) (hnb'.trans hnb)

/-- One `DYNFREE`: the pair's identifiers, blocks, element type, size, and its
current capacity and block. -/
structure FreeD where
  gp : Common.AST.ident
  gs : Common.AST.ident
  bp : block
  bs : block
  elt : Cfrontend.Ctypes.type
  c : Nat
  cap : Nat
  blk : block

/-- A right-nested sequence (the last statement not followed by a skip). -/
def seqR : List statement → statement
  | [] => .Sskip
  | [s] => s
  | s :: rest => .Ssequence s (seqR rest)

/-- The pairs' globals. -/
def FreeD.globals (ds : List FreeD) : List block := ds.flatMap fun d => [d.bs, d.bp]

/-- What a run of `DYNFREE`s needs: the globals' symbols and `DynAt`, the
globals distinct, and the allocated blocks distinct and apart from the globals. -/
structure FreeD.Ok [NautyVerified.Program.NautyEnv ge] (m : mem) (ds : List FreeD) : Prop where
  sym : ∀ d ∈ ds, Genv.find_symbol ge.genv_genv d.gs = some d.bs ∧
    Genv.find_symbol ge.genv_genv d.gp = some d.bp
  dyn : ∀ d ∈ ds, DynAt m d.bp d.bs d.c d.cap d.blk
  glob : (FreeD.globals ds).Pairwise (· ≠ ·)
  apart : ∀ d ∈ ds, 0 < d.cap → d.blk ∉ FreeD.globals ds
  blks : ds.Pairwise (fun d d' => 0 < d.cap → 0 < d'.cap → d.blk ≠ d'.blk)

theorem FreeD.mem_globals {ds : List FreeD} {d : FreeD} (h : d ∈ ds) :
    d.bs ∈ FreeD.globals ds ∧ d.bp ∈ FreeD.globals ds := by
  simp only [FreeD.globals, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false]
  exact ⟨⟨d, h, .inl rfl⟩, ⟨d, h, .inr rfl⟩⟩

theorem FreeD.globals_cons (d : FreeD) (ds : List FreeD) :
    FreeD.globals (d :: ds) = d.bs :: d.bp :: FreeD.globals ds := by
  simp [FreeD.globals]

theorem FreeD.Ok.tail {m m' : mem} {d : FreeD} {ds : List FreeD} (h : FreeD.Ok m (d :: ds))
    (hu : Unch m m' (fun z => z = d.bs ∨ z = d.bp ∨ (0 < d.cap ∧ z = d.blk))) : FreeD.Ok m' ds := by
  have hg := h.glob
  rw [FreeD.globals_cons, List.pairwise_cons, List.pairwise_cons] at hg
  obtain ⟨hbs, hbp, hg'⟩ := hg
  have hbl := h.blks
  rw [List.pairwise_cons] at hbl
  have G := FreeD.mem_globals (List.mem_cons_self (a := d) (l := ds))
  have hap := h.apart d (by simp)
  have notS : ∀ d' ∈ ds, ∀ z, (z = d'.bs ∨ z = d'.bp ∨ (0 < d'.cap ∧ z = d'.blk)) →
      ¬ (z = d.bs ∨ z = d.bp ∨ (0 < d.cap ∧ z = d.blk)) := by
    intro d' hd' z hz hz'
    have hgl := FreeD.mem_globals hd'
    have G' := FreeD.mem_globals (List.mem_cons_of_mem d hd')
    have hap' := h.apart d' (List.mem_cons_of_mem d hd')
    rcases hz with rfl | rfl | ⟨hc', rfl⟩ <;> rcases hz' with e | e | ⟨hc, e⟩
    · exact hbs _ (List.mem_cons_of_mem _ hgl.1) e.symm
    · exact hbp _ hgl.1 e.symm
    · exact hap hc (e ▸ G'.1)
    · exact hbs _ (List.mem_cons_of_mem _ hgl.2) e.symm
    · exact hbp _ hgl.2 e.symm
    · exact hap hc (e ▸ G'.2)
    · exact hap' hc' (by rw [e]; exact G.1)
    · exact hap' hc' (by rw [e]; exact G.2)
    · exact hbl.1 d' hd' hc hc' e.symm
  refine ⟨fun d' hd' => h.sym d' (List.mem_cons_of_mem d hd'), fun d' hd' => ?_, hg', fun d' hd' hc => ?_,
    hbl.2⟩
  · exact (h.dyn d' (List.mem_cons_of_mem d hd')).keep hu (notS d' hd' _ (.inr (.inl rfl)))
      (notS d' hd' _ (.inl rfl)) (fun hc => Keep.unch hu (notS d' hd' _ (.inr (.inr ⟨hc, rfl⟩))))
  · intro hm
    exact h.apart d' (List.mem_cons_of_mem d hd') hc (by
      rw [FreeD.globals_cons]; exact .tail _ (.tail _ hm))

/-- A run of `DYNFREE`s. -/
theorem wp_dynfrees {e : env} {f : function} {Q : Post} {le : temp_env} (hnil : NoShadow e) :
    ∀ (ds : List FreeD) (m : mem), FreeD.Ok m ds →
    (∀ m', (∀ d ∈ ds, ∀ c b', DynAt m' d.bp d.bs c 0 b') →
      Unch m m' (fun z => z ∈ FreeD.globals ds ∨ ∃ d ∈ ds, 0 < d.cap ∧ z = d.blk) →
      Mem.nextblock m' = Mem.nextblock m → Q.normal E0 e le m') →
    Wp xi ge f (seqR (ds.map fun d => dynfree d.gp d.gs d.elt)) Q e le m
  | [], m, _, hQ => by
    apply wp_skip
    exact hQ m (fun d hd => absurd hd (by simp)) (Unch.refl _ _) rfl
  | [d], m, h, hQ => by
    obtain ⟨hgs, hgp⟩ := h.sym d (by simp)
    refine wp_dynfree hgs hgp (h.dyn d (by simp)) (fun m' hD' hu hnb => hQ m' ?_ ?_ hnb) hnil
    · intro d' hd'; simp only [List.mem_singleton] at hd'; subst hd'; exact hD'
    · refine hu.mono fun z hz => ?_
      rcases hz with rfl | rfl | ⟨hc, rfl⟩
      · exact .inl (by simp [FreeD.globals])
      · exact .inl (by simp [FreeD.globals])
      · exact .inr ⟨d, by simp, hc, rfl⟩
  | d :: d' :: rest, m, h, hQ => by
    obtain ⟨hgs, hgp⟩ := h.sym d (by simp)
    show Wp xi ge f (.Ssequence (dynfree d.gp d.gs d.elt)
      (seqR ((d' :: rest).map fun d => dynfree d.gp d.gs d.elt))) Q e le m
    wp_step
    refine wp_dynfree hgs hgp (h.dyn d (by simp)) (fun m1 hD1 hu1 hnb1 => ?_) hnil
    simp only [seqPost, Post.after, E0_append]
    have ht := h.tail hu1
    refine wp_dynfrees hnil (d' :: rest) m1 ht (fun m' hD' hu' hnb' => hQ m' ?_ ?_ (hnb'.trans hnb1))
    · intro d₀ hd₀
      simp only [List.mem_cons] at hd₀
      rcases hd₀ with rfl | hd₀
      · intro c b'
        have hg := h.glob
        rw [FreeD.globals_cons, List.pairwise_cons, List.pairwise_cons] at hg
        obtain ⟨hbs, hbp, -⟩ := hg
        have G := FreeD.mem_globals (List.mem_cons_self (a := d₀) (l := d' :: rest))
        have nT : ∀ z, (z = d₀.bs ∨ z = d₀.bp) → ¬ (z ∈ FreeD.globals (d' :: rest) ∨
            ∃ d ∈ d' :: rest, 0 < d.cap ∧ z = d.blk) := by
          rintro z hz (hz' | ⟨d₁, hd₁, hc₁, rfl⟩)
          · rcases hz with rfl | rfl
            · exact hbs _ (List.mem_cons_of_mem _ hz') rfl
            · exact hbp _ hz' rfl
          · have hap := h.apart d₁ (List.mem_cons_of_mem _ hd₁) hc₁
            rcases hz with e | e
            · exact hap (by first | (rw [e]; exact G.1) | (rw [← e]; exact G.1))
            · exact hap (by first | (rw [e]; exact G.2) | (rw [← e]; exact G.2))
        exact (hD1 c b').keep hu' (nT _ (.inr rfl)) (nT _ (.inl rfl)) (fun hc => absurd hc (Nat.lt_irrefl 0))
      · exact hD' d₀ (by simp [hd₀])
    · refine (hu1.mono fun z hz => ?_).trans (hu'.mono fun z hz => ?_)
      · rcases hz with rfl | rfl | ⟨hc, rfl⟩
        · exact .inl (by simp [FreeD.globals])
        · exact .inl (by simp [FreeD.globals])
        · exact .inr ⟨d, by simp, hc, rfl⟩
      · rcases hz with hz | ⟨d₁, hd₁, hc₁, rfl⟩
        · exact .inl (by simp only [FreeD.globals, List.flatMap_cons, List.mem_append] at hz ⊢; exact .inr hz)
        · exact .inr ⟨d₁, by simp only [List.mem_cons] at hd₁ ⊢; exact .inr hd₁, hc₁, rfl⟩

end NautyVerified.Proofs.Alloc

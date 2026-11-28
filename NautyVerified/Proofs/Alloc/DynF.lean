import NautyVerified.Proofs.Alloc.DynL
import NautyVerified.Proofs.Alloc.Keep

/-!
# `DYNALLOC1` on the fields of a struct

nausparse.h's `SG_ALLOC(sg, nlen, ndelen, msg)` is three `DYNALLOC1`s whose
pointer and capacity are fields of a `sparsegraph` struct reached through a
pointer temporary: `DYNALLOC1(size_t, (sg).v, (sg).vlen, nlen, msg)` and the
same for `d`/`dlen` and `e`/`elen`. `dynalloc1F` is one of them as
SimplExpr writes it, `fld p sid f ty` being `p->f` for `p` of type
`struct sid *`.

`FieldDyn m bc po so c cap b`: the capacity field (at `so` in block `bc`)
holds `cap`, and when `cap > 0` the pointer field (at `po`) points to block
`b`, allocated by `malloc` for `c * cap` bytes; when `cap = 0` it holds
`NULL`. This is `DynAt` with the two globals replaced by two disjoint fields
of one block.

`wp_dynalloc1F`: the size expression's value `vx`, cast to `size_t`, is `n`
(it may read memory, but none of `bc` or the old block); afterwards the pair
holds capacity at least `n`, and only the two fields of `bc`, the old block
and a new block have changed (`FieldFrame` for the rest of `bc`).
-/

namespace NautyVerified.Proofs.Alloc

variable {ge : CompCert4Lean.Cfrontend.Clight.genv} [E : NautyVerified.Program.NautyEnv ge]
set_option linter.unusedSectionVars false

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs

variable {xi : ExternalCalls}

/-- `p->f` for a temporary `p` of type `struct sid *`. -/
abbrev fld (p sid f : Common.AST.ident) (ty : Cfrontend.Ctypes.type) : expr :=
  .Efield (.Ederef (.Etempvar p (tptr (.Tstruct sid Cfrontend.Ctypes.noattr)))
    (.Tstruct sid Cfrontend.Ctypes.noattr)) f ty

/-- `DYNALLOC1(elt, p->fp, p->fs, sz, msg)`, as SimplExpr writes it, with
temporaries `t1` (the allocator's result) and `t2` (its cast). -/
abbrev dynalloc1F (p sid fp fs : Common.AST.ident) (elt : Cfrontend.Ctypes.type) (szE : expr)
    (t1 t2 msg : Common.AST.ident) (msgLen : Int) : statement :=
  sk (.Sifthenelse (.Ebinop .Ogt (.Ecast szE tulong) (fld p sid fs tulong) tint)
    (.Ssequence
      (sk (.Sifthenelse (fld p sid fs tulong)
        (sk (.Scall none (.Evar Source.dense.id.free (tfun [tptr .Tvoid] .Tvoid))
          [fld p sid fp (tptr elt)]))
        .Sskip))
      (.Ssequence
        (sk (.Sassign (fld p sid fs tulong) szE))
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (sk (.Scall (some t1) (.Evar Source.dense.id.nauty_zalloc (tfun [tulong] (tptr .Tvoid)))
                [.Ebinop .Omul (.Ecast szE tulong) (.Ecast (.Esizeof elt tulong) tulong) tulong]))
              (.Sset t2 (.Ecast (.Ecast (.Etempvar t1 (tptr .Tvoid)) (tptr elt)) (tptr elt))))
            (.Sassign (fld p sid fp (tptr elt)) (.Etempvar t2 (tptr elt))))
          (.Sifthenelse (.Ebinop .Oeq (.Etempvar t2 (tptr elt)) (.Ecast (ci 0 tint) (tptr .Tvoid)) tint)
            (sk (.Scall none (.Evar Source.dense.id.alloc_error (tfun [tptr tschar] .Tvoid))
              [.Evar msg (tarray tschar msgLen)]))
            .Sskip))))
    .Sskip)

/-- The `csize chunk` bytes at `ofs` miss the 8 bytes at `o`. -/
def Apart (chunk : memory_chunk) (ofs : Z) (o : ptrofs) : Prop :=
  intOfZ ofs + csize chunk ≤ intOfZ (Ptrofs.unsigned o) ∨ intOfZ (Ptrofs.unsigned o) + 8 ≤ intOfZ ofs

/-- A `DYNALLSTAT`-style pair held in the fields at `po` (pointer) and `so`
(capacity) of block `bc`. -/
structure FieldDyn (m : mem) (bc : block) (po so : ptrofs) (c cap : Nat) (b : block) : Prop where
  capLd : Mem.load .Mint64 m bc (Ptrofs.unsigned so) = some (.Vlong (lr cap))
  capW : Mem.valid_access m .Mint64 bc (Ptrofs.unsigned so) .Writable
  ptrW : Mem.valid_access m .Mint64 bc (Ptrofs.unsigned po) .Writable
  ptr : 0 < cap → Mem.load .Mint64 m bc (Ptrofs.unsigned po) = some (.Vptr b Ptrofs.zero)
  mal : 0 < cap → Malloced m b (c * cap)
  apart : Apart .Mint64 (Ptrofs.unsigned po) so
  bne : 0 < cap → b ≠ bc
  small : c * cap < 2 ^ 62
  capLt : cap < 2147483648
  null : cap = 0 → Mem.load .Mint64 m bc (Ptrofs.unsigned po) = some Vnullptr

/-- Block `bc` changed only in the 8-byte fields at `po` and `so`. -/
structure FieldFrame (m m' : mem) (bc : block) (po so : ptrofs) : Prop where
  load : ∀ chunk ofs, Apart chunk ofs po → Apart chunk ofs so →
    Mem.load chunk m' bc ofs = Mem.load chunk m bc ofs
  access : ∀ chunk ofs p, Mem.valid_access m chunk bc ofs p → Mem.valid_access m' chunk bc ofs p

theorem FieldFrame.refl (m : mem) (bc : block) (po so : ptrofs) : FieldFrame m m bc po so :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ h => h⟩

theorem FieldFrame.trans {m₁ m₂ m₃ : mem} {bc : block} {po so : ptrofs}
    (h₁ : FieldFrame m₁ m₂ bc po so) (h₂ : FieldFrame m₂ m₃ bc po so) : FieldFrame m₁ m₃ bc po so :=
  ⟨fun c o a1 a2 => (h₂.load c o a1 a2).trans (h₁.load c o a1 a2),
   fun c o p h => h₂.access c o p (h₁.access c o p h)⟩

/-- A change outside `bc` is a frame of `bc`. -/
theorem FieldFrame.of_unch {m m' : mem} {S : block → Prop} {bc : block} (hu : Unch m m' S)
    (hb : ¬ S bc) (po so : ptrofs) : FieldFrame m m' bc po so :=
  ⟨fun c o _ _ => hu.load c bc o hb, fun c o p h => hu.access c bc o p hb h⟩

theorem load_apart {m m' : mem} {bc : block} {o : ptrofs} {v : val} {chunk : memory_chunk} {ofs : Z}
    (hst : Mem.store .Mint64 m bc (Ptrofs.unsigned o) v = some m') (h : Apart chunk ofs o) :
    Mem.load chunk m' bc ofs = Mem.load chunk m bc ofs := by
  apply Mem.load_store_other _ _ _ _ _ _ hst
  right
  rcases h with h | h
  · left; change intOfZ _ ≤ intOfZ _; rw [intOfZ_add]; exact h
  · right; change intOfZ _ ≤ intOfZ _; rw [intOfZ_add]; exact h

/-- A store into one of the two fields is a frame. -/
theorem FieldFrame.store {m m' : mem} {bc : block} {po so o : ptrofs} {v : val}
    (hst : Mem.store .Mint64 m bc (Ptrofs.unsigned o) v = some m') (ho : o = po ∨ o = so) :
    FieldFrame m m' bc po so :=
  ⟨fun _ _ a1 a2 => by rcases ho with rfl | rfl; exact load_apart hst a1; exact load_apart hst a2,
   fun _ _ _ h => Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ h⟩

/-- Another pair in `bc`, apart from the fields a frame may change, survives it. -/
theorem FieldDyn.frame {m m' : mem} {bc : block} {po so po' so' : ptrofs} {c cap : Nat} {b : block}
    (h : FieldDyn m bc po' so' c cap b) (hf : FieldFrame m m' bc po so)
    (h1 : Apart .Mint64 (Ptrofs.unsigned po') po) (h2 : Apart .Mint64 (Ptrofs.unsigned po') so)
    (h3 : Apart .Mint64 (Ptrofs.unsigned so') po) (h4 : Apart .Mint64 (Ptrofs.unsigned so') so)
    (hk : 0 < cap → Keep m m' b) : FieldDyn m' bc po' so' c cap b :=
  { h with
    capLd := by rw [hf.load _ _ h3 h4]; exact h.capLd
    capW := hf.access _ _ _ h.capW
    ptrW := hf.access _ _ _ h.ptrW
    ptr := fun hc => by rw [hf.load _ _ h1 h2]; exact h.ptr hc
    mal := fun hc => (h.mal hc).keep (hk hc)
    null := fun hc => by rw [hf.load _ _ h1 h2]; exact h.null hc }

theorem Malloced.valid {m : mem} {b : block} {N : Nat} (h : Malloced m b N) : Mem.valid_block m b :=
  Mem.perm_valid_block _ _ _ _ _ (h.perm (-1) (by decide) (by omega))

/-- A pair survives a change that leaves its block and its allocated block alone. -/
theorem FieldDyn.unch {m m' : mem} {bc : block} {po so : ptrofs} {c cap : Nat} {b : block}
    {S : block → Prop} (h : FieldDyn m bc po so c cap b) (hu : Unch m m' S) (hbc : ¬ S bc)
    (hb : 0 < cap → ¬ S b) : FieldDyn m' bc po so c cap b :=
  { h with
    capLd := by rw [hu.load _ _ _ hbc]; exact h.capLd
    capW := hu.access _ _ _ _ hbc h.capW
    ptrW := hu.access _ _ _ _ hbc h.ptrW
    ptr := fun hc => by rw [hu.load _ _ _ hbc]; exact h.ptr hc
    mal := fun hc => (h.mal hc).keep (Keep.unch hu (hb hc))
    null := fun hc => by rw [hu.load _ _ _ hbc]; exact h.null hc }

/-- A store into `bc` apart from the 8 bytes at `o` leaves them. -/
theorem load_apart' {m m' : mem} {bc : block} {o : ptrofs} {v : val} {chunk : memory_chunk} {ofs : Z}
    (hst : Mem.store chunk m bc ofs v = some m') (h : Apart chunk ofs o) :
    Mem.load .Mint64 m' bc (Ptrofs.unsigned o) = Mem.load .Mint64 m bc (Ptrofs.unsigned o) := by
  apply Mem.load_store_other _ _ _ _ _ _ hst
  right
  rcases h with h | h
  · right; change intOfZ _ ≤ intOfZ _; rw [intOfZ_add]; exact h
  · left; change intOfZ _ ≤ intOfZ _; rw [intOfZ_add]; exact h

/-- A pair survives a store into its block apart from its two fields. -/
theorem FieldDyn.store {m m' : mem} {bc : block} {po so : ptrofs} {c cap : Nat} {b : block}
    {chunk : memory_chunk} {ofs : Z} {w : val} (h : FieldDyn m bc po so c cap b)
    (hst : Mem.store chunk m bc ofs w = some m') (h1 : Apart chunk ofs po) (h2 : Apart chunk ofs so) :
    FieldDyn m' bc po so c cap b :=
  { h with
    capLd := by rw [load_apart' hst h2]; exact h.capLd
    capW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ h.capW
    ptrW := Mem.store_valid_access_1 _ _ _ _ _ _ hst _ _ _ _ h.ptrW
    ptr := fun hc => by rw [load_apart' hst h1]; exact h.ptr hc
    mal := fun hc => (h.mal hc).keep (Keep.unch (Unch.store hst rfl) (h.bne hc).symm)
    null := fun hc => by rw [load_apart' hst h1]; exact h.null hc }

/-- An allocated pair survives a `wp_dynalloc1F` on another pair of its block. -/
theorem FieldDyn.after {m m' : mem} {bc : block} {po so po' so' : ptrofs} {c cap cap2 : Nat}
    {b b2 b2' : block} (h : FieldDyn m bc po' so' c cap b)
    (hf : FieldFrame m m' bc po so)
    (hu : Unch m m' (fun z => z = bc ∨ (0 < cap2 ∧ z = b2) ∨ (¬ Mem.valid_block m b2' ∧ z = b2')))
    (hb2 : 0 < cap2 → b ≠ b2)
    (h1 : Apart .Mint64 (Ptrofs.unsigned po') po) (h2 : Apart .Mint64 (Ptrofs.unsigned po') so)
    (h3 : Apart .Mint64 (Ptrofs.unsigned so') po) (h4 : Apart .Mint64 (Ptrofs.unsigned so') so) :
    FieldDyn m' bc po' so' c cap b :=
  h.frame hf h1 h2 h3 h4 fun hc => Keep.unch hu fun hz => by
    rcases hz with hz | ⟨hp2, hz⟩ | ⟨hv, hz⟩
    · exact h.bne hc hz
    · exact hb2 hp2 hz
    · exact hv (hz ▸ (h.mal hc).valid)

/-- Reading field `f` of the struct a temporary points to. -/
theorem eval_fld {e : env} {le : temp_env} {m : mem} {p sid f : Common.AST.ident}
    {ty : Cfrontend.Ctypes.type} {chunk : memory_chunk} {bc : block} {cofs o : ptrofs} {v : val}
    (hp : PTree.get p le = some (.Vptr bc cofs))
    (hl : Exec.lvalOfField ge (.Tstruct sid Cfrontend.Ctypes.noattr) f (.Vptr bc cofs) = some (bc, o, .Full))
    (hmode : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hld : Mem.load chunk m bc (Ptrofs.unsigned o) = some v) :
    Exec.evalExpr ge e le m (fld p sid f ty) = some v := by
  simp only [Exec.evalExpr, hp, typeof, Exec.derefLoc,
    show Cfrontend.Ctypes.access_mode (.Tstruct sid Cfrontend.Ctypes.noattr) = .By_copy from rfl, hl,
    hmode, Mem.loadv]
  exact hld

theorem lval_fld {e : env} {le : temp_env} {m : mem} {p sid f : Common.AST.ident}
    {ty : Cfrontend.Ctypes.type} {bc : block} {cofs o : ptrofs}
    (hp : PTree.get p le = some (.Vptr bc cofs))
    (hl : Exec.lvalOfField ge (.Tstruct sid Cfrontend.Ctypes.noattr) f (.Vptr bc cofs) = some (bc, o, .Full)) :
    Exec.evalLvalue ge e le m (fld p sid f ty) = some (bc, o, .Full) := by
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, typeof, Exec.derefLoc,
    show Cfrontend.Ctypes.access_mode (.Tstruct sid Cfrontend.Ctypes.noattr) = .By_copy from rfl, hl]

theorem eval_binop {e : env} {le : temp_env} {m : mem} {op : Cfrontend.Cop.binary_operation}
    {a1 a2 : expr} {t : Cfrontend.Ctypes.type} {v1 v2 : val}
    (h1 : Exec.evalExpr ge e le m a1 = some v1) (h2 : Exec.evalExpr ge e le m a2 = some v2) :
    Exec.evalExpr ge e le m (.Ebinop op a1 a2 t) =
      Cfrontend.Cop.sem_binary_operation ge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m := by
  simp only [Exec.evalExpr, h1, h2]

theorem eval_cast {e : env} {le : temp_env} {m : mem} {a : expr} {t : Cfrontend.Ctypes.type} {v : val}
    (h : Exec.evalExpr ge e le m a = some v) :
    Exec.evalExpr ge e le m (.Ecast a t) = Cfrontend.Cop.sem_cast v (typeof a) t m := by
  simp only [Exec.evalExpr, h]

/-- `DYNALLOC1` on the pair in the fields `fp` (at `po`) and `fs` (at `so`)
of the struct at `bc`. -/
theorem wp_dynalloc1F {e : env} {f : function} {Q : Post} {le : temp_env} {m : mem}
    {p sid fp fs t1 t2 msg : Common.AST.ident} {elt : Cfrontend.Ctypes.type} {msgLen : Int}
    {bc b : block} {cofs po so : ptrofs} {c cap n : Nat} {szE : expr} {vx : val}
    (hp : PTree.get p le = some (.Vptr bc cofs))
    (hlp : Exec.lvalOfField ge (.Tstruct sid Cfrontend.Ctypes.noattr) fp (.Vptr bc cofs) =
      some (bc, po, .Full))
    (hls : Exec.lvalOfField ge (.Tstruct sid Cfrontend.Ctypes.noattr) fs (.Vptr bc cofs) =
      some (bc, so, .Full))
    (hc : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv elt) = c)
    (hD : FieldDyn m bc po so c cap b)
    (hx : ∀ m', Unch m m' (fun z => z = bc ∨ (0 < cap ∧ z = b)) →
      Exec.evalExpr ge e le m' szE = some vx)
    (hcast : ∀ m', Cfrontend.Cop.sem_cast vx (typeof szE) tulong m' = some (.Vlong (lr n)))
    (hn : n < 2147483648) (hcn : c * n < 2 ^ 62) (hpt1 : p ≠ t1) (hpt2 : p ≠ t2)
    (hQ : ∀ le' m' cap' b', FieldDyn m' bc po so c cap' b' → n ≤ cap' →
      Unch m m' (fun z => z = bc ∨ (0 < cap ∧ z = b) ∨ (¬ Mem.valid_block m b' ∧ z = b')) →
      FieldFrame m m' bc po so →
      ((cap' = cap ∧ b' = b ∧ m' = m) ∨
        (¬ Mem.valid_block m b' ∧ cap < cap' ∧ Zeros m' b' (c * cap'))) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ k, k ≠ t1 → k ≠ t2 → PTree.get k le' = PTree.get k le) →
      Q.normal E0 e le' m')
    (hnil : NoShadow e := by exact NautyVerified.Proofs.Alloc.noShadow_empty) :
    Wp xi ge f (dynalloc1F p sid fp fs elt szE t1 t2 msg msgLen) Q e le m := by
  have hnil3 := hnil _ _ E.find_free
  have hcap := hD.capLt
  have hcapE : ∀ m', Mem.load .Mint64 m' bc (Ptrofs.unsigned so) = some (.Vlong (lr cap)) →
      Exec.evalExpr ge e le m' (fld p sid fs tulong) = some (.Vlong (lr cap)) :=
    fun _ h => eval_fld hp hls rfl h
  wp_step; wp_step
  apply wp_if_eval
  rw [eval_binop ((eval_cast (hx m (Unch.refl _ _))).trans (hcast m)) (hcapE m hD.capLd)]
  simp only [typeof, cop]
  rw [ltu_lr (a := cap) (b := n) (by omega) (by omega)]
  by_cases hnc : cap < n
  · rw [ite_eq_left (by simpa using hnc)]
    wp_step
    -- `if (p->fs) free(p->fp);`
    have hfree : ∀ (Q' : Post), (∀ m1, Unch m m1 (fun z => 0 < cap ∧ z = b) →
        Mem.nextblock m1 = Mem.nextblock m → Q'.normal E0 e le m1) →
        Wp xi ge f (sk (.Sifthenelse (fld p sid fs tulong)
          (sk (.Scall none (.Evar Source.dense.id.free (tfun [tptr .Tvoid] .Tvoid))
            [fld p sid fp (tptr elt)])) .Sskip)) Q' e le m := by
      intro Q' hQ'
      wp_step; wp_step
      apply wp_if_eval
      rw [hcapE m hD.capLd]
      simp only [typeof, cop, eq_lr_zero (k := cap) (by omega)]
      by_cases h0 : cap = 0
      · rw [ite_eq_right (by simp [h0])]
        apply wp_skip
        exact hQ' m (Unch.refl _ _) rfl
      · rw [ite_eq_left (by simp [h0])]
        have hpos : 0 < cap := by omega
        wp_step; wp_step
        refine wp_call (vf := .Vptr E.free Ptrofs.zero) _ (freeSpec b (c * cap)) (free_satisfies b _) rfl
          (by simp [Exec.evalExpr, Exec.lvalOfVar, hnil3, E.find_free, Exec.derefLoc,
            Cfrontend.Ctypes.access_mode])
          (by simp only [Exec.evalExprlist]
              rw [eval_fld hp hlp rfl (hD.ptr hpos)]
              simp [typeof, cop])
          (by simp [Common.Globalenvs.Genv.find_funct, E.funct_free]) rfl ⟨rfl, hD.mal hpos⟩ ?_
        rintro t v m1 ⟨rfl, rfl, hu, hnb⟩
        exact hQ' m1 (hu.mono fun z hz => ⟨hpos, hz⟩) hnb
    refine hfree _ ?_
    intro m1 hu1 hnb1
    have hbc1 : ¬ (0 < cap ∧ bc = b) := fun ⟨hp', h⟩ => hD.bne hp' h.symm
    have hcapW1 := hu1.access _ _ _ _ hbc1 hD.capW
    have hptrW1 := hu1.access _ _ _ _ hbc1 hD.ptrW
    obtain ⟨m2, hst2⟩ := Mem.valid_access_store _ _ _ _ (.Vlong (lr n)) hcapW1
    have hx1 : Exec.evalExpr ge e le m1 szE = some vx :=
      hx m1 (hu1.mono fun z hz => .inr hz)
    wp_step; wp_step; wp_step
    apply wp_assign_eval
    rw [lval_fld hp hls, hx1]
    simp only [show typeof (fld p sid fs tulong) = tulong from rfl, hcast, Exec.assignLoc,
      Cfrontend.Ctypes.access_mode, Mem.storev, hst2]
    have hu2 : Unch m m2 (fun z => z = bc ∨ (0 < cap ∧ z = b)) :=
      (hu1.mono fun z hz => .inr hz).trans (Unch.store hst2 (.inl rfl))
    have hsz : Vptrofs (Ptrofs.repr (Cfrontend.Ctypes.sizeof ge.genv_cenv elt)) = .Vlong (lr c) := by
      rw [show Cfrontend.Ctypes.sizeof ge.genv_cenv elt = zOfInt c by
        rw [← hc, zOfInt_intOfZ], vptrofs_lr]
    wp_step; wp_step; wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr E.zalloc Ptrofs.zero) (targs := [tulong]) (tres := tptr .Tvoid)
      (cc := Common.AST.cc_default) _ (zallocSpec (n * c)) (zalloc_satisfies _) rfl
      (by simp [Exec.evalExpr, Exec.lvalOfVar, hnil _ _ E.find_zalloc, E.find_zalloc, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode])
      (by simp only [Exec.evalExprlist]
          rw [eval_binop ((eval_cast (hx m2 hu2)).trans (hcast m2))
            (eval_cast (show Exec.evalExpr ge e le m2 (.Esizeof elt tulong) = some _ from rfl))]
          simp [typeof, cop, hsz, lr_mul])
      (by simp [Common.Globalenvs.Genv.find_funct, E.funct_zalloc]) rfl
      ⟨rfl, by rw [Nat.mul_comm]; exact hcn⟩ ?_
    rintro t v m3 ⟨rfl, b', rfl, hfr, hz3⟩
    simp only [set_opttemp, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    have hptrW2 := Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _ hptrW1
    have hbc' : bc ≠ b' := fun h => hfr.new (h ▸ valid_of_access hptrW2)
    have hptrW3 := hfr.unch.access _ _ _ _ hbc' hptrW2
    obtain ⟨m4, hst4⟩ := Mem.valid_access_store _ _ _ _ (.Vptr b' Ptrofs.zero) hptrW3
    apply wp_assign_eval
    have hpt : PTree.get p (PTree.set t2 (.Vptr b' Ptrofs.zero) (PTree.set t1 (.Vptr b' Ptrofs.zero) le)) =
        some (.Vptr bc cofs) := by
      rw [temps_gso _ _ hpt2, temps_gso _ _ hpt1]; exact hp
    rw [lval_fld hpt hlp]
    simp only [Exec.evalExpr, temps_gss, typeof,
      cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev, Mptr_eq, hst4]
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
    have hap' : Apart .Mint64 (Ptrofs.unsigned so) po := by
      rcases hD.apart with h | h
      · right; exact h
      · left; exact h
    have hD' : FieldDyn m4 bc po so c n b' :=
      { capLd := by
          rw [load_apart hst4 hap', hfr.unch.load _ _ _ hbc', Mem.load_store_same _ _ _ _ _ _ hst2]
          rfl
        capW := Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _
          (hfr.unch.access _ _ _ _ hbc' (Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _ hcapW1))
        ptrW := Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _ hptrW3
        ptr := fun _ => by rw [Mem.load_store_same _ _ _ _ _ _ hst4]; rfl
        mal := fun _ =>
          { hdr := by
              rw [Mem.load_store_other _ _ _ _ _ _ hst4 _ _ _ (.inl hbc'.symm), hfr.hdr, Nat.mul_comm]
            perm := fun o h1 h2 => Mem.perm_store_1 _ _ _ _ _ _ hst4 _ _ _ _
              (hfr.perm o h1 (by rw [Nat.mul_comm]; exact h2))
            small := hcn }
        apart := hD.apart
        bne := fun _ => hbc'.symm
        small := hcn
        capLt := hn
        null := fun h0 => absurd h0 (by omega) }
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
    refine hQ _ m4 n b' hD' (Nat.le_refl _) ?_ ?_
      (.inr ⟨hnew, hnc, by
        rw [Nat.mul_comm]
        exact (Zeros.of_bytes hz3).unch (Unch.store hst4 rfl) hbc'⟩) hgrow ?_
    · exact (((hu1.mono fun z hz => .inr (.inl hz)).trans
        (Unch.store hst2 (.inl rfl))).trans (hfr.unch.mono fun z hz => .inr (.inr ⟨hz ▸ hnew, hz⟩))).trans
        (Unch.store hst4 (.inl rfl))
    · exact (((FieldFrame.of_unch hu1 hbc1 po so).trans (FieldFrame.store hst2 (.inr rfl))).trans
        (FieldFrame.of_unch hfr.unch hbc' po so)).trans (FieldFrame.store hst4 (.inl rfl))
    · intro k h1 h2
      rw [temps_gso _ _ h2, temps_gso _ _ h1]
  · rw [ite_eq_right (by simpa using hnc)]
    apply wp_skip
    exact hQ le m cap b hD (by omega) (Unch.refl _ _) (FieldFrame.refl _ _ _ _) (.inl ⟨rfl, rfl, rfl⟩)
      (fun _ h => h) (fun _ _ _ => rfl)

end NautyVerified.Proofs.Alloc

import NautyVerified.Proofs.Sparse.Bestcell.Spec
import NautyVerified.Proofs.Sparse.Bestcell.Syntax
import NautyVerified.Proofs.Sparse.Bestcell.Cells
import NautyVerified.Proofs.Sparse.Testcanlab.Satisfies
import NautyVerified.Proofs.Alloc.Dyn3

/-!
# What `bestcell_sg`'s loops read

`wp_dynW`: one of the four `DYNALLOC1`s, as a change of `Works` at one pair
(`fset` replaces one entry), with `Orig` recording that the new block is the
old one or new. `Frame`: after the allocations, the arguments and `SG_VDE`'s
pointers in temporaries, `work1b` pointing `n/2` entries into `work1`, the
graph, `lab` and `ptn` in memory, and the four pointer globals holding blocks
`w k`, distinct from each other and from everything read. `Mod m m' w`: only
those blocks changed, each keeping its `malloc` header.
-/

namespace NautyVerified.Proofs.Sparse.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse NautyVerified.Program
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat)
open NautyVerified.Proofs.Alloc (DynAt Keep)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

abbrev F := sparse.fn.«nausparse:bestcell_sg»

/-- `f` with entry `k` replaced by `x`. -/
def fset {α : Type} (f : Fin 4 → α) (k : Fin 4) (x : α) : Fin 4 → α :=
  fun j => if j = k then x else f j

theorem wp_ne_ws : ∀ j k : Fin 4, wp j ≠ ws k := by decide
theorem wp_ne : ∀ j k : Fin 4, j ≠ k → wp j ≠ wp k := by decide
theorem ws_ne : ∀ j k : Fin 4, j ≠ k → ws j ≠ ws k := by decide
theorem wglobs_cases : ∀ z ∈ wglobs, ∃ k, z = wp k ∨ z = ws k := by decide

/-- Each pair's block is the old one (with the old capacity) or was not valid in `m`. -/
def Orig (m : mem) (c : Fin 4 → Nat) (b : Fin 4 → block) (c' : Fin 4 → Nat)
    (b' : Fin 4 → block) : Prop :=
  ∀ k, (c' k = c k ∧ b' k = b k) ∨ ¬ Mem.valid_block m (b' k)

theorem Orig.refl (m : mem) (c : Fin 4 → Nat) (b : Fin 4 → block) : Orig m c b c b :=
  fun _ => .inl ⟨rfl, rfl⟩

theorem Orig.trans {m m1 : mem} {c c1 c2 : Fin 4 → Nat} {b b1 b2 : Fin 4 → block}
    (h1 : Orig m c b c1 b1) (h2 : Orig m1 c1 b1 c2 b2)
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m1 z) : Orig m c b c2 b2 := fun k => by
  rcases h2 k with ⟨e1, e2⟩ | hnv
  · rw [e1, e2]; exact h1 k
  · exact .inr fun hv => hnv (hg _ hv)

section
variable {m : mem} {c : Fin 4 → Nat} {b : Fin 4 → block}

theorem Works.glob_valid (h : Works m c b) : ∀ z ∈ wglobs, Mem.valid_block m z := fun z hz => by
  obtain ⟨k, rfl | rfl⟩ := wglobs_cases z hz
  · exact Alloc.valid_of_access (h.dyn k).bpW
  · exact Alloc.valid_of_access (h.dyn k).bsW

theorem Works.valid (h : Works m c b) (k : Fin 4) (hc : 0 < c k) : Mem.valid_block m (b k) :=
  Alloc.Malloced.valid ((h.dyn k).mal hc)

theorem worksSet_mono {m1 : mem} {c1 : Fin 4 → Nat} {b1 : Fin 4 → block} (ho : Orig m c b c1 b1)
    (hg : ∀ z, Mem.valid_block m z → Mem.valid_block m1 z) :
    ∀ z, worksSet m1 c1 b1 z → worksSet m c b z := by
  rintro z (h | ⟨k, hk, rfl⟩ | h)
  · exact .inl h
  · rcases ho k with ⟨e1, e2⟩ | hnv
    · exact .inr (.inl ⟨k, e1 ▸ hk, e2⟩)
    · exact .inr (.inr hnv)
  · exact .inr (.inr fun hv => h (hg _ hv))

/-- After the run, every block that changed is one `worksSet` allows. -/
theorem worksSet_of {c1 : Fin 4 → Nat} {b1 : Fin 4 → block} (ho : Orig m c b c1 b1)
    (hc : ∀ k, 0 < c1 k) : ∀ z, (∃ k, z = b1 k) → worksSet m c b z := by
  rintro z ⟨k, rfl⟩
  rcases ho k with ⟨e1, e2⟩ | hnv
  · exact .inr (.inl ⟨k, e1 ▸ hc k, e2⟩)
  · exact .inr (.inr hnv)

end

/-- One `DYNALLOC1(int, work<k>, work<k>_sz, n, "bestcell_sg")`. -/
theorem wp_dynW {Q : Logic.Post} {le : temp_env} {m : mem} {c : Fin 4 → Nat} {b : Fin 4 → block}
    {n : Nat} (k : Fin 4) {x y t1 t2 : ident}
    (hgs : Genv.find_symbol sge.genv_genv x = some (ws k))
    (hgp : Genv.find_symbol sge.genv_genv y = some (wp k))
    (hW : Works m c b) (hx : PTree.get id.n le = some (.Vint (ir n))) (hn : n < 1073741824)
    (hQ : ∀ le' m' cap' b', Works m' (fset c k cap') (fset b k b') → n ≤ cap' →
      Orig m c b (fset c k cap') (fset b k b') → Unch m m' (worksSet m c b) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ z, z ≠ t1 → z ≠ t2 → PTree.get z le' = PTree.get z le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F (dyn x y t1 t2) Q empty_env le m := by
  refine Alloc.wp_dynalloc1 (E := NautyEnv.sparse) hgs hgp rfl (hW.dyn k) hx (by omega)
    (show 4 * n < 2 ^ 62 by omega) ?_
  intro le' m' cap' b' hD' hle hu hor hg ho
  have hS : ∀ z, Mem.valid_block m z → z ≠ ws k → z ≠ wp k → (0 < c k → z ≠ b k) →
      ¬ (z = ws k ∨ z = wp k ∨ (0 < c k ∧ z = b k) ∨ (¬ Mem.valid_block m b' ∧ z = b')) :=
    fun z hv h1 h2 h3 => Alloc.not_dynSet hv h1 h2 h3
  have hvp : ∀ j, Mem.valid_block m (wp j) := fun j => Alloc.valid_of_access (hW.dyn j).bpW
  have hvs : ∀ j, Mem.valid_block m (ws j) := fun j => Alloc.valid_of_access (hW.dyn j).bsW
  have hap : ∀ j, 0 < c j → ∀ z ∈ wglobs, b j ≠ z := fun j hc z hz h => hW.apart j hc (h ▸ hz)
  refine hQ le' m' cap' b' ⟨fun j => ?_, fun j hc => ?_, fun j j' hjj hc hc' => ?_⟩ hle
    (fun j => ?_) (hu.mono fun z hz => ?_) hg ho
  · by_cases hj : j = k
    · subst hj; simp only [fset, ite_true]; exact hD'
    · simp only [fset, ite_eq_right hj]
      refine (hW.dyn j).keep hu
        (hS _ (hvp j) (wp_ne_ws j k) (wp_ne j k hj) fun hc h => hap k hc _ (wp_mem j) h.symm)
        (hS _ (hvs j) (ws_ne j k hj) (fun h => wp_ne_ws k j h.symm)
          fun hc h => hap k hc _ (ws_mem j) h.symm)
        fun hc => Keep.unch hu (hS _ (hW.valid j hc) (hap j hc _ (ws_mem k)) (hap j hc _ (wp_mem k))
          fun hck => hW.distinct j k hj hc hck)
  · by_cases hj : j = k
    · subst hj
      simp only [fset, ite_true] at hc ⊢
      rcases hor with ⟨rfl, rfl⟩ | hnv
      · exact hW.apart j hc
      · exact fun hm => hnv (hW.glob_valid _ hm)
    · simp only [fset, ite_eq_right hj] at hc ⊢
      exact hW.apart j hc
  · by_cases hj : j = k
    · subst hj
      have hj' : j' ≠ j := fun h => hjj h.symm
      simp only [fset, ite_true, ite_eq_right hj'] at hc hc' ⊢
      rcases hor with ⟨rfl, rfl⟩ | hnv
      · exact hW.distinct j j' hjj hc hc'
      · exact fun h => hnv (h ▸ hW.valid j' hc')
    · by_cases hj' : j' = k
      · subst hj'
        simp only [fset, ite_true, ite_eq_right hj] at hc hc' ⊢
        rcases hor with ⟨rfl, rfl⟩ | hnv
        · exact hW.distinct j j' hjj hc hc'
        · exact fun h => hnv (h ▸ hW.valid j hc)
      · simp only [fset, ite_eq_right hj, ite_eq_right hj'] at hc hc' ⊢
        exact hW.distinct j j' hjj hc hc'
  · by_cases hj : j = k
    · subst hj; simp only [fset, ite_true]; exact hor
    · exact .inl ⟨by simp [fset, hj], by simp [fset, hj]⟩
  · rcases hz with rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩
    · exact .inl (ws_mem k)
    · exact .inl (wp_mem k)
    · exact .inr (.inl ⟨k, hc, rfl⟩)
    · exact .inr (.inr hnv)

/-! ## The frame of the loops -/

structure Frame {n : Nat} (m : mem) (le : temp_env) (G : Hex.SparseGraph n) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (bl : block)
    (lofs : ptrofs) (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat) (level : Nat)
    (w : Fin 4 → block) (o1b : ptrofs) : Prop where
  hlab : PTree.get id.lab le = some (.Vptr bl lofs)
  hptn : PTree.get id.ptn le = some (.Vptr bp pofs)
  hlev : PTree.get id.level le = some (.Vint (ir level))
  hn : PTree.get id.n le = some (.Vint (ir n))
  hv : PTree.get id.v le = some (.Vptr bv vo)
  hd : PTree.get id.d le = some (.Vptr bd dofs)
  he : PTree.get id.e le = some (.Vptr be eo)
  h1b : PTree.get id.work1b le = some (.Vptr (w 0) o1b)
  o1b : intOfZ (Ptrofs.unsigned o1b) = 0 + csize .Mint32 * ((n / 2 : Nat) : Int)
  varr : ArrayAt m .Mint64 bv (intOfZ (Ptrofs.unsigned vo)) (vVals G) n
  darr : ArrayAt m .Mint32 bd (intOfZ (Ptrofs.unsigned dofs)) (dVals G) n
  earr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size
  larr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n
  lsmall : ∀ j < n, lab[j]! < n
  linj : ∀ a b, a < n → b < n → lab[a]! = lab[b]! → a = b
  lonto : ∀ p < n, ∃ j < n, lab[j]! = p
  parr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n
  psize : ptn.size = n
  psmall : ∀ x < n, ptn[x]! < 2147483648
  plast : ptn[n - 1]! ≤ level
  levlt : level < 2147483648
  wptr : ∀ k, Mem.load .Mint64 m (wp k) (zOfInt 0) = some (.Vptr (w k) Ptrofs.zero)
  wdist : ∀ k k', k ≠ k' → w k ≠ w k'
  wapart : ∀ k, ∀ z ∈ [bv, bd, be, bl, bp] ++ wglobs, w k ≠ z
  n0 : 0 < n
  nlt : n < 1073741824

/-- The temporaries the loops read but never set. -/
def Args (x : ident) : Prop :=
  x = id.lab ∨ x = id.ptn ∨ x = id.level ∨ x = id.n ∨ x = id.v ∨ x = id.d ∨ x = id.e ∨
    x = id.work1b

instance (x : ident) : Decidable (Args x) := by unfold Args; infer_instance

/-- Only the four blocks changed, each keeping its header. -/
def Mod (m m' : mem) (w : Fin 4 → block) : Prop :=
  Unch m m' (fun z => ∃ k, z = w k) ∧ ∀ k, Keep m m' (w k)

theorem Mod.refl (m : mem) (w : Fin 4 → block) : Mod m m w :=
  ⟨Unch.refl _ _, fun _ => Keep.refl _ _⟩

theorem Mod.trans {m₁ m₂ m₃ : mem} {w : Fin 4 → block} (h₁ : Mod m₁ m₂ w) (h₂ : Mod m₂ m₃ w) :
    Mod m₁ m₃ w :=
  ⟨h₁.1.trans h₂.1, fun k => (h₁.2 k).trans (h₂.2 k)⟩

section
variable {n : Nat} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {bv : block} {vo : ptrofs}
  {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {bl : block} {lofs : ptrofs}
  {lab : Array Nat} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {level : Nat}
  {w : Fin 4 → block} {o1b : ptrofs}

theorem Frame.temps (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    {le' : temp_env} (hle : ∀ x, Args x → PTree.get x le' = PTree.get x le) :
    Frame m le' G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b :=
  { h with
    hlab := by rw [hle _ (by decide)]; exact h.hlab
    hptn := by rw [hle _ (by decide)]; exact h.hptn
    hlev := by rw [hle _ (by decide)]; exact h.hlev
    hn := by rw [hle _ (by decide)]; exact h.hn
    hv := by rw [hle _ (by decide)]; exact h.hv
    hd := by rw [hle _ (by decide)]; exact h.hd
    he := by rw [hle _ (by decide)]; exact h.he
    h1b := by rw [hle _ (by decide)]; exact h.h1b }

/-- A store to `w k` and a change of a block `w k` changes nothing else. -/
theorem Frame.not_w (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    {z : block} (hz : z ∈ [bv, bd, be, bl, bp] ++ wglobs) : ¬ ∃ k, z = w k := by
  rintro ⟨k, rfl⟩
  exact h.wapart k _ hz rfl

theorem Frame.unch (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    {m' : mem} (hu : Unch m m' (fun z => ∃ k, z = w k)) :
    Frame m' le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b :=
  { h with
    varr := h.varr.unch hu (h.not_w (by simp))
    darr := h.darr.unch hu (h.not_w (by simp))
    earr := h.earr.unch hu (h.not_w (by simp))
    larr := h.larr.unch hu (h.not_w (by simp))
    parr := h.parr.unch hu (h.not_w (by simp))
    wptr := fun k => by
      rw [hu.load _ _ _ (h.not_w (List.mem_append_right _ (wp_mem k)))]; exact h.wptr k }

/-- A change of block `w k` alone. -/
theorem Frame.mod (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    {m' : mem} (k : Fin 4) (hu : Unch m m' (· = w k)) (hk : Keep m m' (w k)) : Mod m m' w :=
  ⟨hu.mono fun _ hz => ⟨k, hz⟩, fun j => by
    by_cases hj : j = k
    · subst hj; exact hk
    · exact Keep.unch hu (h.wdist j k hj)⟩

/-- A change of `w 2` and `w 3` alone. -/
theorem Frame.mod23 (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    {m' : mem} (hu : Unch m m' (fun z => z = w 2 ∨ z = w 3)) (hk2 : Keep m m' (w 2))
    (hk3 : Keep m m' (w 3)) : Mod m m' w :=
  ⟨hu.mono fun _ hz => hz.elim (fun e => ⟨2, e⟩) (fun e => ⟨3, e⟩), fun k => by
    match k with
    | 0 => exact Keep.unch hu (by
        rintro (e | e)
        · exact h.wdist 0 2 (by decide) e
        · exact h.wdist 0 3 (by decide) e)
    | 1 => exact Keep.unch hu (by
        rintro (e | e)
        · exact h.wdist 1 2 (by decide) e
        · exact h.wdist 1 3 (by decide) e)
    | 2 => exact hk2
    | 3 => exact hk3⟩

theorem Frame.not23 (h : Frame m le G bv vo bd dofs be eo bl lofs lab bp pofs ptn level w o1b)
    (k : Fin 4) (hk : k = 0 ∨ k = 1) : ¬ (w k = w 2 ∨ w k = w 3) := by
  rcases hk with rfl | rfl <;> rintro (e | e)
  · exact h.wdist 0 2 (by decide) e
  · exact h.wdist 0 3 (by decide) e
  · exact h.wdist 1 2 (by decide) e
  · exact h.wdist 1 3 (by decide) e

end

/-! ## Reading and writing the work arrays -/

theorem eval_gvar {le : temp_env} {m : mem} {x : ident} {k : Fin 4} {bw : block}
    (hx : Genv.find_symbol sge.genv_genv x = some (wp k))
    (h : Mem.load .Mint64 m (wp k) (zOfInt 0) = some (.Vptr bw Ptrofs.zero)) :
    Exec.evalExpr sge empty_env le m (.Evar x (tptr tint)) = some (.Vptr bw Ptrofs.zero) := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get x (empty_env : env) = none from rfl,
    hx, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, Alloc.Mptr_eq]
  exact h

/-- Writing `p[a] = x` where `p` points `off` elements into an array of `N`. -/
theorem wp_store_off {f : function} {Q : Logic.Post} {e : env} {le : temp_env} {m : mem} {pe : expr}
    {bo : block} {ofs : ptrofs} {vals : Nat → val} {N off : Nat} {base : Int}
    (harr : ArrayAt m .Mint32 bo base vals N) (hN : N < 2147483648)
    (hp : Exec.evalExpr sge e le m pe = some (.Vptr bo ofs)) (hpty : typeof pe = tptr tint)
    (hofs : intOfZ (Ptrofs.unsigned ofs) = base + csize .Mint32 * (off : Int))
    (a : expr) (c : Nat) (hc : off + c < N)
    (ha : Exec.evalExpr sge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (rty : Cfrontend.Ctypes.type) (hrty : typeof rhs = rty) (v wv : val)
    (hrhs : Exec.evalExpr sge e le m rhs = some v)
    (hcast : Cfrontend.Cop.sem_cast v rty tint m = some wv)
    (hw : Val.load_result .Mint32 wv = wv)
    (hQ : ∀ m', ArrayAt m' .Mint32 bo base (upd vals (off + c) wv) N →
      Unch m m' (· = bo) → Alloc.Keep m m' bo → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 e le m') :
    Wp xi sge f (.Sassign (.Ederef (.Ebinop .Oadd pe a (tptr tint)) tint) rhs) Q e le m := by
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc wv hw
  have hf := harr.fits
  have hb := harr.base_nonneg
  have haddr : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof sge.genv_cenv tint)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint32 base (off + c) := by
    rw [← elemOfs_slice]
    apply addr_elem ofs _ .Mint32 rfl hofs (by omega)
    simp only [show csize .Mint32 = 4 from rfl] at hf ⊢
    omega
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hpty, hrhs, hrty]
  simp only [typeof, cop, hcast, Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
  rw [haddr, hst]
  exact hQ m' harr' (Unch.store hst rfl) (Alloc.Keep.store hst (by
    simp only [elemOfs, intOfZ_zOfInt, show csize .Mint32 = 4 from rfl]
    omega))
    (fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz)

/-- Reading `p[a]` where `p` points `off` elements into an array of `N`. -/
theorem eval_off {e : env} {le : temp_env} {m : mem} {pe : expr}
    {bo : block} {ofs : ptrofs} {vals : Nat → val} {N off : Nat} {base : Int}
    (harr : ArrayAt m .Mint32 bo base vals N) (hN : N < 2147483648)
    (hp : Exec.evalExpr sge e le m pe = some (.Vptr bo ofs)) (hpty : typeof pe = tptr tint)
    (hofs : intOfZ (Ptrofs.unsigned ofs) = base + csize .Mint32 * (off : Int))
    (a : expr) (c : Nat) (hc : off + c < N)
    (ha : Exec.evalExpr sge e le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr sge e le m (.Ederef (.Ebinop .Oadd pe a (tptr tint)) tint) = some (vals (off + c)) := by
  have hs := harr.slice off (N - off) (by omega)
  rw [← hofs] at hs
  exact eval_idx hs (by omega) hp hpty rfl rfl a c (by omega) ha hty

end NautyVerified.Proofs.Sparse.Bestcell

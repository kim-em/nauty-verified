import NautyVerified.Proofs.Sparse.Ints.Main

/-!
# `sortints` meets its specification

`sortintsSpec C X start len`: called with `x` pointing at element `start`
of the array of `C` (holding `X`) and `n = len` with `start + len ≤ N`,
nausparse.c's `sortints` leaves in the array `X` with the segment
`[start, start + len)` replaced by HexGraphIso's `sortCells` of it, changes no
other block that was valid before the call, keeps every such block's
permissions and `malloc` header, and emits no events.

The precondition `1 ≤ start` or "the segment has no repeated entry" is what
keeps the template's inclusive right cursor (`xc`) inside the array, as
CompCert compares pointers only when both are (weakly) valid. `refine_sg`
calls `sortints(HITCELL, hitcells)` at the base of `work4`, on distinct cell
starts.
-/

namespace NautyVerified.Proofs.Sparse.Sort.Ints

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Spec.SortC
open NautyVerified.Source

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

def sortintsSpec (C : Ctx) (X : Array Nat) (start len : Nat) : FunSpec where
  pre args m := args = [.Vptr C.bx (pt C.base start), .Vint (ir len)] ∧
    C.Ok ∧ Arr m C X ∧ (1 ≤ start ∨ Win X start (start + len)) ∧ start + len ≤ C.N
  post _ m t _ m' := t = E0 ∧ (∃ Z, Arr m' C Z ∧
      Z.extract start (start + len) = Hex.GraphIso.Nauty.Sparse.sortCells (X.extract start (start + len)) ∧
      ∀ q, q < start ∨ start + len ≤ q → Z[q]! = X[q]!) ∧
    Unch m m' (fun z => z = C.bx ∨ ¬ Mem.valid_block m z) ∧
    ∀ b, Mem.valid_block m b → Alloc.Keep m m' b

/-- The temporaries on entry. -/
def sTemps (C : Ctx) (start len : Nat) : temp_env :=
  PTree.set id.«n» (.Vint (ir len))
    (PTree.set id.«x» (.Vptr C.bx (pt C.base start))
      (create_undef_temps sparse.fn.«nausparse:sortints».fn_temps))

set_option maxRecDepth 100000 in
theorem sortints_vars :
    sparse.fn.«nausparse:sortints».fn_vars = [(id.«stack», tarray entry 40)] := rfl

set_option maxRecDepth 100000 in
theorem sizeof_stack : sizeof sge.genv_cenv (tarray entry 40) = zOfInt 640 := rfl

omit binary64_certificate binary32_certificate in
/-- A fresh stack is writable and freeable throughout, and empty. -/
theorem stack_alloc {m m1 : mem} {bs : block} {C : Ctx}
    (h : Mem.alloc m (zOfInt 0) (zOfInt 640) = (m1, bs)) : StackAt m1 C bs [] := by
  have hp : ∀ o : Int, 0 ≤ o → o < 640 → Mem.perm m1 bs (zOfInt o) .Cur .Freeable := fun o h0 h1 =>
    Mem.perm_alloc_2 _ _ _ _ _ h _ _ ⟨by
      change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt]; exact h0, by
      change intOfZ _ < intOfZ _; simp [intOfZ_zOfInt]; exact h1⟩
  have hp' : ∀ o : Z, 0 ≤ intOfZ o → intOfZ o < 640 → Mem.perm m1 bs o .Cur .Freeable := fun o h0 h1 => by
    have := hp (intOfZ o) h0 h1; rwa [zOfInt_intOfZ] at this
  have va : ∀ (c : memory_chunk) (o : Int) (w a : Int), intOfZ (Common.Memdata.size_chunk c) = w →
      intOfZ (Common.Memdata.align_chunk c) = a → 0 ≤ o → o + w ≤ 640 → a ∣ o →
      Mem.valid_access m1 c bs (zOfInt o) .Writable := by
    intro c o w a hw ha h0 h1 hd
    refine ⟨fun o' ho' => Mem.perm_implies _ _ _ _ _ _ (hp' o' ?_ ?_) (.perm_F_any _), ?_⟩
    · have := ho'.1; change intOfZ _ ≤ intOfZ _ at this; simp [intOfZ_zOfInt] at this; omega
    · have := ho'.2; change intOfZ _ < intOfZ (ZArith.BinInt.Z.add _ _) at this
      simp [intOfZ_add, intOfZ_zOfInt, hw] at this; omega
    · obtain ⟨k, hk⟩ := hd
      refine ⟨zOfInt k, ?_⟩
      apply intOfZ_injective
      simp [intOfZ_mul, intOfZ_zOfInt, ha, hk, Int.mul_comm]
  refine ⟨by simp, fun i hi => va _ _ 8 8 rfl rfl (by omega) (by omega) ⟨2 * i, by omega⟩,
    fun i hi => va _ _ 4 4 rfl rfl (by omega) (by omega) ⟨4 * i + 2, by omega⟩,
    fun o ho => hp' o ho.1 ho.2, fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp)⟩

theorem sortints_satisfies {xi : ExternalCalls} (C : Ctx) (X : Array Nat) (start len : Nat) :
    Satisfies xi sge (.Internal sparse.fn.«nausparse:sortints») (sortintsSpec C X start len) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m => ∃ bs, e = sEnv bs ∧ le = sTemps C start len ∧
      Mem.alloc m₀ (zOfInt 0) (zOfInt 640) = (m, bs)) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    obtain ⟨m1, bs⟩ := Mem.alloc m (zOfInt 0) (zOfInt 640) |> fun p => (p.1, p.2)
    have hal : Mem.alloc m (zOfInt 0) (zOfInt 640) = ((Mem.alloc m (zOfInt 0) (zOfInt 640)).1,
        (Mem.alloc m (zOfInt 0) (zOfInt 640)).2) := rfl
    refine ⟨sEnv (Mem.alloc m (zOfInt 0) (zOfInt 640)).2, sTemps C start len,
      (Mem.alloc m (zOfInt 0) (zOfInt 640)).1, ⟨?_, ?_, ?_, ?_, rfl⟩, _, rfl, rfl, hal⟩
    · rw [sortints_vars]; exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
    · rw [sortints_vars]
      exact .cons _ _ _ _ _ _ _ _ _ (by rw [sizeof_stack]; exact hal) (.nil _ _)
  · rintro args m₀ ⟨rfl, hC, hX, hs1, hsN⟩
    rw [triple_iff_wp]
    rintro e le m ⟨bs, rfl, rfl, hal⟩
    rw [sparse.fn.«nausparse:sortints».fn_body_eq, body_eq]
    have hN := hC.nN
    have hfresh : ¬ Mem.valid_block m₀ bs := Mem.fresh_block_alloc _ _ _ _ _ hal
    have hvx : Mem.valid_block m₀ C.bx := by
      have hw := hX.arr.writable 0 hC.pos
      exact Mem.perm_valid_block _ _ _ _ _ (hw.1 _ ⟨Int.le_refl _, by
        change intOfZ _ < intOfZ (ZArith.BinInt.Z.add _ _)
        rw [intOfZ_add]; have : intOfZ (Common.Memdata.size_chunk .Mint32) = 4 := rfl; omega⟩)
    have hbx : bs ≠ C.bx := fun h => hfresh (h ▸ hvx)
    have hu0 : Unch m₀ m (· = bs) := Alloc.Unch.alloc hal
    have hX1 : Arr m C X := Arr.unch hu0 (Ne.symm hbx) hX
    have hS1 : StackAt m C bs [] := stack_alloc hal
    have hkeep0 : ∀ b, Mem.valid_block m₀ b → Alloc.Keep m₀ m b := fun b hb =>
      (Alloc.KeepV.alloc hal b hb).1
    -- the end of the body: free the stack
    have fin : ∀ (le' : temp_env) (m' : mem), Arr m' C (Hex.GraphIso.Nauty.Sparse.Sort.indirect X C.Y start len) →
        StackAt m' C bs [] → Unch m m' (fun z => z = C.bx ∨ z = bs) → Alloc.KeepA m m' →
        ∃ mf, Mem.free_list m' (blocks_of_env sge (sEnv bs)) = some mf ∧
          (sortintsSpec C X start len).post [.Vptr C.bx (pt C.base start),
            .Vint (ir len)] m₀ E0 .Vundef mf := by
      intro le' m' h' hS' hu' hk'
      obtain ⟨mf, hf⟩ := Mem.range_perm_free m' bs _ _ hS'.free
      have hblocks : blocks_of_env sge (sEnv bs) =
          [(bs, zOfInt 0, sizeof sge.genv_cenv (tarray entry 40))] := rfl
      have huf : Unch m' mf (· = bs) := Alloc.Unch.free hf
      have hxs : X.size = C.N := hX.size
      refine ⟨mf, by rw [hblocks, sizeof_stack]; simp only [Mem.free_list, hf], rfl,
        ⟨_, Arr.unch huf (Ne.symm hbx) h',
          indirect_ident X C.Y start len 2147483648 (by omega) (fun i hi => hC.yid i hi)
            (fun q _ hq => by have := hX.bnd q (by omega); rwa [hC.ysize] at this),
          fun q hq => Hex.GraphIso.Nauty.Sparse.Sort.indirect_outside X C.Y start len q
            (by omega) hq⟩, ?_, fun b hb => ?_⟩
      · refine (hu0.mono fun z hz => .inr (hz ▸ hfresh)).trans
          ((hu'.mono fun z hz => hz.elim .inl fun h => .inr (h ▸ hfresh)).trans
            (huf.mono fun z hz => .inr (hz ▸ hfresh)))
      · have hbb : b ≠ bs := fun h => hfresh (h ▸ hb)
        exact ((hkeep0 b hb).trans (hk' b)).trans (Alloc.Keep.unch huf hbb)
    simp only [body, sk]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, E0_append]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp (disch := decide) only [Exec.evalExpr, sTemps, temps_gso, temps_gss, typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 1) = ir ((1 : Nat) : Int) from rfl,
      key_cmp 1 len (by decide) (by omega)]
    have hP0 : Pend start (start + len) len [] := ⟨fun _ h => absurd h (by simp), fun _ h => absurd h (by simp)⟩
    by_cases h1 : 1 < len
    · rw [ite_eq_left (by simpa using h1)]
      refine wp_push (l := []) (le := PTree.set id.«top» (.Vint (Lib.Integers.Int.repr (zOfInt 0)))
        (sTemps C start len)) hS1 (by decide) (by rw [temps_gss]; rfl)
        (pv id.«x») (tv id.«n») start len
        (fun _ => by simp (disch := decide) only [pv, Exec.evalExpr, sTemps, temps_gso, temps_gss])
        rfl (fun _ => by simp (disch := decide) only [tv, Exec.evalExpr, sTemps, temps_gso, temps_gss])
        rfl ?_
      intro m2 hS2 hu2 hk2
      simp only [seqPost, Post.after, E0_append]
      have hP1 : Pend start (start + len) len [(start, len)] :=
        ⟨fun q hq => by simp at hq; subst hq; simp; omega, fun i hi => by
          simp at hi; subst hi; simp⟩
      refine wp_mainLoop (fuel := 2 * len + 1) hC hbx hsN hs1
        (Arr.unch hu2 (Ne.symm hbx) hX1) hS2 hP1 (.inr (by simp [wt]; omega))
        (by simp) ?_
      intro le' m' h' hS' hu' hk'
      rw [List.nil_append, List.reverse_singleton, show [(start, len)] = (if len > 1 then [(start, len)] else [])
        by simp; omega, ← indirect_eq] at h'
      exact fin le' m' h' hS' ((hu2.mono fun z hz => .inr hz).trans hu') (hk2.trans hk')
    · rw [ite_eq_right (by simpa using h1)]
      apply wp_skip
      simp only [E0_append]
      refine wp_mainLoop (fuel := 2 * len + 1) (l := []) hC hbx hsN hs1 hX1 hS1 hP0 (.inl rfl)
        (by rw [temps_gss]; rfl) ?_
      intro le' m' h' hS' hu' hk'
      rw [List.reverse_nil, show ([] : List (Nat × Nat)) = (if len > 1 then [(start, len)] else [])
        by simp; omega, ← indirect_eq] at h'
      exact fin le' m' h' hS' hu' hk'

end NautyVerified.Proofs.Sparse.Sort.Ints

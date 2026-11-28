import NautyVerified.Proofs.Sparse.Ints.Frame
import NautyVerified.Proofs.Sparse.Blocks

/-!
# The work stack

`sortints` keeps its pending segments in the local
`struct {int *addr; int len;} stack[40]`, 16 bytes an entry (`addr` at 0,
`len` at 8), in the block `bs` of its environment. `StackAt m C bs l`: the
first `l.length` entries hold `l` (bottom first), as cursors into the array
of `C`, and the whole stack is writable and freeable. `wp_push` and
`eval_pop*` are `push p l` and the two reads of `stack[top]`.
-/

namespace NautyVerified.Proofs.Sparse.Sort.Ints

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {C : Ctx}

section Layout
omit binary64_certificate binary32_certificate

set_option maxRecDepth 100000 in
theorem sizeof_entry : sizeof sge.genv_cenv entry = zOfInt 16 := rfl

set_option maxRecDepth 100000 in
theorem lval_addr (b : block) (o : ptrofs) :
    Exec.lvalOfField sge entry id.«addr» (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 0)), .Full) := rfl

set_option maxRecDepth 100000 in
theorem lval_len (b : block) (o : ptrofs) :
    Exec.lvalOfField sge entry id.«len» (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt 8)), .Full) := rfl

end Layout

/-- The environment of `sortints`: `stack` at block `bs`. -/
abbrev sEnv (bs : block) : env := PTree.set id.«stack» (bs, tarray entry 40) empty_env

/-- The stack holds `l`, bottom first. -/
structure StackAt (m : mem) (C : Ctx) (bs : block) (l : List (Nat × Nat)) : Prop where
  len : l.length ≤ 40
  wr64 : ∀ i : Nat, i < 40 → Mem.valid_access m .Mint64 bs (zOfInt (16 * (i : Int))) .Writable
  wr32 : ∀ i : Nat, i < 40 → Mem.valid_access m .Mint32 bs (zOfInt (16 * (i : Int) + 8)) .Writable
  free : Mem.range_perm m bs (zOfInt 0) (zOfInt 640) .Cur .Freeable
  addr : ∀ i < l.length, Mem.load .Mint64 m bs (zOfInt (16 * i)) =
    some (.Vptr C.bx (pt C.base l[i]!.1))
  size : ∀ i < l.length, Mem.load .Mint32 m bs (zOfInt (16 * i + 8)) = some (.Vint (ir l[i]!.2))

section
omit binary64_certificate binary32_certificate

/-- Changes outside the stack block keep it. -/
theorem StackAt.unch {m m' : mem} {S : block → Prop} (hu : Unch m m' S) {bs : block}
    (hb : ¬ S bs) {l : List (Nat × Nat)} (h : StackAt m C bs l) : StackAt m' C bs l where
  len := h.len
  wr64 i hi := hu.access _ _ _ _ hb (h.wr64 i hi)
  wr32 i hi := hu.access _ _ _ _ hb (h.wr32 i hi)
  free o ho := by
    have hv : Mem.valid_access m .Mint8unsigned bs o .Freeable :=
      ⟨fun o' ho' => by
        have : o' = o := by
          apply intOfZ_injective
          have := ho'.1; have := ho'.2
          change intOfZ _ ≤ intOfZ _ at *
          change intOfZ _ < intOfZ (ZArith.BinInt.Z.add _ _) at *
          simp only [intOfZ_add] at *
          have h1 : intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 := rfl
          omega
        subst this; exact h.free o' ho, ⟨o, by
          apply intOfZ_injective; simp [Common.Memdata.align_chunk]⟩⟩
    exact (hu.access _ _ _ _ hb hv).1 o ⟨Int.le_refl _, by
      change intOfZ _ < intOfZ (ZArith.BinInt.Z.add _ _)
      simp only [intOfZ_add]
      have h1 : intOfZ (Common.Memdata.size_chunk .Mint8unsigned) = 1 := rfl
      omega⟩
  addr i hi := by rw [hu.load _ _ _ hb]; exact h.addr i hi
  size i hi := by rw [hu.load _ _ _ hb]; exact h.size i hi

end

/-- The location of `stack[top].f`, `δ` the field's offset. -/
theorem lval_stk {le : temp_env} {m : mem} {bs : block} {k : Nat}
    (hk : k < 40) (htop : PTree.get id.«top» le = some (.Vint (ir k))) :
    Exec.evalLvalue sge (sEnv bs) le m (stk id.«addr» (tptr tint)) =
      some (bs, Ptrofs.add (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr (zOfInt 16))
        (Ptrofs.of_ints (ir (k : Int))))) (Ptrofs.repr (zOfInt 0)), .Full) ∧
    Exec.evalLvalue sge (sEnv bs) le m (stk id.«len» tint) =
      some (bs, Ptrofs.add (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr (zOfInt 16))
        (Ptrofs.of_ints (ir (k : Int))))) (Ptrofs.repr (zOfInt 8)), .Full) := by
  have hv : Exec.lvalOfVar sge (sEnv bs) id.«stack» (tarray entry 40) =
      some (bs, Ptrofs.zero, .Full) := by
    simp only [Exec.lvalOfVar, sEnv, temps_gss]
    rfl
  constructor
  · simp only [stk, Exec.evalLvalue, Exec.evalExpr, hv, htop]
    simp only [typeof, cop, sizeof_entry, Exec.derefLoc, Cfrontend.Ctypes.access_mode, lval_addr]
  · simp only [stk, Exec.evalLvalue, Exec.evalExpr, hv, htop]
    simp only [typeof, cop, sizeof_entry, Exec.derefLoc, Cfrontend.Ctypes.access_mode, lval_len]

section
omit binary64_certificate binary32_certificate

/-- Writing entry `l.length` and appending it. -/
theorem StackAt.push {m m1 m2 : mem} {bs : block} {l : List (Nat × Nat)} (hS : StackAt m C bs l)
    (hl : l.length < 40) (p sz : Nat)
    (h1 : Mem.store .Mint64 m bs (zOfInt (16 * l.length)) (.Vptr C.bx (pt C.base p)) = some m1)
    (h2 : Mem.store .Mint32 m1 bs (zOfInt (16 * l.length + 8)) (.Vint (ir sz)) = some m2) :
    StackAt m2 C bs (l ++ [(p, sz)]) := by
  have h8 : intOfZ (Common.Memdata.size_chunk .Mint64) = 8 := rfl
  have h4 : intOfZ (Common.Memdata.size_chunk .Mint32) = 4 := rfl
  have far : ∀ (c : Common.AST.memory_chunk) (o o' : Int) (w : Int),
      intOfZ (Common.Memdata.size_chunk c) = w → o + w ≤ o' →
      ZArith.BinInt.Z.le (ZArith.BinInt.Z.add (zOfInt o) (Common.Memdata.size_chunk c)) (zOfInt o') := by
    intro c o o' w hw hle
    change intOfZ _ ≤ intOfZ _
    simp only [intOfZ_add, intOfZ_zOfInt, hw]; exact hle
  refine ⟨by simp; omega, fun i hi => ?_, fun i hi => ?_, fun o ho => ?_, fun i hi => ?_,
    fun i hi => ?_⟩
  · exact Mem.store_valid_access_1 _ _ _ _ _ _ h2 _ _ _ _
      (Mem.store_valid_access_1 _ _ _ _ _ _ h1 _ _ _ _ (hS.wr64 i hi))
  · exact Mem.store_valid_access_1 _ _ _ _ _ _ h2 _ _ _ _
      (Mem.store_valid_access_1 _ _ _ _ _ _ h1 _ _ _ _ (hS.wr32 i hi))
  · exact Mem.perm_store_1 _ _ _ _ _ _ h2 _ _ _ _ (Mem.perm_store_1 _ _ _ _ _ _ h1 _ _ _ _ (hS.free o ho))
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases hik : i = l.length
    · subst hik
      rw [Mem.load_store_other _ _ _ _ _ _ h2 _ _ _ (.inr (.inl (far _ _ _ 8 h8 (by omega)))),
        Mem.load_store_same _ _ _ _ _ _ h1]
      simp; rfl
    · have hil : i < l.length := by omega
      rw [Mem.load_store_other _ _ _ _ _ _ h2 _ _ _ (.inr (.inl (far _ _ _ 8 h8 (by omega)))),
        Mem.load_store_other _ _ _ _ _ _ h1 _ _ _ (.inr (.inl (far _ _ _ 8 h8 (by omega)))),
        hS.addr i hil]
      simp [List.getElem?_append_left hil]
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases hik : i = l.length
    · subst hik
      rw [Mem.load_store_same _ _ _ _ _ _ h2]
      simp; rfl
    · have hil : i < l.length := by omega
      rw [Mem.load_store_other _ _ _ _ _ _ h2 _ _ _ (.inr (.inl (far _ _ _ 4 h4 (by omega)))),
        Mem.load_store_other _ _ _ _ _ _ h1 _ _ _ (.inr (.inl (far _ _ _ 4 h4 (by omega)))),
        hS.size i hil]
      simp [List.getElem?_append_left hil]

/-- The stack without its top entry. -/
theorem StackAt.pop {m : mem} {bs : block} {l : List (Nat × Nat)} {top : Nat × Nat}
    (hS : StackAt m C bs (l ++ [top])) : StackAt m C bs l :=
  ⟨by have := hS.len; simp at this; omega, hS.wr64, hS.wr32, hS.free,
    fun i hi => by
      have := hS.addr i (by simp; omega); simpa [List.getElem?_append_left hi] using this,
    fun i hi => by
      have := hS.size i (by simp; omega); simpa [List.getElem?_append_left hi] using this⟩

end

theorem wp_push {f : function} {Q : Post} {bs : block} {le : temp_env} {m : mem}
    {l : List (Nat × Nat)} (hS : StackAt m C bs l) (hl : l.length < 40)
    (htop : PTree.get id.«top» le = some (.Vint (ir l.length))) (pe ze : expr) (p sz : Nat)
    (hp : ∀ m', Exec.evalExpr sge (sEnv bs) le m' pe = some (.Vptr C.bx (pt C.base p)))
    (hpt : typeof pe = tptr tint)
    (hz : ∀ m', Exec.evalExpr sge (sEnv bs) le m' ze = some (.Vint (ir sz))) (hzt : typeof ze = tint)
    (hQ : ∀ m', StackAt m' C bs (l ++ [(p, sz)]) → Unch m m' (· = bs) → Alloc.KeepA m m' →
      Q.normal E0 (sEnv bs) (PTree.set id.«top» (.Vint (ir (l.length + 1))) le) m') :
    Wp xi sge f (push pe ze) Q (sEnv bs) le m := by
  have hk := lval_stk (m := m) (bs := bs) hl htop
  obtain ⟨m1, hm1⟩ := Mem.valid_access_store m .Mint64 bs _ (.Vptr C.bx (pt C.base p)) (hS.wr64 l.length hl)
  obtain ⟨m2, hm2⟩ := Mem.valid_access_store m1 .Mint32 bs _ (.Vint (ir sz))
    (Mem.store_valid_access_1 _ _ _ _ _ _ hm1 _ _ _ _ (hS.wr32 l.length hl))
  simp only [push, sk]
  wp_step; wp_step; wp_step
  apply wp_assign_eval
  rw [hk.1, hp m]
  simp only [hpt]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint64 m bs (Ptrofs.unsigned _) _ with
    | some m' => _ | none => False
  rw [entry_ofs _ hl 0 (by decide) (by decide), show 16 * (l.length : Int) + 0 =
    16 * (l.length : Int) by omega, hm1]
  simp only [E0_append]
  wp_step; wp_step; wp_step
  apply wp_assign_eval
  rw [(lval_stk (m := m1) (bs := bs) hl htop).2, hz m1]
  simp only [hzt]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint32 m1 bs (Ptrofs.unsigned _) _ with
    | some m' => _ | none => False
  rw [entry_ofs _ hl 8 (by decide) (by decide), hm2]
  simp only [E0_append]
  wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, htop, typeof, cop, ir_add]
  have hu : Unch m m2 (· = bs) := (Unch.store hm1 (S := (· = bs)) rfl).trans (Unch.store hm2 rfl)
  have hka : Alloc.KeepA m m2 := (Alloc.KeepA.store hm1 (by simp [intOfZ_zOfInt]; omega)).trans
    (Alloc.KeepA.store hm2 (by simp [intOfZ_zOfInt]; omega))
  have := hQ m2 (hS.push hl p sz hm1 hm2) hu hka
  simpa using this

/-- `x = stack[top].addr` and `x = stack[top].len` for the entry `top` of the stack. -/
theorem eval_pop {bs : block} {le : temp_env} {m : mem} {l : List (Nat × Nat)}
    (hS : StackAt m C bs l) {k : Nat} (hk : k < l.length)
    (htop : PTree.get id.«top» le = some (.Vint (ir k))) :
    Exec.evalExpr sge (sEnv bs) le m (stk id.«addr» (tptr tint)) =
      some (.Vptr C.bx (pt C.base l[k]!.1)) ∧
    Exec.evalExpr sge (sEnv bs) le m (stk id.«len» tint) = some (.Vint (ir l[k]!.2)) := by
  have hk40 : k < 40 := by have := hS.len; omega
  have hl := lval_stk (m := m) (bs := bs) hk40 htop
  have ef : ∀ (f : ident) (ty : type), Exec.evalExpr sge (sEnv bs) le m (stk f ty) =
      (Exec.evalLvalue sge (sEnv bs) le m (stk f ty)).bind
        (fun r => Exec.derefLoc ty m r.1 r.2.1 r.2.2) := by
    intro f ty
    simp only [stk, Exec.evalExpr, Exec.evalLvalue]
    split
    · split <;> simp_all [Option.bind]
    · simp_all [Option.bind]
  constructor
  · rw [ef, hl.1]
    simp only [Option.bind, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
    show Mem.load .Mint64 m bs (Ptrofs.unsigned _) = _
    rw [entry_ofs _ hk40 0 (by decide) (by decide), show 16 * (k : Int) + 0 = 16 * (k : Int) by
      omega]
    exact hS.addr k hk
  · rw [ef, hl.2]
    simp only [Option.bind, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
    show Mem.load .Mint32 m bs (Ptrofs.unsigned _) = _
    rw [entry_ofs _ hk40 8 (by decide) (by decide)]
    exact hS.size k hk

end NautyVerified.Proofs.Sparse.Sort.Ints

import NautyVerified.Proofs.Bestcell.Syntax
import NautyVerified.Proofs.Graph.Rows
import NautyVerified.Proofs.Alloc.Dyn
import NautyVerified.Spec.Bestcell

/-!
# What `bestcell`'s loops read

`Frame`: after the three `DYNALLOC1`s, the arguments in temporaries, the
graph, `lab`, `ptn` and the `bit` table in memory, and the static pointers
`workperm`, `workset` and `bucket` holding blocks `bP`, `bS`, `bB`, distinct
from each other and from everything read. `Mod m m'`: only those three blocks
changed, each keeping its `malloc` header.
-/

namespace NautyVerified.Proofs.Bestcell

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Alloc (Keep gat)
open NautyVerified.Proofs.Updatecan (tv labAt)
open Hex.GraphIso.Nauty (VSet)

abbrev WP := Block.naugraphWorkperm
abbrev WPS := Block.naugraphWorkpermSz
abbrev WS := Block.naugraphWorkset
abbrev WSS := Block.naugraphWorksetSz
abbrev BK := Block.naugraphBucket
abbrev BKS := Block.naugraphBucketSz
abbrev BIT := Block.naugraphBit

structure Frame {n : Nat} (m : mem) (le : temp_env) (bg : block) (gofs : ptrofs)
    (gw : Nat → Lib.Integers.int64) (grows : Array (VSet n)) (bl : block) (lofs : ptrofs)
    (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat) (level M : Nat)
    (bP bS bB : block) : Prop where
  hg : PTree.get id.g le = some (.Vptr bg gofs)
  hlab : PTree.get id.lab le = some (.Vptr bl lofs)
  hptn : PTree.get id.ptn le = some (.Vptr bp pofs)
  hlev : PTree.get id.level le = some (.Vint (ir level))
  hm : PTree.get id.m le = some (.Vint (ir M))
  hn : PTree.get id.n le = some (.Vint (ir n))
  graph : GraphAt m bg gofs gw grows M
  larr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n
  lsmall : ∀ j < n, lab[j]! < n
  parr : ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n
  psize : ptn.size = n
  psmall : ∀ x < n, ptn[x]! < 2147483648
  plast : ptn[n - 1]! ≤ level
  levlt : level < 2147483648
  wpP : Mem.load .Mint64 m WP (zOfInt 0) = some (.Vptr bP Ptrofs.zero)
  wsP : Mem.load .Mint64 m WS (zOfInt 0) = some (.Vptr bS Ptrofs.zero)
  bkP : Mem.load .Mint64 m BK (zOfInt 0) = some (.Vptr bB Ptrofs.zero)
  bit : BitTable m BIT
  dPS : bP ≠ bS
  dPB : bP ≠ bB
  dSB : bS ≠ bB
  owned : ∀ z, z = bP ∨ z = bS ∨ z = bB → z ≠ bg ∧ z ≠ bl ∧ z ≠ bp ∧ z ≠ WP ∧ z ≠ WS ∧ z ≠ BK ∧
    z ≠ BIT
  n0 : 0 < n
  nlt : n < 1073741824
  M1 : 0 < M
  Mlt : M < 33554432
  nM : n ≤ 64 * M

section
variable {n : Nat} {m : mem} {le : temp_env} {bg : block} {gofs : ptrofs}
  {gw : Nat → Lib.Integers.int64} {grows : Array (VSet n)} {bl : block} {lofs : ptrofs}
  {lab : Array Nat} {bp : block} {pofs : ptrofs} {ptn : Array Nat} {level M : Nat}
  {bP bS bB : block}

/-- The temporaries `bestcell` reads but never sets. -/
abbrev Args (x : Common.AST.ident) : Prop :=
  x = id.g ∨ x = id.lab ∨ x = id.ptn ∨ x = id.level ∨ x = id.m ∨ x = id.n

theorem Frame.temps (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {le' : temp_env} (hle : ∀ x, Args x → PTree.get x le' = PTree.get x le) :
    Frame m le' bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB :=
  { h with
    hg := by rw [hle _ (.inl rfl)]; exact h.hg
    hlab := by rw [hle _ (.inr (.inl rfl))]; exact h.hlab
    hptn := by rw [hle _ (.inr (.inr (.inl rfl)))]; exact h.hptn
    hlev := by rw [hle _ (.inr (.inr (.inr (.inl rfl))))]; exact h.hlev
    hm := by rw [hle _ (.inr (.inr (.inr (.inr (.inl rfl)))))]; exact h.hm
    hn := by rw [hle _ (.inr (.inr (.inr (.inr (.inr rfl)))))]; exact h.hn }

/-- Only the three arrays changed, each keeping its header. -/
def Mod (m m' : mem) (bP bS bB : block) : Prop :=
  Unch m m' (fun z => z = bP ∨ z = bS ∨ z = bB) ∧ Keep m m' bP ∧ Keep m m' bS ∧ Keep m m' bB

theorem Mod.refl (m : mem) (bP bS bB : block) : Mod m m bP bS bB :=
  ⟨Unch.refl _ _, Keep.refl _ _, Keep.refl _ _, Keep.refl _ _⟩

theorem Mod.trans {m₁ m₂ m₃ : mem} (h₁ : Mod m₁ m₂ bP bS bB) (h₂ : Mod m₂ m₃ bP bS bB) :
    Mod m₁ m₃ bP bS bB :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩

theorem Frame.unch (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {m' : mem} (hu : Unch m m' (fun z => z = bP ∨ z = bS ∨ z = bB)) :
    Frame m' le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB := by
  have own := h.owned
  have nb : ∀ z, (∀ y, y = bP ∨ y = bS ∨ y = bB → y ≠ z) → ¬ (z = bP ∨ z = bS ∨ z = bB) :=
    fun z hz hc => hz z hc rfl
  have nG := nb bg fun y hy => (own y hy).1
  have nL := nb bl fun y hy => (own y hy).2.1
  have nP := nb bp fun y hy => (own y hy).2.2.1
  have nWP := nb WP fun y hy => (own y hy).2.2.2.1
  have nWS := nb WS fun y hy => (own y hy).2.2.2.2.1
  have nBK := nb BK fun y hy => (own y hy).2.2.2.2.2.1
  have nBit := nb BIT fun y hy => (own y hy).2.2.2.2.2.2
  exact { h with
    graph := ⟨h.graph.arr.unch hu nG, h.graph.rep⟩
    larr := h.larr.unch hu nL
    parr := h.parr.unch hu nP
    wpP := by rw [hu.load _ _ _ nWP]; exact h.wpP
    wsP := by rw [hu.load _ _ _ nWS]; exact h.wsP
    bkP := by rw [hu.load _ _ _ nBK]; exact h.bkP
    bit := h.bit.unch hu nBit }

theorem Frame.modP (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {m' : mem} (hu : Unch m m' (· = bP)) (hk : Keep m m' bP) : Mod m m' bP bS bB :=
  ⟨hu.mono fun _ hz => .inl hz, hk, Keep.unch hu h.dPS.symm, Keep.unch hu h.dPB.symm⟩

theorem Frame.modS (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {m' : mem} (hu : Unch m m' (· = bS)) (hk : Keep m m' bS) : Mod m m' bP bS bB :=
  ⟨hu.mono fun _ hz => .inr (.inl hz), Keep.unch hu h.dPS, hk, Keep.unch hu h.dSB.symm⟩

theorem Frame.modB (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {m' : mem} (hu : Unch m m' (· = bB)) (hk : Keep m m' bB) : Mod m m' bP bS bB :=
  ⟨hu.mono fun _ hz => .inr (.inr hz), Keep.unch hu h.dPB, Keep.unch hu h.dSB, hk⟩

/-! ## Reading -/

theorem eval_lab (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge empty_env le m (labAt a) = some (.Vint (ir (lab[c]! : Int))) :=
  eval_at h.larr (by have := h.nlt; omega) id.lab h.hlab a c hc ha hty

theorem eval_ptn (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge empty_env le m (ptnAt a) = some (.Vint (ir (ptn[c]! : Int))) :=
  eval_at h.parr (by have := h.nlt; omega) id.ptn h.hptn a c hc ha hty

theorem eval_ptnGt (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    (c : Nat) (hc : c < n) (hi : PTree.get id.i le = some (.Vint (ir c))) :
    Exec.evalExpr ge empty_env le m ptnGt = some (Val.of_bool (decide (level < ptn[c]!))) := by
  have hpe := eval_ptn h (tv id.i) c hc hi rfl
  have := h.psmall c hc
  have := h.levlt
  rw [Exec.evalExpr, hpe, show Exec.evalExpr ge empty_env le m (tv id.level) = _ from h.hlev]
  simp only [typeof, cop]
  rw [ir_lt (a := (level : Int)) (b := (ptn[c]! : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  congr 2
  apply decide_eq_decide.2; omega

theorem eval_wp (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {wv : Nat → val} (hw : ArrayAt m .Mint32 bP 0 wv n) (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge empty_env le m (gat id.wp a) = some (wv c) :=
  Alloc.eval_gat rfl find_naugraphWorkperm h.wpP hw (by have := h.nlt; omega) a c hc ha hty

theorem eval_bk (h : Frame m le bg gofs gw grows bl lofs lab bp pofs ptn level M bP bS bB)
    {bv : Nat → val} (hb : ArrayAt m .Mint32 bB 0 bv (n + 2)) (a : expr) (c : Nat) (hc : c < n + 2)
    (ha : Exec.evalExpr ge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint) :
    Exec.evalExpr ge empty_env le m (gat id.bk a) = some (bv c) :=
  Alloc.eval_gat rfl find_naugraphBucket h.bkP hb (by have := h.nlt; omega) a c hc ha hty

end

end NautyVerified.Proofs.Bestcell

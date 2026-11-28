import NautyVerified.Proofs.Sparse.Refine.Nontrivial.ResetK

/-!
# `RESETMARKS2` keeping every block's permissions

`wp_resetmarks2K` is `Refine/Marks2.lean`'s `wp_resetmarks2` with
`KeepA` (every block keeps its permissions and header) added to the
postcondition, which `refine_sg`'s `Frame` needs. `Mem.setK2`: memory after
it, with the new stamp and marks.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source

variable {xi : ExternalCalls}

open NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt)

attribute [local instance] NautyVerified.Program.NautyEnv.sparse
/-- `RESETMARKS2`'s change: the stamp and the second mark array. -/
theorem Mem.setK2 {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (fun z => z = Block.vmark2Val ∨ (0 < L.mc2 ∧ z = L.mb2)))
    (st : Nat) (mk : Nat → Int) (hM : Marks2.MarksAt m' L.mc2 L.mb2 st mk) :
    Mem m' L G t { S with st2 := st, mk2 := mk } where
  graph := h.graph.unch hu (fun hh => hh.elim (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun hh => hh.elim (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun hh => hh.elim (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun hh => hh.elim (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2))
  lab := h.lab.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 0 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 0 10 (by decide) (by simp [Loc.wblocks])) hh2.2))
  ptn := h.ptn.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 1 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 1 10 (by decide) (by simp [Loc.wblocks])) hh2.2))
  nc := h.nc.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 2 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 2 10 (by decide) (by simp [Loc.wblocks])) hh2.2))
  act := h.act.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 3 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 3 10 (by decide) (by simp [Loc.wblocks])) hh2.2))
  w1 := h.w1.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 5 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 5 10 (by decide) (by simp [Loc.wblocks])) hh2.2))
  w2 := h.w2.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 6 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 6 10 (by decide) (by simp [Loc.wblocks])) hh2.2))
  w3 := h.w3.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 7 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 7 10 (by decide) (by simp [Loc.wblocks])) hh2.2))
  w4 := h.w4.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 8 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 8 10 (by decide) (by simp [Loc.wblocks])) hh2.2))
  actRep := h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 4 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 4 10 (by decide) (by simp [Loc.wblocks])) hh2.2))⟩
  d1 := h.d1.keep hu (fun hh => hh.elim (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun hh => hh.elim (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun _ => Keep.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 5 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 5 10 (by decide) (by simp [Loc.wblocks])) hh2.2)))
  d2 := h.d2.keep hu (fun hh => hh.elim (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun hh => hh.elim (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun _ => Keep.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 6 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 6 10 (by decide) (by simp [Loc.wblocks])) hh2.2)))
  d3 := h.d3.keep hu (fun hh => hh.elim (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun hh => hh.elim (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun _ => Keep.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 7 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 7 10 (by decide) (by simp [Loc.wblocks])) hh2.2)))
  d4 := h.d4.keep hu (fun hh => hh.elim (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun hh => hh.elim (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun _ => Keep.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 8 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 8 10 (by decide) (by simp [Loc.wblocks])) hh2.2)))
  k1 := h.k1.unch hu (fun hh => hh.elim (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun hh => hh.elim (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2)) (fun hh => hh.elim (pw_ne hok.wdistinct 11 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (Ne.symm (pw_ne hok.wdistinct 10 11 (by decide) (by simp [Loc.wblocks]))) hh2.2)) (fun _ => (fun hh => hh.elim (pw_ne hok.wdistinct 9 12 (by decide) (by simp [Loc.wblocks])) (fun hh2 => (pw_ne hok.wdistinct 9 10 (by decide) (by simp [Loc.wblocks])) hh2.2)))
  k2 := hM
  bit := fun q hq => by rw [hu.load _ _ _ (fun hh => hh.elim (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun hh => hh.elim (fun e => hok.rw (NautyVerified.Program.NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hh2 => (fun e => hok.rw (NautyVerified.Program.NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) hh2.2))]; exact h.left q hq

/-- `RESETMARKS2`, with every block keeping its permissions and header. -/
theorem wp_resetmarks2K {f : function} {Q : Post} {le : temp_env} {m : mem} {cap : Nat} {b : block}
    {st : Nat} {marks : Nat → Int} {t ij : ident}
    (hM : Marks2.MarksAt m cap b st marks)
    (hQ : ∀ le' m' val' marks', Marks2.MarksAt m' cap b val' marks' → (∀ i < cap, marks' i < val') →
      Unch m m' (fun z => z = Block.vmark2Val ∨ (0 < cap ∧ z = b)) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Alloc.KeepA m m' →
      (∀ x, x ≠ t → x ≠ ij → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge f (Marks2.resetmarks2 t ij) Q empty_env le m := by
  have hV1 := hM.val1
  have hV2 := hM.val32
  have hD := hM.dyn
  have hne1 : Block.vmark2Val ≠ Block.vmark2 := by decide
  have hne2 : Block.vmark2Val ≠ Block.vmark2Sz := by decide
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Marks2.eval_val hM.valLd]
  let le1 := PTree.set t (.Vint (ir st)) le
  have ht1 : PTree.get t le1 = some (.Vint (ir st)) := temps_gss _ _ _
  refine Marks2.wp_storeVal (x := st + 1) (by omega) ?_ rfl hM.valW ?_
  · simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]; push_cast; rfl
  intro m1 hst1
  have hu1 : Unch m m1 (· = Block.vmark2Val) := Unch.store hst1 rfl
  have hval1 : Mem.load .Mint16signed m1 Block.vmark2Val (zOfInt 0) = some (.Vint (ir (st + 1))) := by
    have := Mem.load_store_same _ _ _ _ _ _ hst1
    rw [this]
    exact congrArg (fun x => some (val.Vint x)) (Search.sign_ext16_ir (a := ((st + 1 : Nat) : Int))
      (by omega) (by omega))
  have hW1 : Mem.valid_access m1 .Mint16signed Block.vmark2Val (zOfInt 0) .Writable :=
    Mem.store_valid_access_1 _ _ _ _ _ _ hst1 _ _ _ _ hM.valW
  have hg1 : ∀ z, Mem.valid_block m z → Mem.valid_block m1 z :=
    fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hst1 _ h
  have hnb : 0 < cap → ¬ b = Block.vmark2Val := fun hc h => hM.bval hc h
  have hD1 : Alloc.DynAt m1 Block.vmark2 Block.vmark2Sz 2 cap b :=
    { hD with
      capLd := by rw [hu1.load _ _ _ hne2.symm]; exact hD.capLd
      bsW := hu1.access _ _ _ _ hne2.symm hD.bsW
      bpW := hu1.access _ _ _ _ hne1.symm hD.bpW
      ptr := fun hc => by rw [hu1.load _ _ _ hne1.symm]; exact hD.ptr hc
      mal := fun hc => (hD.mal hc).keep (Alloc.Keep.unch hu1 (hnb hc))
      null := fun hc => by rw [hu1.load _ _ _ hne1.symm]; exact hD.null hc }
  have harr1 : ArrayAt m1 .Mint16signed b 0 (markVals marks) cap := by
    by_cases hc : 0 < cap
    · exact hM.arr.unch hu1 (hnb hc)
    · have : cap = 0 := by omega
      subst this; exact ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
        fun _ h => absurd h (by omega)⟩
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, typeof, cop]
  rw [ir_lt (a := (st : Int)) (b := 32000) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
  have hle1 : ∀ x, x ≠ t → PTree.get x le1 = PTree.get x le := fun x hx => temps_gso _ _ hx
  by_cases hv : st < 32000
  · rw [show decide ((st : Int) < 32000) = true from decide_eq_true (by omega)]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [E0_append]
    refine hQ le1 m1 (st + 1) marks ⟨hD1, by rw [hval1]; push_cast; rfl, hW1, by omega, by omega,
      harr1, fun i hi => ⟨(hM.bounds i hi).1, by have := (hM.bounds i hi).2; omega⟩, hM.bval⟩
      (fun i hi => by have := (hM.bounds i hi).2; omega) (hu1.mono fun z hz => .inl hz) hg1
      (Alloc.KeepA.store hst1 (by decide)) (fun x hx _ => hle1 x hx)
  · have hst : st = 32000 := by omega
    subst hst
    rw [show decide (((32000 : Nat) : Int) < 32000) = false by decide]
    simp only [Bool.not_false, ite_true]
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
    let le2 := PTree.set ij (.Vlong (lr 0)) le1
    refine Marks2.wp_zeroLoop (le := le2) hD1.capLd hD1.capLt hD1.ptr harr1 hD1.bne (temps_gss _ _ _) ?_
    intro le3 m3 harr3 hu3 hkp3 hg3 ho3
    wp_step; wp_step
    have hW3 : Mem.valid_access m3 .Mint16signed Block.vmark2Val (zOfInt 0) .Writable :=
      hu3.access _ _ _ _ (fun ⟨hc, h⟩ => hnb hc h.symm) hW1
    refine Marks2.wp_storeVal (x := 1) (by decide) (by simp only [Exec.evalExpr]; rfl) rfl hW3 ?_
    intro m4 hst4
    have hu4 : Unch m3 m4 (· = Block.vmark2Val) := Unch.store hst4 rfl
    have hnS : ∀ z, (z = Block.vmark2 ∨ z = Block.vmark2Sz) →
        ¬ ((z = Block.vmark2Val) ∨ (0 < cap ∧ z = b)) := by
      rintro z (rfl | rfl) (h | ⟨hc, h⟩)
      · exact hne1 h.symm
      · exact (hD.bne hc).2 h.symm
      · exact hne2 h.symm
      · exact (hD.bne hc).1 h.symm
    have hu : Unch m m4 (fun z => z = Block.vmark2Val ∨ (0 < cap ∧ z = b)) :=
      ((hu1.mono fun z hz => .inl hz).trans (hu3.mono fun z hz => .inr hz)).trans
        (hu4.mono fun z hz => .inl hz)
    have hval4 : Mem.load .Mint16signed m4 Block.vmark2Val (zOfInt 0) = some (.Vint (ir 1)) := by
      rw [Mem.load_store_same _ _ _ _ _ _ hst4]; rfl
    have harr4 : ArrayAt m4 .Mint16signed b 0 (markVals fun _ => 0) cap := by
      by_cases hc : 0 < cap
      · exact harr3.unch hu4 (hnb hc)
      · have : cap = 0 := by omega
        subst this; exact ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
          fun _ h => absurd h (by omega)⟩
    have hD4 : Alloc.DynAt m4 Block.vmark2 Block.vmark2Sz 2 cap b :=
      { hD with
        capLd := by rw [hu.load _ _ _ (hnS _ (.inr rfl))]; exact hD.capLd
        bsW := hu.access _ _ _ _ (hnS _ (.inr rfl)) hD.bsW
        bpW := hu.access _ _ _ _ (hnS _ (.inl rfl)) hD.bpW
        ptr := fun hc => by rw [hu.load _ _ _ (hnS _ (.inl rfl))]; exact hD.ptr hc
        mal := fun hc => ((hD1.mal hc).keep hkp3).keep (Alloc.Keep.unch hu4 (hnb hc))
        null := fun hc => by rw [hu.load _ _ _ (hnS _ (.inl rfl))]; exact hD.null hc }
    refine hQ le3 m4 1 (fun _ => 0) ⟨hD4, hval4, Mem.store_valid_access_1 _ _ _ _ _ _ hst4 _ _ _ _ hW3,
      by decide, by decide, harr4, fun _ _ => ⟨Int.le_refl _, by decide⟩, hM.bval⟩
      (fun _ _ => by decide) hu (fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hst4 _ (hg3 _ (hg1 _ h)))
      (((Alloc.KeepA.store hst1 (by decide)).trans
        (Alloc.KeepA.of_keep (hu3.mono fun z hz => hz.2) hkp3)).trans (Alloc.KeepA.store hst4 (by decide)))
      (fun x hx hx' => by rw [ho3 x hx', temps_gso _ _ hx', hle1 x hx])

end NautyVerified.Proofs.Sparse.Refine.Trivial

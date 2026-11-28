import NautyVerified.Proofs.Sparse.Updatecan.Row
import NautyVerified.Proofs.Alloc.Dyn3
import NautyVerified.Proofs.Sparse.Prep

/-!
# `updatecan_sg` meets its specification

`updatecanSpec`: called on a sparse graph `G` (`SparseGraphAt`, so `wt` is
`NULL`), the canonical store holding the first `samerows` rows of `R`
(`CanonAt … R samerows …`) whose offsets have `n + 1` entries and whose
neighbour array has room for the rows from `samerows` on, and a permutation
`lab`, nausparse.c's `updatecan_sg` leaves the store holding all `n` rows of
HexGraphIso's `Sparse.updatecan (ofGraph G) R lab samerows`, with `nv = n`
and `nde` the number of directed edges of `G`. It uses `work1` as `INVLAB`
(`Sparse.inverse n lab`); nothing else changes.
-/

namespace NautyVerified.Proofs.Sparse.Updatecan

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse NautyVerified.Program
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat cast_l_i)
open Hex.GraphIso.Nauty.Sparse (Graph Rows inverse inverse_lt)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

/-- The byte offset `k` of a struct at `sofs`, when it does not wrap. -/
theorem fofs_int {sofs : ptrofs} {k : Int} (h : intOfZ (Ptrofs.unsigned sofs) + k < 2 ^ 64)
    (hk : 0 ≤ k) : intOfZ (fofs sofs k) = intOfZ (Ptrofs.unsigned sofs) + k := by
  simp only [fofs, intOfZ_Ptrofs_unsigned, bvp_add, bvp_repr, intOfZ_zOfInt, BitVec.toNat_add,
    BitVec.toNat_ofInt] at h ⊢
  have h0 : (k % ((2 ^ 64 : Nat) : Int)).toNat = k.toNat := by
    rw [Int.emod_eq_of_lt hk (by omega)]
  rw [h0, Nat.mod_eq_of_lt (by omega)]
  push_cast; omega

/-- A store at struct byte `k2` leaves a load at struct byte `k1` of a disjoint field. -/
theorem load_field_other {m m' : mem} {b : block} {sofs : ptrofs} {c1 c2 : memory_chunk}
    {k1 k2 : Int} {v w : val} (hs : intOfZ (Ptrofs.unsigned sofs) + 48 < 2 ^ 64)
    (hk1 : 0 ≤ k1) (hk1' : k1 ≤ 48) (hk2 : 0 ≤ k2) (hk2' : k2 ≤ 48)
    (hd : k1 + csize c1 ≤ k2 ∨ k2 + csize c2 ≤ k1)
    (hst : Mem.store c2 m b (fofs sofs k2) w = some m') (hl : Mem.load c1 m b (fofs sofs k1) = some v) :
    Mem.load c1 m' b (fofs sofs k1) = some v := by
  have e1 := fofs_int (sofs := sofs) (k := k1) (by omega) hk1
  have e2 := fofs_int (sofs := sofs) (k := k2) (by omega) hk2
  have s1 : intOfZ (Common.Memdata.size_chunk c1) = csize c1 := rfl
  have s2 : intOfZ (Common.Memdata.size_chunk c2) = csize c2 := rfl
  rw [Mem.load_store_other _ _ _ _ _ _ hst _ _ _ (.inr (by
    rcases hd with hd | hd
    · left; show intOfZ _ ≤ intOfZ _; rw [intOfZ_add, e1, e2, s1]; omega
    · right; show intOfZ _ ≤ intOfZ _; rw [intOfZ_add, e1, e2, s2]; omega))]
  exact hl

/-- `canong->f = x;` -/
theorem wp_setField {Q : Post} {le : temp_env} {m : mem} {f : ident} {ty : Cfrontend.Ctypes.type}
    {chunk : memory_chunk} {x : expr} {bc : block} {cofs : ptrofs} {k : Int} {v w : val}
    (hp : PTree.get id.canong le = some (.Vptr bc cofs))
    (hlv : Exec.lvalOfField sge sgTy f (.Vptr bc cofs) =
      some (bc, Ptrofs.add cofs (Ptrofs.repr (zOfInt k)), .Full))
    (hmode : Cfrontend.Ctypes.access_mode ty = .By_value chunk)
    (hx : Exec.evalExpr sge empty_env le m x = some v) {tx : Cfrontend.Ctypes.type}
    (hxt : typeof x = tx) (hcast : Cfrontend.Cop.sem_cast v tx ty m = some w)
    (hW : Mem.valid_access m chunk bc (fofs cofs k) .Writable)
    (hQ : ∀ m', Mem.store chunk m bc (fofs cofs k) w = some m' → Q.normal E0 empty_env le m') :
    Wp xi sge F (setField f ty x) Q empty_env le m := by
  obtain ⟨m', hst⟩ := Mem.valid_access_store _ _ _ _ w hW
  wp_step; wp_step
  apply wp_assign_eval
  rw [hx, hxt]
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, typeof, cop, Exec.derefLoc,
    show Cfrontend.Ctypes.access_mode sgTy = .By_copy from rfl, hlv, hcast, Exec.assignLoc, hmode,
    Mem.storev]
  rw [show Ptrofs.unsigned (Ptrofs.add cofs (Ptrofs.repr (zOfInt k))) = fofs cofs k from rfl, hst]
  exact hQ m' hst

/-- `SWG_VDE(p, v, d, e, w)`. -/
theorem wp_vdew {Q : Post} {le : temp_env} {m : mem} {p v d e w : ident} {bsg : block} {sofs : ptrofs}
    {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs}
    (hp : PTree.get p le = some (.Vptr bsg sofs)) (hpv : p ≠ v) (hpd : p ≠ d) (hpe : p ≠ e)
    (hv : Mem.load .Mint64 m bsg (fofs sofs 8) = some (.Vptr bv vo))
    (hd : Mem.load .Mint64 m bsg (fofs sofs 24) = some (.Vptr bd dofs))
    (he : Mem.load .Mint64 m bsg (fofs sofs 32) = some (.Vptr be eo))
    (hw : Mem.load .Mint64 m bsg (fofs sofs 40) = some Vnullptr)
    (hQ : Q.normal E0 empty_env (PTree.set w Vnullptr
      (PTree.set e (.Vptr be eo) (PTree.set d (.Vptr bd dofs) (PTree.set v (.Vptr bv vo) le)))) m) :
    Wp xi sge F (vdew p v d e w) Q empty_env le m := by
  let le1 := PTree.set w Vnullptr
    (PTree.set e (.Vptr be eo) (PTree.set d (.Vptr bd dofs) (PTree.set v (.Vptr bv vo) le)))
  refine wp_loop (I := fun _ t e' le' m' => t = E0 ∧ e' = empty_env ∧ le' = le ∧ m' = m)
    (J := fun _ t e' le' m' => t = E0 ∧ e' = empty_env ∧ le' = le1 ∧ m' = m) ?_ ?_ (n := 0)
    ⟨rfl, rfl, rfl, rfl⟩
  · rintro - t e' le' m' ⟨rfl, rfl, rfl, hm⟩
    subst m'
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_sgField hp (lval_v _ _) rfl hv]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_sgField (by rw [temps_gso _ _ hpv]; exact hp) (lval_d _ _) rfl hd]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_sgField (by rw [temps_gso _ _ hpd, temps_gso _ _ hpv]; exact hp) (lval_e _ _) rfl he]
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_sgField (by rw [temps_gso _ _ hpe, temps_gso _ _ hpd, temps_gso _ _ hpv]; exact hp)
      (lval_w _ _) rfl hw]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro - t e' le' m' ⟨rfl, rfl, rfl, hm⟩
    subst m'
    wp_step; wp_step
    apply wp_break
    simpa only [E0_append] using hQ

/-- The blocks `updatecan_sg` writes. -/
def Wr (bc cbv cbd cbe : block) (z : block) : Prop := z = bc ∨ z = cbv ∨ z = cbd ∨ z = cbe

/-- The blocks `updatecan_sg` only reads. -/
def Rd (bsg bv bd be bl : block) (z : block) : Prop := z = bsg ∨ z = bv ∨ z = bd ∨ z = be ∨ z = bl

/-- The specification of `updatecan_sg`. -/
def updatecanSpec {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (R : Rows n) (bc : block)
    (cofs : ptrofs) (cbv : block) (cvo : ptrofs) (cbd : block) (cdofs : ptrofs) (cbe : block)
    (ceo : ptrofs) (lab : Array Nat) (bl : block) (lofs : ptrofs) (sr M capW : Nat) (bW : block) :
    FunSpec where
  pre args m := args = [.Vptr bsg sofs, .Vptr bc cofs, .Vptr bl lofs, .Vint (ir sr), .Vint (ir M),
      .Vint (ir n)] ∧
    SparseGraphAt m bsg sofs G bv vo bd dofs be eo ∧ CanonAt m bc cofs R sr cbv cvo cbd cdofs cbe ceo ∧
    R.offsets.size = n + 1 ∧ start (Graph.ofGraph G) lab sr (base R sr) (n - sr) ≤ R.neighbors.size ∧
    intOfZ (Ptrofs.unsigned cofs) + 48 < 2 ^ 64 ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧ lab.size = n ∧
    (∀ j < n, lab[j]! < n) ∧ (∀ a b, a < n → b < n → lab[a]! = lab[b]! → a = b) ∧
    (∀ p < n, ∃ j < n, lab[j]! = p) ∧
    Alloc.DynAt m Block.work1 Block.work1Sz 4 capW bW ∧ 0 < n ∧ n < 2147483648 ∧
    (∀ z, Rd bsg bv bd be bl z ∨ Wr bc cbv cbd cbe z → Mem.valid_block m z ∧ z ≠ Block.work1 ∧
      z ≠ Block.work1Sz ∧ (0 < capW → z ≠ bW)) ∧
    (∀ z, Wr bc cbv cbd cbe z → ¬ Rd bsg bv bd be bl z) ∧
    bc ≠ cbv ∧ bc ≠ cbd ∧ bc ≠ cbe ∧ cbv ≠ cbd ∧ cbv ≠ cbe ∧ cbd ≠ cbe
  post _ m t _ m' := t = E0 ∧ ∃ capW' bW', Alloc.DynAt m' Block.work1 Block.work1Sz 4 capW' bW' ∧
    n ≤ capW' ∧ ((capW' = capW ∧ bW' = bW) ∨ ¬ Mem.valid_block m bW') ∧
    CanonAt m' bc cofs (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr) n
      cbv cvo cbd cdofs cbe ceo ∧
    Mem.load .Mint32 m' bc (fofs cofs 16) = some (.Vint (ir n)) ∧
    Mem.load .Mint64 m' bc (fofs cofs 0) = some (.Vlong (lr G.neighbors.size)) ∧
    Unch m m' (fun z => Wr bc cbv cbd cbe z ∨ z = Block.work1 ∨ z = Block.work1Sz ∨
      (0 < capW ∧ z = bW) ∨ (¬ Mem.valid_block m bW' ∧ z = bW')) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z)

def entryTemps (bsg : block) (sofs : ptrofs) (bc : block) (cofs : ptrofs) (bl : block) (lofs : ptrofs)
    (sr M n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.samerows (.Vint (ir sr)) (PTree.set id.lab (.Vptr bl lofs)
      (PTree.set id.canong (.Vptr bc cofs) (PTree.set id.g (.Vptr bsg sofs)
        (create_undef_temps F.fn_temps))))))

/-- Every position from `b0` below the end of the rows lies in one of them. -/
theorem locate {n : Nat} (g : Graph n) (lab : Array Nat) (s b0 : Nat) :
    ∀ p j, b0 ≤ j → j < start g lab s b0 p → ∃ q < p, start g lab s b0 q ≤ j ∧ j < start g lab s b0 (q + 1)
  | 0, j, h1, h2 => absurd h2 (by simp only [start]; omega)
  | p + 1, j, h1, h2 => by
    by_cases hj : j < start g lab s b0 p
    · obtain ⟨q, hq, h⟩ := locate g lab s b0 p j h1 hj
      exact ⟨q, by omega, h⟩
    · exact ⟨p, by omega, by omega, h2⟩

/-- The rows `updatecan_sg` leaves are `Sparse.updatecan`'s. -/
theorem canonRows_update {n : Nat} (G : Hex.SparseGraph n) (R : Rows n) (lab : Array Nat) (sr : Nat)
    {vv dv ev vv' dv' ev' : Nat → val} (hrows : CanonRows R sr vv dv ev) (hsz : R.offsets.size = n + 1)
    (hfit : start (Graph.ofGraph G) lab sr (base R sr) (n - sr) ≤ R.neighbors.size) (hn0 : 0 < n)
    (hlsz : lab.size = n)
    (P1 : ∀ i < sr, vv' i = vv i ∧ dv' i = dv i)
    (P2 : ∀ q < n - sr, vv' (sr + q) = .Vlong (lr (start (Graph.ofGraph G) lab sr (base R sr) q)) ∧
      dv' (sr + q) = .Vint (ir ((Graph.ofGraph G).degree lab[sr + q]!)))
    (P3 : ∀ e < base R sr, ev' e = ev e)
    (P4 : ∀ q < n - sr, ∀ j < (Graph.ofGraph G).degree lab[sr + q]!,
      ev' (start (Graph.ofGraph G) lab sr (base R sr) q + j) =
        nbv G lab (Graph.ofGraph G).offsets[lab[sr + q]!]! j) :
    CanonRows (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr) n vv' dv' ev' := by
  have hsr := hrows.bound
  have U := updatecan_rows (Graph.ofGraph G) R lab sr hsr hsz hfit
  have B := Hex.GraphIso.Nauty.Sparse.updatecan_before (Graph.ofGraph G) R lab sr hsr
  have S := Hex.GraphIso.Nauty.Sparse.updatecan_sizes (Graph.ofGraph G) R lab sr
  have hoff : ∀ q ≤ n - sr, (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr).offsets[sr + q]! = start (Graph.ofGraph G) lab sr (base R sr) q := U.1
  have hbsr : sr ≠ 0 → base R sr = R.offsets[sr]! := fun h => by simp [base, h]
  have hRsr : sr ≠ 0 → (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr).offsets[sr]! = R.offsets[sr]! := fun h => by
    have := hoff 0 (Nat.zero_le _); rw [Nat.add_zero] at this; rw [this, ← hbsr h]; rfl
  have hbase' : base (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr) n = start (Graph.ofGraph G) lab sr (base R sr) (n - sr) := by
    simp only [base, show n ≠ 0 by omega, ite_false]
    have := hoff (n - sr) (Nat.le_refl _); rwa [show sr + (n - sr) = n by omega] at this
  have hst_le := fun {a b : Nat} (h : a ≤ b) => start_mono (Graph.ofGraph G) lab sr (base R sr) h
  have hb_le : base R sr ≤ R.neighbors.size := hrows.base_le
  have hstq : ∀ q, start (Graph.ofGraph G) lab sr (base R sr) (q + 1) = start (Graph.ofGraph G) lab sr (base R sr) q + (Graph.ofGraph G).degree lab[sr + q]! := fun _ => rfl
  -- offsets of (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr) below and above samerows
  have hofs : ∀ i, i ≤ n → (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr).offsets[i]! = if i < sr then R.offsets[i]! else start (Graph.ofGraph G) lab sr (base R sr) (i - sr) := by
    intro i hi
    by_cases h : i < sr
    · rw [if_pos h]; exact B.1 i h
    · rw [if_neg h]; have := hoff (i - sr) (by omega); rwa [show sr + (i - sr) = i by omega] at this
  refine ⟨Nat.le_refl _, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, ?_, ?_,
    fun j hj => ?_⟩
  · -- mono
    rw [hofs i (by omega), hofs (i + 1) (by omega)]
    by_cases h1 : i + 1 < sr
    · rw [if_pos (by omega), if_pos h1]; exact hrows.mono i (by omega)
    · by_cases h2 : i < sr
      · rw [if_pos h2, if_neg h1, show i + 1 - sr = 0 by omega]
        have := hrows.mono i h2
        show _ ≤ base R sr
        rw [hbsr (by omega), show sr = i + 1 by omega]; exact this
      · rw [if_neg h2, if_neg h1]; exact hst_le (by omega)
  · -- v
    by_cases h : i < sr
    · rw [(P1 i h).1, hrows.v i h, B.1 i h]
    · have := (P2 (i - sr) (by omega)).1
      rw [show sr + (i - sr) = i by omega] at this
      rw [this, hofs i (by omega), if_neg h]
  · -- d
    have hdeg : (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr).degree i = (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr).offsets[i + 1]! - (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr).offsets[i]! := rfl
    by_cases h : i < sr
    · rw [(P1 i h).2, hrows.d i h, hdeg, hofs i (by omega), hofs (i + 1) (by omega), if_pos h]
      by_cases h1 : i + 1 < sr
      · rw [if_pos h1]; rfl
      · rw [if_neg h1, show i + 1 - sr = 0 by omega]
        have e : start (Graph.ofGraph G) lab sr (base R sr) 0 = R.offsets[i + 1]! := by
          show base R sr = _; rw [hbsr (by omega), show sr = i + 1 by omega]
        rw [e]; rfl
    · have := (P2 (i - sr) (by omega)).2
      rw [show sr + (i - sr) = i by omega] at this
      rw [this, hdeg, hofs i (by omega), hofs (i + 1) (by omega), if_neg h, if_neg (by omega),
        show i + 1 - sr = (i - sr) + 1 by omega, hstq, show sr + (i - sr) = i by omega,
        Nat.add_sub_cancel_left]
  · -- e
    rw [hbase'] at hj
    by_cases h : j < base R sr
    · rw [P3 j h, hrows.e j h, B.2 j (by simpa [base] using h)]
    · obtain ⟨q, hq, h1, h2⟩ := locate (Graph.ofGraph G) lab sr (base R sr) (n - sr) j (by omega) hj
      obtain ⟨d, rfl⟩ : ∃ d, j = start (Graph.ofGraph G) lab sr (base R sr) q + d := ⟨j - start (Graph.ofGraph G) lab sr (base R sr) q, by omega⟩
      rw [hstq] at h2
      rw [P4 q hq d (by omega), U.2 q hq d (by omega)]
  · rw [hbase', S.2]; exact hfit
  · rw [S.2]; exact hrows.nde31
  · rw [hbase'] at hj
    by_cases h : j < base R sr
    · rw [B.2 j (by simpa [base] using h)]; exact hrows.small j h
    · obtain ⟨q, hq, h1, h2⟩ := locate (Graph.ofGraph G) lab sr (base R sr) (n - sr) j (by omega) hj
      obtain ⟨d, rfl⟩ : ∃ d, j = start (Graph.ofGraph G) lab sr (base R sr) q + d := ⟨j - start (Graph.ofGraph G) lab sr (base R sr) q, by omega⟩
      rw [hstq] at h2
      rw [U.2 q hq d (by omega)]
      exact inverse_lt hlsz hn0 _

/-- `k = samerows == 0 ? 0 : cv[samerows-1] + cd[samerows-1]` sets `k` to `base R samerows`. -/
theorem wp_setK {n : Nat} {Q : Post} {le : temp_env} {m : mem} {R : Rows n} {sr : Nat} {cbv : block}
    {cvo : ptrofs} {cbd : block} {cdofs : ptrofs} {vv dv ev : Nat → val}
    (hsrV : PTree.get id.samerows le = some (.Vint (ir sr)))
    (hcvV : PTree.get id.cv le = some (.Vptr cbv cvo)) (hcdV : PTree.get id.cd le = some (.Vptr cbd cdofs))
    (hcv : ArrayAt m .Mint64 cbv (intOfZ (Ptrofs.unsigned cvo)) vv n)
    (hcd : ArrayAt m .Mint32 cbd (intOfZ (Ptrofs.unsigned cdofs)) dv n)
    (hrows : CanonRows R sr vv dv ev) (hn31 : n < 2147483648)
    (hQ : ∀ le', PTree.get id.k le' = some (.Vlong (lr (base R sr))) →
      (∀ x, x ≠ id.k → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m) :
    Wp xi sge F setK Q empty_env le m := by
  have hsr := hrows.bound
  have hnd := hrows.nde31
  wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le m (tv id.samerows) = _ from hsrV]
  simp only [Exec.evalExpr, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 0) = ir 0 from rfl,
    ir_eq (a := (sr : Int)) (b := 0) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
  by_cases hs0 : sr = 0
  · subst hs0
    simp (config := {decide := true}) only [cop, ite_true, Val.of_bool]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩]
    exact hQ _ (temps_gss _ _ _) fun x hx => temps_gso _ _ hx
  · rw [show decide ((sr : Int) = 0) = false from decide_eq_false (by omega)]
    simp (config := {decide := true}) only [cop, ite_false, Val.of_bool]
    have hsub : Exec.evalExpr sge empty_env le m (.Ebinop .Osub (tv id.samerows) (ci 1 tint) tint) =
        some (.Vint (ir ((sr - 1 : Nat) : Int))) := by
      simp only [Exec.evalExpr, hsrV, typeof, cop, show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl,
        ir_sub]
      rw [show ((sr : Int) - 1) = ((sr - 1 : Nat) : Int) by omega]
    have hi := hrows.mono (sr - 1) (by omega)
    have hend := hrows.end_le (show sr - 1 < sr by omega)
    have hb : base R sr = R.offsets[sr]! := by simp [base, hs0]
    rw [show sr - 1 + 1 = sr by omega] at hi hend
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, eval_tidx (ge := sge) hcv hn31 hcvV rfl rfl _ (sr - 1) (by omega) hsub rfl,
      eval_tidx (ge := sge) hcd hn31 hcdV rfl rfl _ (sr - 1) (by omega) hsub rfl,
      hrows.v (sr - 1) (by omega), hrows.d (sr - 1) (by omega)]
    have hdeg : R.degree (sr - 1) = R.offsets[sr]! - R.offsets[sr - 1]! := by
      show R.offsets[sr - 1 + 1]! - _ = _; rw [show sr - 1 + 1 = sr by omega]
    have hd31 : R.degree (sr - 1) < 2147483648 := by
      have := hrows.base_le; rw [hdeg]; omega
    simp only [typeof, cop, cast_l_i _ hd31, Sparse.lr_add]
    refine hQ _ ?_ fun x hx => temps_gso _ _ hx
    rw [temps_gss, hb, hdeg, Nat.add_sub_cancel' hi]

theorem updatecan_satisfies {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs)
    (bv : block) (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (R : Rows n)
    (bc : block) (cofs : ptrofs) (cbv : block) (cvo : ptrofs) (cbd : block) (cdofs : ptrofs)
    (cbe : block) (ceo : ptrofs) (lab : Array Nat) (bl : block) (lofs : ptrofs) (sr M capW : Nat)
    (bW : block) :
    Satisfies xi sge (.Internal F) (updatecanSpec G bsg sofs bv vo bd dofs be eo R bc cofs cbv cvo cbd
      cdofs cbe ceo lab bl lofs sr M capW bW) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bsg sofs bc cofs bl lofs sr M n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bsg sofs bc cofs bl lofs sr M n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩,
      rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hgr, hca, hosz, hfit, hcofs, hlarr, hlsz, hls, hinj, hsurj, hDW, hn0, hn31,
      hsep, hWR, hbc1, hbc2, hbc3, hc12, hc13, hc23⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [sparse.fn.updatecan_sg.fn_body_eq, body_eq]
    obtain ⟨vv, dv, ev, hcvarr, hcdarr, hcearr, hrows⟩ := hca.rows
    have hsr := hrows.bound
    have hnd := hrows.nde31
    let le0 := entryTemps bsg sofs bc cofs bl lofs sr M n
    wp_step
    refine wp_vdew (bsg := bsg) (sofs := sofs)
      (by simp (config := {decide := true}) only [le0, entryTemps, temps_gso, temps_gss])
      (by decide) (by decide) (by decide) hgr.v hgr.d hgr.e hgr.w ?_
    wp_step
    refine wp_vdew (bsg := bc) (sofs := cofs)
      (by simp (config := {decide := true}) only [le0, entryTemps, temps_gso, temps_gss])
      (by decide) (by decide) (by decide) hca.v hca.d hca.e hca.w ?_
    let leV := PTree.set id.cwt Vnullptr (PTree.set id.ce (.Vptr cbe ceo) (PTree.set id.cd (.Vptr cbd cdofs)
      (PTree.set id.cv (.Vptr cbv cvo) (PTree.set id.wt Vnullptr (PTree.set id.e (.Vptr be eo)
        (PTree.set id.d (.Vptr bd dofs) (PTree.set id.v (.Vptr bv vo) le0)))))))
    have hnV : PTree.get id.n leV = some (.Vint (ir n)) := by
      simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss]
    wp_step
    refine Alloc.wp_dynalloc1 (E := NautyEnv.sparse) find_work1Sz find_work1 rfl hDW hnV hn31
      (show 4 * n < 2 ^ 62 by omega) ?_
    intro le1 m1 capW1 bW1 hDW1 hnW hu1 hor1 hg1 ho1
    have hcW1 : 0 < capW1 := by omega
    have hvW : Mem.valid_block m Block.work1 := Alloc.valid_of_access hDW.bpW
    have hext : ∀ z, Rd bsg bv bd be bl z ∨ Wr bc cbv cbd cbe z →
        ¬ (z = Block.work1Sz ∨ z = Block.work1 ∨ (0 < capW ∧ z = bW) ∨
          (¬ Mem.valid_block m bW1 ∧ z = bW1)) ∧ z ≠ bW1 := fun z hz =>
      ⟨Alloc.not_dynSet (hsep z hz).1 (hsep z hz).2.2.1 (hsep z hz).2.1 (hsep z hz).2.2.2,
       Alloc.ne_new hor1 (hsep z hz).1 (hsep z hz).2.2.2 hcW1⟩
    have hget1 : ∀ x, x ≠ idOf 703 → x ≠ idOf 704 → PTree.get x le1 = PTree.get x leV := ho1
    have hcan1 : PTree.get id.canong le1 = some (.Vptr bc cofs) := by
      rw [hget1 _ (by decide) (by decide)]
      simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss]
    have hg1' : PTree.get id.g le1 = some (.Vptr bsg sofs) := by
      rw [hget1 _ (by decide) (by decide)]
      simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss]
    have hnL : PTree.get id.n le1 = some (.Vint (ir n)) := by
      rw [hget1 _ (by decide) (by decide)]; exact hnV
    have eBc : Rd bsg bv bd be bl bc ∨ Wr bc cbv cbd cbe bc := .inr (.inl rfl)
    have eBsg : Rd bsg bv bd be bl bsg ∨ Wr bc cbv cbd cbe bsg := .inl (.inl rfl)
    have hbcg : bc ≠ bsg := fun h => hWR bc (.inl rfl) (.inl h)
    -- canong->nv = n
    wp_step
    refine wp_setField hcan1 (lval_nv _ _) rfl (by simp only [Exec.evalExpr]; exact hnL) rfl rfl
      (hu1.access _ _ _ _ (hext bc eBc).1 hca.nvW) ?_
    intro m2 hst2
    -- canong->nde = g->nde
    have hnde2 : Mem.load .Mint64 m2 bsg (fofs sofs 0) = some (.Vlong (lr G.neighbors.size)) := by
      rw [Mem.load_store_other _ _ _ _ _ _ hst2 _ _ _ (.inl hbcg.symm), hu1.load _ _ _ (hext bsg eBsg).1]
      exact hgr.nde
    wp_step
    refine wp_setField hcan1 (lval_nde _ _) rfl (eval_sgField hg1' (lval_nde _ _) rfl hnde2) rfl rfl
      (Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _ (hu1.access _ _ _ _ (hext bc eBc).1 hca.ndeW)) ?_
    intro m3 hst3
    have hu23 : Unch m1 m3 (· = bc) :=
      ((Unch.store hst2 rfl).trans (Unch.store hst3 rfl)).mono fun z (h : bc = z) => h.symm
    have hg13 : ∀ z, Mem.valid_block m1 z → Mem.valid_block m3 z := fun z h =>
      Mem.store_valid_block_1 _ _ _ _ _ _ hst3 _ (Mem.store_valid_block_1 _ _ _ _ _ _ hst2 _ h)
    have hbcW1 : bc ≠ bW1 := (hext bc eBc).2
    have hDW3 : Alloc.DynAt m3 Block.work1 Block.work1Sz 4 capW1 bW1 :=
      hDW1.keep hu23 (fun h => (hsep bc eBc).2.1 h.symm) (fun h => (hsep bc eBc).2.2.1 h.symm)
        (fun _ => Alloc.Keep.unch hu23 (fun h => hbcW1 h.symm))
    have tr : ∀ {z : block} {chunk : memory_chunk} {base : Int} {vals : Nat → val} {k : Nat},
        (Rd bsg bv bd be bl z ∨ Wr bc cbv cbd cbe z) → z ≠ bc → ArrayAt m chunk z base vals k →
        ArrayAt m3 chunk z base vals k := fun hz hzc h =>
      (h.unch hu1 (hext _ hz).1).unch hu23 hzc
    have hRd : ∀ z, Rd bsg bv bd be bl z → z ≠ bc := fun z hz h => hWR bc (.inl rfl) (h ▸ hz)
    obtain ⟨wv, hwarr⟩ := Alloc.malloced_array (hDW3.mal hcW1) .Mint32 4 rfl rfl n (by omega)
    have hlarr3 := tr (.inl (.inr (.inr (.inr (.inr rfl))))) (hRd bl (.inr (.inr (.inr (.inr rfl))))) hlarr
    wp_step
    refine Testcanlab.wp_scatter (f := F) (bl := bl) (lofs := lofs)
      (by rw [hget1 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss])
      hlarr3 hlsz hls hinj hsurj hnL hn31 (hDW3.ptr hcW1) hwarr
      (hext bl (.inl (.inr (.inr (.inr (.inr rfl)))))).2 (hDW3.bne hcW1).2.symm ?_
    intro le4 m4 hwarr4 hu4 hk4 hg4 ho4
    let g := Graph.ofGraph G
    have hget4 : ∀ x, x ≠ id.i → x ≠ idOf 703 → x ≠ idOf 704 → PTree.get x le4 = PTree.get x leV :=
      fun x h1 h2 h3 => by rw [ho4 x h1, hget1 x h2 h3]
    have eR : ∀ {z}, Rd bsg bv bd be bl z → Rd bsg bv bd be bl z ∨ Wr bc cbv cbd cbe z := fun h => .inl h
    have eW : ∀ {z}, Wr bc cbv cbd cbe z → Rd bsg bv bd be bl z ∨ Wr bc cbv cbd cbe z := fun h => .inr h
    have t4 : ∀ {z : block} {chunk : memory_chunk} {base : Int} {vals : Nat → val} {k : Nat}
        (hz : Rd bsg bv bd be bl z ∨ Wr bc cbv cbd cbe z), z ≠ bc → ArrayAt m chunk z base vals k →
        ArrayAt m4 chunk z base vals k := fun hz hzc h => (tr hz hzc h).unch hu4 (hext _ hz).2
    have wcv : Wr bc cbv cbd cbe cbv := .inr (.inl rfl)
    have wcd : Wr bc cbv cbd cbe cbd := .inr (.inr (.inl rfl))
    have wce : Wr bc cbv cbd cbe cbe := .inr (.inr (.inr rfl))
    have hcv4 := t4 (eW wcv) hbc1.symm hcvarr
    have hcd4 := t4 (eW wcd) hbc2.symm hcdarr
    have hce4 := t4 (eW wce) hbc3.symm hcearr
    have hW4 : Mem.load .Mint64 m4 Block.work1 (zOfInt 0) = some (.Vptr bW1 Ptrofs.zero) := by
      rw [hu4.load _ _ _ (fun h => (hDW3.bne hcW1).2 h.symm)]; exact hDW3.ptr hcW1
    have gv : ∀ {x : ident} {w : val}, x ≠ id.i → x ≠ idOf 703 → x ≠ idOf 704 → PTree.get x leV = some w →
        PTree.get x le4 = some w := fun h1 h2 h3 h => by rw [hget4 _ h1 h2 h3]; exact h
    have hf : Frame m4 le4 G bv vo bd dofs be eo cbv cvo cbd cdofs cbe ceo lab bl lofs bW1 :=
      { hv := gv (by decide) (by decide) (by decide)
          (by simp (config := {decide := true}) only [leV, temps_gso, temps_gss])
        hd := gv (by decide) (by decide) (by decide)
          (by simp (config := {decide := true}) only [leV, temps_gso, temps_gss])
        he := gv (by decide) (by decide) (by decide)
          (by simp (config := {decide := true}) only [leV, temps_gso, temps_gss])
        hwt := gv (by decide) (by decide) (by decide)
          (by simp (config := {decide := true}) only [leV, temps_gso, temps_gss])
        hcv := gv (by decide) (by decide) (by decide)
          (by simp (config := {decide := true}) only [leV, temps_gso, temps_gss])
        hcd := gv (by decide) (by decide) (by decide)
          (by simp (config := {decide := true}) only [leV, temps_gso, temps_gss])
        hce := gv (by decide) (by decide) (by decide)
          (by simp (config := {decide := true}) only [leV, temps_gso, temps_gss])
        hlab := gv (by decide) (by decide) (by decide)
          (by simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss])
        hn := gv (by decide) (by decide) (by decide) hnV
        varr := t4 (eR (.inr (.inl rfl))) (hRd bv (.inr (.inl rfl))) hgr.varr
        darr := t4 (eR (.inr (.inr (.inl rfl)))) (hRd bd (.inr (.inr (.inl rfl)))) hgr.darr
        earr := t4 (eR (.inr (.inr (.inr (.inl rfl))))) (hRd be (.inr (.inr (.inr (.inl rfl))))) hgr.earr
        larr := t4 (eR (.inr (.inr (.inr (.inr rfl))))) (hRd bl (.inr (.inr (.inr (.inr rfl))))) hlarr
        hls := hls, wptr := hW4, warr := hwarr4, n31 := hn31 }
    have hsrV : PTree.get id.samerows le4 = some (.Vint (ir sr)) := gv (by decide) (by decide) (by decide)
      (by simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss])
    have hsepR : ∀ z, (z = cbv ∨ z = cbd ∨ z = cbe) → z ≠ bv ∧ z ≠ bd ∧ z ≠ be ∧ z ≠ bl ∧
        z ≠ Block.work1 ∧ z ≠ bW1 := by
      intro z hz
      have hw : Wr bc cbv cbd cbe z := .inr hz
      have hnr := hWR z hw
      exact ⟨fun h => hnr (.inr (.inl h)), fun h => hnr (.inr (.inr (.inl h))),
        fun h => hnr (.inr (.inr (.inr (.inl h)))), fun h => hnr (.inr (.inr (.inr (.inr h)))),
        (hsep z (.inr hw)).2.1, (hext z (.inr hw)).2⟩
    wp_step
    refine wp_setK hsrV hf.hcv hf.hcd hcv4 hcd4 hrows hn31 ?_
    intro le5 hk5 ho5
    have hf5 := hf.temps (le' := le5) fun x _ hx => ho5 x (fun h => hx (by subst h; decide))
    let st := start g lab sr (base R sr)
    have hst_le := fun {a b : Nat} (h : a ≤ b) => start_mono g lab sr (base R sr) h
    have hstq : ∀ q, st (q + 1) = st q + g.degree lab[sr + q]! := fun _ => rfl
    have hb_le : base R sr ≤ st 0 := Nat.le_refl _
    let Inv := fun (p : Nat) (le' : temp_env) (m' : mem) => ∃ vv' dv' ev',
      PTree.get id.k le' = some (.Vlong (lr (st p))) ∧
      ArrayAt m' .Mint64 cbv (intOfZ (Ptrofs.unsigned cvo)) vv' n ∧
      ArrayAt m' .Mint32 cbd (intOfZ (Ptrofs.unsigned cdofs)) dv' n ∧
      ArrayAt m' .Mint32 cbe (intOfZ (Ptrofs.unsigned ceo)) ev' R.neighbors.size ∧
      (∀ i < sr, vv' i = vv i ∧ dv' i = dv i) ∧
      (∀ q < p, vv' (sr + q) = .Vlong (lr (st q)) ∧ dv' (sr + q) = .Vint (ir (g.degree lab[sr + q]!))) ∧
      (∀ e < base R sr, ev' e = ev e) ∧
      (∀ q < p, ∀ j < g.degree lab[sr + q]!, ev' (st q + j) = nbv G lab g.offsets[lab[sr + q]!]! j) ∧
      Unch m4 m' (fun z => z = cbv ∨ z = cbd ∨ z = cbe) ∧
      (∀ z, Mem.valid_block m4 z → Mem.valid_block m' z) ∧
      ∀ x, x ≠ id.i → ¬ RowLocal x → PTree.get x le' = PTree.get x le5
    let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
      e' = empty_env ∧ ∃ p, p ≤ n - sr ∧ v = n - sr - p ∧
        PTree.get id.i le' = some (.Vint (ir (sr + p))) ∧ Inv p le' m'
    let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
      e' = empty_env ∧ ∃ p, p < n - sr ∧ v = n - sr - p ∧
        PTree.get id.i le' = some (.Vint (ir (sr + p))) ∧ Inv (p + 1) le' m'
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [show Exec.evalExpr sge empty_env le5 m4 (tv id.samerows) = _ by
      show PTree.get _ _ = _; rw [ho5 _ (by decide), hsrV]]
    refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - sr - 0)
      ⟨rfl, rfl, 0, Nat.zero_le _, rfl, by rw [temps_gss]; simp, vv, dv, ev,
        by rw [temps_gso _ _ (by decide)]; exact hk5, hcv4, hcd4, hce4, fun i _ => ⟨rfl, rfl⟩,
        fun q hq => absurd hq (by omega), fun _ _ => rfl, fun q hq => absurd hq (by omega), Unch.refl _ _,
        fun _ h => h, fun x hx _ => temps_gso _ _ hx⟩
    · rintro v t e' le' m' ⟨rfl, rfl, p, hp, rfl, hi, vv', dv', ev', hk', hcv', hcd', hce', P1, P2, P3, P4,
        hu', hg', ho'⟩
      have hf' := (hf5.mem hu' (fun h => (hsepR _ h).1 rfl) (fun h => (hsepR _ h).2.1 rfl)
        (fun h => (hsepR _ h).2.2.1 rfl) (fun h => (hsepR _ h).2.2.2.1 rfl)
        (fun h => (hsepR _ h).2.2.2.2.1 rfl) (fun h => (hsepR _ h).2.2.2.2.2 rfl)).temps ho'
      wp_step; wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tv id.i) = _ from hi,
        show Exec.evalExpr sge empty_env le' m' (tv id.n) = _ from hf'.hn]
      simp only [typeof, cop]
      rw [ir_lt (a := (sr : Int) + p) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hpn : sr + p < n
      · rw [ite_eq_left (by simp; omega)]
        apply wp_skip
        have hKD : st p + g.degree lab[sr + p]! ≤ R.neighbors.size := by
          rw [← hstq]; exact Nat.le_trans (hst_le (by omega)) hfit
        refine wp_row hf' hi hpn hk' hcv' hcd' hce' hKD hnd hsepR ⟨hc12, hc13, hc23⟩ ?_
        intro le'' m'' ev'' hcv'' hcd'' hce'' hlow hrow hk'' hu'' hg'' ho''
        refine ⟨by simp, rfl, p, by omega, rfl, by rw [ho'' _ (by decide)]; exact hi,
          upd vv' (sr + p) (.Vlong (lr (st p))), upd dv' (sr + p) (.Vint (ir (g.degree lab[sr + p]!))), ev'',
          hk'', hcv'', hcd'', hce'', fun i hi' => ?_, fun q hq => ?_, fun e he => ?_,
          fun q hq j hj => ?_, hu'.trans hu'', fun z h => hg'' _ (hg' _ h),
          fun x hx hx' => by rw [ho'' x hx', ho' x hx hx']⟩
        · rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]; exact P1 i hi'
        · by_cases hqp : q = p
          · subst hqp; exact ⟨upd_same _ _ _, upd_same _ _ _⟩
          · rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]; exact P2 q (by omega)
        · rw [hlow e (Nat.lt_of_lt_of_le he (hst_le (Nat.zero_le p)))]; exact P3 e he
        · by_cases hqp : q = p
          · subst hqp; exact hrow j hj
          · have h1 : st (q + 1) ≤ st p := hst_le (by omega)
            rw [hstq] at h1
            rw [hlow _ (by omega)]; exact P4 q (by omega) j hj
      · rw [ite_eq_right (by simp; omega)]
        apply wp_break
        have hp' : p = n - sr := by omega
        subst hp'
        refine ⟨m', Isautom.free_empty _, ?_⟩
        have hbcS : ¬ (bc = cbv ∨ bc = cbd ∨ bc = cbe) := by
          rintro (h | h | h)
          · exact hbc1 h
          · exact hbc2 h
          · exact hbc3 h
        have hS1 := (hext bc eBc).1
        -- a load from `canong` survives from `m` to `m'`
        have fld : ∀ {k : Int} {v : val}, (k = 8 ∨ (24 ≤ k ∧ k ≤ 40)) →
            Mem.load .Mint64 m bc (fofs cofs k) = some v → Mem.load .Mint64 m' bc (fofs cofs k) = some v := by
          intro k v hk h
          have c8 : csize .Mint64 = 8 := rfl
          have c4 : csize .Mint32 = 4 := rfl
          rw [hu'.load _ _ _ hbcS, hu4.load _ _ _ hbcW1]
          refine load_field_other hcofs (by omega) (by omega) (by decide) (by decide) (.inr (by omega)) hst3 ?_
          refine load_field_other hcofs (by omega) (by omega) (by decide) (by decide) (by omega) hst2 ?_
          rw [hu1.load _ _ _ hS1]; exact h
        have acc : ∀ {c : memory_chunk} {k : Int}, Mem.valid_access m2 c bc (fofs cofs k) .Writable →
            Mem.valid_access m' c bc (fofs cofs k) .Writable := fun h =>
          hu'.access _ _ _ _ hbcS (hu4.access _ _ _ _ hbcW1 (Mem.store_valid_access_1 _ _ _ _ _ _ hst3 _ _ _ _ h))
        have hcanon : CanonAt m' bc cofs (Hex.GraphIso.Nauty.Sparse.updatecan (Graph.ofGraph G) R lab sr) n
            cbv cvo cbd cdofs cbe ceo :=
          { ndeW := acc (Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _ (hu1.access _ _ _ _ hS1 hca.ndeW))
            v := fld (.inl rfl) hca.v
            nvW := acc (Mem.store_valid_access_1 _ _ _ _ _ _ hst2 _ _ _ _ (hu1.access _ _ _ _ hS1 hca.nvW))
            d := fld (.inr ⟨by decide, by decide⟩) hca.d
            e := fld (.inr ⟨by decide, by decide⟩) hca.e
            w := fld (.inr ⟨by decide, by decide⟩) hca.w
            rows := ⟨vv', dv', ev', hcv', hcd',
              by rw [(Hex.GraphIso.Nauty.Sparse.updatecan_sizes _ R lab sr).2]; exact hce',
              canonRows_update G R lab sr hrows hosz hfit hn0 hlsz P1 (by simpa using P2) P3
                (by simpa using P4)⟩ }
        have hnv : Mem.load .Mint32 m' bc (fofs cofs 16) = some (.Vint (ir n)) := by
          rw [hu'.load _ _ _ hbcS, hu4.load _ _ _ hbcW1]
          refine load_field_other hcofs (by decide) (by decide) (by decide) (by decide) (.inr (by decide))
            hst3 ?_
          rw [Mem.load_store_same _ _ _ _ _ _ hst2]; rfl
        have hnde : Mem.load .Mint64 m' bc (fofs cofs 0) = some (.Vlong (lr G.neighbors.size)) := by
          rw [hu'.load _ _ _ hbcS, hu4.load _ _ _ hbcW1, Mem.load_store_same _ _ _ _ _ _ hst3]; rfl
        have hWS : ∀ z, (z = cbv ∨ z = cbd ∨ z = cbe) → z ≠ Block.work1 ∧ z ≠ Block.work1Sz ∧ z ≠ bW1 :=
          fun z hz => ⟨(hsep z (.inr (.inr hz))).2.1, (hsep z (.inr (.inr hz))).2.2.1, (hext z (.inr (.inr hz))).2⟩
        have hDWf : Alloc.DynAt m' Block.work1 Block.work1Sz 4 capW1 bW1 :=
          (hDW3.keep hu4 (fun h => (hDW3.bne hcW1).2 h.symm) (fun h => (hDW3.bne hcW1).1 h.symm)
            (fun _ => hk4)).keep hu' (fun h => (hWS _ h).1 rfl) (fun h => (hWS _ h).2.1 rfl)
            (fun _ => Alloc.Keep.unch hu' fun h => (hWS _ h).2.2 rfl)
        refine ⟨rfl, capW1, bW1, hDWf, hnW, hor1, hcanon, hnv, hnde, ?_,
          fun z h => hg' _ (hg4 _ (hg13 _ (hg1 _ h)))⟩
        refine (((hu1.mono fun z hz => ?_).trans (hu23.mono fun z hz => .inl (.inl hz))).trans
          (hu4.mono fun z hz => ?_)).trans (hu'.mono fun z hz => .inl (.inr hz))
        · rcases hz with h | h | h | h
          · exact .inr (.inr (.inl h))
          · exact .inr (.inl h)
          · exact .inr (.inr (.inr (.inl h)))
          · exact .inr (.inr (.inr (.inr h)))
        · subst hz
          rcases hor1 with ⟨h1, h2⟩ | hnv'
          · exact .inr (.inr (.inr (.inl ⟨by omega, h2⟩)))
          · exact .inr (.inr (.inr (.inr ⟨hnv', rfl⟩)))
    · rintro v t e' le' m' ⟨rfl, rfl, p, hp, rfl, hi, hinv⟩
      wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tv id.i) = _ from hi]
      simp only [Exec.evalExpr, typeof, cop, ir_add]
      obtain ⟨vv', dv', ev', hk', hcv', hcd', hce', P1, P2, P3, P4, hu', hg', ho'⟩ := hinv
      exact ⟨n - sr - (p + 1), by omega, by simp, rfl, p + 1, by omega, rfl,
        by rw [temps_gss]; push_cast; rfl, vv', dv', ev', by rw [temps_gso _ _ (by decide)]; exact hk',
        hcv', hcd', hce', P1, P2, P3, P4, hu', hg', fun x hx hx' => by rw [temps_gso _ _ hx, ho' x hx hx']⟩

end NautyVerified.Proofs.Sparse.Updatecan

import NautyVerified.Proofs.Sparse.Updatecan.Copy

/-!
# One row of `updatecan_sg`

`wp_row`: row `c` stores `k` (`K`) in `cv[c]`, the degree of `lab[c]` in
`cd[c]`, the relabelled neighbours of `lab[c]` from `ce[K]`, and advances `k`
by that degree (`wt` is `NULL`).
-/

namespace NautyVerified.Proofs.Sparse.Updatecan

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat cast_l_i)
open Hex.GraphIso.Nauty.Sparse (Graph Rows inverse)

variable {xi : ExternalCalls}

/-- The temporaries a row changes. -/
def RowLocal (x : ident) : Prop :=
  x = id.t1 ∨ x = id.dli ∨ x = id.vli ∨ x = id.j ∨ x = id.k ∨ x = id.t2

instance (x : ident) : Decidable (RowLocal x) := by unfold RowLocal; infer_instance

/-- What the rows read. -/
structure Frame {n : Nat} (m : mem) (le : temp_env) (G : Hex.SparseGraph n) (bv : block) (vo : ptrofs)
    (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (cbv : block) (cvo : ptrofs) (cbd : block)
    (cdofs : ptrofs) (cbe : block) (ceo : ptrofs) (lab : Array Nat) (bl : block) (lofs : ptrofs)
    (bW : block) : Prop where
  hv : PTree.get id.v le = some (.Vptr bv vo)
  hd : PTree.get id.d le = some (.Vptr bd dofs)
  he : PTree.get id.e le = some (.Vptr be eo)
  hwt : PTree.get id.wt le = some Vnullptr
  hcv : PTree.get id.cv le = some (.Vptr cbv cvo)
  hcd : PTree.get id.cd le = some (.Vptr cbd cdofs)
  hce : PTree.get id.ce le = some (.Vptr cbe ceo)
  hlab : PTree.get id.lab le = some (.Vptr bl lofs)
  hn : PTree.get id.n le = some (.Vint (ir n))
  varr : ArrayAt m .Mint64 bv (intOfZ (Ptrofs.unsigned vo)) (vVals G) n
  darr : ArrayAt m .Mint32 bd (intOfZ (Ptrofs.unsigned dofs)) (dVals G) n
  earr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size
  larr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n
  hls : ∀ j < n, lab[j]! < n
  wptr : Mem.load .Mint64 m Block.work1 (zOfInt 0) = some (.Vptr bW Ptrofs.zero)
  warr : ArrayAt m .Mint32 bW 0 (fun p => .Vint (ir (((inverse n lab)[p]! : Nat) : Int))) n
  n31 : n < 2147483648

section
variable {n : Nat} {m m' : mem} {le le' : temp_env} {G : Hex.SparseGraph n} {bv : block} {vo : ptrofs}
    {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {cbv : block} {cvo : ptrofs} {cbd : block}
    {cdofs : ptrofs} {cbe : block} {ceo : ptrofs} {lab : Array Nat} {bl : block} {lofs : ptrofs}
    {bW : block}

theorem Frame.temps (h : Frame m le G bv vo bd dofs be eo cbv cvo cbd cdofs cbe ceo lab bl lofs bW)
    (hle : ∀ x, x ≠ id.i → ¬ RowLocal x → PTree.get x le' = PTree.get x le) :
    Frame m le' G bv vo bd dofs be eo cbv cvo cbd cdofs cbe ceo lab bl lofs bW :=
  { h with
    hv := by rw [hle _ (by decide) (by decide)]; exact h.hv
    hd := by rw [hle _ (by decide) (by decide)]; exact h.hd
    he := by rw [hle _ (by decide) (by decide)]; exact h.he
    hwt := by rw [hle _ (by decide) (by decide)]; exact h.hwt
    hcv := by rw [hle _ (by decide) (by decide)]; exact h.hcv
    hcd := by rw [hle _ (by decide) (by decide)]; exact h.hcd
    hce := by rw [hle _ (by decide) (by decide)]; exact h.hce
    hlab := by rw [hle _ (by decide) (by decide)]; exact h.hlab
    hn := by rw [hle _ (by decide) (by decide)]; exact h.hn }

theorem Frame.mem (h : Frame m le G bv vo bd dofs be eo cbv cvo cbd cdofs cbe ceo lab bl lofs bW)
    {S : block → Prop} (hu : Unch m m' S) (h1 : ¬ S bv) (h2 : ¬ S bd) (h3 : ¬ S be) (h4 : ¬ S bl)
    (h5 : ¬ S Block.work1) (h6 : ¬ S bW) :
    Frame m' le G bv vo bd dofs be eo cbv cvo cbd cdofs cbe ceo lab bl lofs bW :=
  { h with
    varr := h.varr.unch hu h1, darr := h.darr.unch hu h2, earr := h.earr.unch hu h3
    larr := h.larr.unch hu h4
    wptr := by rw [hu.load _ _ _ h5]; exact h.wptr
    warr := h.warr.unch hu h6 }
end

/-- One row. -/
theorem wp_row {n : Nat} {Q : Post} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {bv : block}
    {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {cbv : block} {cvo : ptrofs}
    {cbd : block} {cdofs : ptrofs} {cbe : block} {ceo : ptrofs} {lab : Array Nat} {bl : block}
    {lofs : ptrofs} {bW : block} {vv dv ev : Nat → val} {N K c : Nat}
    (hf : Frame m le G bv vo bd dofs be eo cbv cvo cbd cdofs cbe ceo lab bl lofs bW)
    (hi : PTree.get id.i le = some (.Vint (ir c))) (hc : c < n)
    (hk : PTree.get id.k le = some (.Vlong (lr K)))
    (hcvarr : ArrayAt m .Mint64 cbv (intOfZ (Ptrofs.unsigned cvo)) vv n)
    (hcdarr : ArrayAt m .Mint32 cbd (intOfZ (Ptrofs.unsigned cdofs)) dv n)
    (hcearr : ArrayAt m .Mint32 cbe (intOfZ (Ptrofs.unsigned ceo)) ev N)
    (hKD : K + (Graph.ofGraph G).degree lab[c]! ≤ N) (hN : N < 2147483648)
    (hsep : ∀ z, (z = cbv ∨ z = cbd ∨ z = cbe) → z ≠ bv ∧ z ≠ bd ∧ z ≠ be ∧ z ≠ bl ∧
      z ≠ Block.work1 ∧ z ≠ bW)
    (hcc : cbv ≠ cbd ∧ cbv ≠ cbe ∧ cbd ≠ cbe)
    (hQ : ∀ le' m' ev', ArrayAt m' .Mint64 cbv (intOfZ (Ptrofs.unsigned cvo)) (upd vv c (.Vlong (lr K))) n →
      ArrayAt m' .Mint32 cbd (intOfZ (Ptrofs.unsigned cdofs))
        (upd dv c (.Vint (ir ((Graph.ofGraph G).degree lab[c]!)))) n →
      ArrayAt m' .Mint32 cbe (intOfZ (Ptrofs.unsigned ceo)) ev' N →
      (∀ e, e < K → ev' e = ev e) →
      (∀ j < (Graph.ofGraph G).degree lab[c]!,
        ev' (K + j) = nbv G lab (Graph.ofGraph G).offsets[lab[c]!]! j) →
      PTree.get id.k le' = some (.Vlong (lr (K + (Graph.ofGraph G).degree lab[c]!))) →
      Unch m m' (fun z => z = cbv ∨ z = cbd ∨ z = cbe) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, ¬ RowLocal x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m') :
    Wp xi sge F row Q empty_env le m := by
  have hn31 := hf.n31
  have hlc := hf.hls c hc
  have hgd : (Graph.ofGraph G).degree lab[c]! ≤ n := degree_lt G hlc
  have hs1 := hsep cbv (.inl rfl)
  have hs2 := hsep cbd (.inr (.inl rfl))
  have hs3 := hsep cbe (.inr (.inr rfl))
  -- cv[i] = k
  wp_step; wp_step; wp_step
  refine wp_idx_store (chunk := .Mint64) (bo := cbv) (ofs := cvo) hcvarr hn31
    (by simp only [Exec.evalExpr]; exact hf.hcv) rfl rfl rfl (tv id.i) c hc hi rfl (tl id.k) tulong rfl
    (.Vlong (lr K)) (.Vlong (lr K)) hk rfl rfl ?_
  intro m1 hcv1 hu1 hk1 hg1
  have hf1 := hf.mem hu1 (fun h => hs1.1 h.symm) (fun h => hs1.2.1 h.symm) (fun h => hs1.2.2.1 h.symm)
    (fun h => hs1.2.2.2.1 h.symm) (fun h => hs1.2.2.2.2.1 h.symm) (fun h => hs1.2.2.2.2.2 h.symm)
  have hcd1 := hcdarr.unch hu1 (fun h => hcc.1 h.symm)
  have hce1 := hcearr.unch hu1 (fun h => hcc.2.1 h.symm)
  -- dli = cd[i] = d[lab[i]]
  wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_tidx (ge := sge) hf1.darr hn31 hf1.hd rfl rfl _ lab[c]! hlc
    (eval_tidx (ge := sge) hf1.larr hn31 hf1.hlab rfl rfl (tv id.i) c hc hi rfl) rfl]
  simp only [dVals, typeof, cop]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss]
  let le2 := PTree.set id.dli (.Vint (ir ((Graph.ofGraph G).degree lab[c]!)))
    (PTree.set id.t1 (.Vint (ir ((Graph.ofGraph G).degree lab[c]!))) le)
  have hi2 : PTree.get id.i le2 = some (.Vint (ir c)) := by
    rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hi
  have hf2 : Frame m1 le2 G bv vo bd dofs be eo cbv cvo cbd cdofs cbe ceo lab bl lofs bW :=
    hf1.temps fun x _ hx => by
      rw [temps_gso _ _ (fun h => hx (by subst h; decide)), temps_gso _ _ (fun h => hx (by subst h; decide))]
  refine wp_idx_store (chunk := .Mint32) (bo := cbd) (ofs := cdofs) hcd1 hn31
    (by simp only [Exec.evalExpr]; exact hf2.hcd) rfl rfl rfl (tv id.i) c hc hi2 rfl
    (.Etempvar id.t1 tint) tint rfl (.Vint (ir ((Graph.ofGraph G).degree lab[c]!))) (.Vint (ir ((Graph.ofGraph G).degree lab[c]!)))
    (by show PTree.get id.t1 le2 = _; rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _) rfl rfl ?_
  intro m2 hcd2 hu2 hk2 hg2
  have hf3 := hf2.mem hu2 (fun h => hs2.1 h.symm) (fun h => hs2.2.1 h.symm) (fun h => hs2.2.2.1 h.symm)
    (fun h => hs2.2.2.2.1 h.symm) (fun h => hs2.2.2.2.2.1 h.symm) (fun h => hs2.2.2.2.2.2 h.symm)
  have hcv2 := hcv1.unch hu2 (fun h => hcc.1 h)
  have hce2 := hce1.unch hu2 (fun h => hcc.2.2 h.symm)
  -- vli = v[lab[i]]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tidx (ge := sge) hf3.varr hn31 hf3.hv rfl rfl _ lab[c]! hlc
    (eval_tidx (ge := sge) hf3.larr hn31 hf3.hlab rfl rfl (tv id.i) c hc hi2 rfl) rfl]
  simp only [vVals]
  let le3 := PTree.set id.vli (.Vlong (lr (Graph.ofGraph G).offsets[lab[c]!]!)) le2
  have hf4 : Frame m2 le3 G bv vo bd dofs be eo cbv cvo cbd cdofs cbe ceo lab bl lofs bW :=
    hf3.temps fun x _ hx => temps_gso _ _ (fun h => hx (by subst h; decide))
  -- if (wt)
  wp_step; wp_step
  apply wp_if_eval
  rw [show Exec.evalExpr sge empty_env le3 m2 (.Etempvar id.wt (tptr tint)) = some Vnullptr from hf4.hwt]
  simp only [typeof, cop, Vnullptr]
  simp (config := {decide := true}) only []
  have hlo : (Graph.ofGraph G).offsets[lab[c]!]! ≤ (Graph.ofGraph G).offsets[lab[c]! + 1]! :=
    offsets_le G (Nat.le_succ lab[c]!) (show lab[c]! + 1 ≤ n by omega)
  have hhi : (Graph.ofGraph G).offsets[lab[c]! + 1]! ≤ G.neighbors.size := offsets_last G (show lab[c]! + 1 ≤ n by omega)
  have hdeg : (Graph.ofGraph G).degree lab[c]! = (Graph.ofGraph G).offsets[lab[c]! + 1]! - (Graph.ofGraph G).offsets[lab[c]!]! := rfl
  refine wp_copy (D := (Graph.ofGraph G).degree lab[c]!) hf4.hce hce2 hf4.he hf4.earr (temps_gss _ _ _)
    (by rw [temps_gso _ _ (by decide)]; exact temps_gss _ _ _)
    (by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hk)
    (by omega) hKD hN hf4.wptr hf4.warr hn31 ⟨hs3.2.2.1, hs3.2.2.2.2.2, hs3.2.2.2.2.1⟩ ?_
  intro le5 m5 ev' hce5 hlow hrow hk5 hu5 hkp5 hg5 ho5
  refine hQ le5 m5 ev' (hcv2.unch hu5 (fun h => hcc.2.1 h)) (hcd2.unch hu5 (fun h => hcc.2.2 h)) hce5
    hlow hrow hk5 ?_ (fun z h => hg5 _ (hg2 _ (hg1 _ h))) ?_
  · exact ((hu1.mono fun z hz => .inl hz).trans (hu2.mono fun z hz => .inr (.inl hz))).trans
      (hu5.mono fun z hz => .inr (.inr hz))
  · intro x hx
    simp only [RowLocal, not_or] at hx
    rw [ho5 x hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2, temps_gso _ _ hx.2.2.1, temps_gso _ _ hx.2.1,
      temps_gso _ _ hx.1]

end NautyVerified.Proofs.Sparse.Updatecan

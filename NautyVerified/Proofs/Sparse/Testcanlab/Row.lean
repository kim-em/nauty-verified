import NautyVerified.Proofs.Sparse.Testcanlab.Parts

/-!
# One row of `testcanlab_sg`

`wp_row`: row `c` either ends normally with `rowCode … c = none`, or writes
`*samerows = c` and returns `rowCode … c`.
-/

namespace NautyVerified.Proofs.Sparse.Testcanlab

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat mat cast_l_i)
open Hex.GraphIso.Nauty.Sparse (Graph Rows inverse)

variable {xi : ExternalCalls}

/-- The temporaries a row changes. -/
def RowLocal (x : ident) : Prop :=
  x = id.vi ∨ x = id.di ∨ x = id.vli ∨ x = id.dli ∨ x = id.t1 ∨ x = id.ij ∨ x = id.mina ∨
    x = id.j ∨ x = id.k ∨ x = id.t2

instance (x : ident) : Decidable (RowLocal x) := by unfold RowLocal; infer_instance

/-- What the loop over rows reads. -/
structure Frame {n : Nat} (m : mem) (le : temp_env) (G : Hex.SparseGraph n) (bv : block) (vo : ptrofs)
    (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (R : Rows n) (cbv : block) (cvo : ptrofs)
    (cbd : block) (cdofs : ptrofs) (cbe : block) (ceo : ptrofs) (vv dv ev : Nat → val)
    (lab : Array Nat) (bl : block) (lofs : ptrofs) (bs : block) (so : ptrofs) (svals : Nat → val)
    (bW : block) : Prop where
  hv : PTree.get id.v le = some (.Vptr bv vo)
  hd : PTree.get id.d le = some (.Vptr bd dofs)
  he : PTree.get id.e le = some (.Vptr be eo)
  hcv : PTree.get id.cv le = some (.Vptr cbv cvo)
  hcd : PTree.get id.cd le = some (.Vptr cbd cdofs)
  hce : PTree.get id.ce le = some (cePtr R.neighbors.size cbe ceo)
  hlab : PTree.get id.lab le = some (.Vptr bl lofs)
  hsr : PTree.get id.samerows le = some (.Vptr bs so)
  hn : PTree.get id.n le = some (.Vint (ir n))
  varr : ArrayAt m .Mint64 bv (intOfZ (Ptrofs.unsigned vo)) (vVals G) n
  darr : ArrayAt m .Mint32 bd (intOfZ (Ptrofs.unsigned dofs)) (dVals G) n
  earr : ArrayAt m .Mint32 be (intOfZ (Ptrofs.unsigned eo)) (eVals G) G.neighbors.size
  cvarr : ArrayAt m .Mint64 cbv (intOfZ (Ptrofs.unsigned cvo)) vv n
  cdarr : ArrayAt m .Mint32 cbd (intOfZ (Ptrofs.unsigned cdofs)) dv n
  cearr : ArrayAt m .Mint32 cbe (intOfZ (Ptrofs.unsigned ceo)) ev R.neighbors.size
  rows : CanonRows R n vv dv ev
  larr : ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n
  hls : ∀ j < n, lab[j]! < n
  sarr : ArrayAt m .Mint32 bs (intOfZ (Ptrofs.unsigned so)) svals 1
  wptr : Mem.load .Mint64 m Block.work1 (zOfInt 0) = some (.Vptr bW Ptrofs.zero)
  warr : ArrayAt m .Mint32 bW 0 (fun p => .Vint (ir (((inverse n lab)[p]! : Nat) : Int))) n
  invlt : ∀ p : Nat, (inverse n lab)[p]! < n
  n31 : n < 2147483648

/-- The blocks a frame reads. -/
def FrameB (bv bd be cbv cbd cbe bl bs bW : block) (z : block) : Prop :=
  z = bv ∨ z = bd ∨ z = be ∨ z = cbv ∨ z = cbd ∨ z = cbe ∨ z = bl ∨ z = bs ∨ z = bW ∨ z = Block.work1

section
variable {n : Nat} {m m' : mem} {le le' : temp_env} {G : Hex.SparseGraph n} {bv : block} {vo : ptrofs}
    {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {R : Rows n} {cbv : block} {cvo : ptrofs}
    {cbd : block} {cdofs : ptrofs} {cbe : block} {ceo : ptrofs} {vv dv ev : Nat → val}
    {lab : Array Nat} {bl : block} {lofs : ptrofs} {bs : block} {so : ptrofs} {svals : Nat → val}
    {bW : block}

theorem Frame.temps
    (h : Frame m le G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW)
    (hle : ∀ x, x ≠ id.i → ¬ RowLocal x → PTree.get x le' = PTree.get x le) :
    Frame m le' G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW :=
  { h with
    hv := by rw [hle _ (by decide) (by decide)]; exact h.hv
    hd := by rw [hle _ (by decide) (by decide)]; exact h.hd
    he := by rw [hle _ (by decide) (by decide)]; exact h.he
    hcv := by rw [hle _ (by decide) (by decide)]; exact h.hcv
    hcd := by rw [hle _ (by decide) (by decide)]; exact h.hcd
    hce := by rw [hle _ (by decide) (by decide)]; exact h.hce
    hlab := by rw [hle _ (by decide) (by decide)]; exact h.hlab
    hsr := by rw [hle _ (by decide) (by decide)]; exact h.hsr
    hn := by rw [hle _ (by decide) (by decide)]; exact h.hn }

theorem Frame.mem
    (h : Frame m le G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW)
    {S : block → Prop} (hu : Unch m m' S) (hs : ∀ z, FrameB bv bd be cbv cbd cbe bl bs bW z → ¬ S z) :
    Frame m' le G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW :=
  { h with
    varr := h.varr.unch hu (hs _ (.inl rfl))
    darr := h.darr.unch hu (hs _ (.inr (.inl rfl)))
    earr := h.earr.unch hu (hs _ (.inr (.inr (.inl rfl))))
    cvarr := h.cvarr.unch hu (hs _ (.inr (.inr (.inr (.inl rfl)))))
    cdarr := h.cdarr.unch hu (hs _ (.inr (.inr (.inr (.inr (.inl rfl))))))
    cearr := h.cearr.unch hu (hs _ (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
    larr := h.larr.unch hu (hs _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
    sarr := h.sarr.unch hu (hs _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))))
    wptr := by rw [hu.load _ _ _ (hs _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))))]
               exact h.wptr
    warr := h.warr.unch hu (hs _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))))) }
end

theorem ne_of_frame {bv bd be cbv cbd cbe bl bs bW : block} {S : block → Prop}
    (h : ∀ z, FrameB bv bd be cbv cbd cbe bl bs bW z → ¬ S z) {z : block}
    (hz : FrameB bv bd be cbv cbd cbe bl bs bW z) : ¬ S z := h z hz

/-- One row. -/
theorem wp_row {n : Nat} {Q : Post} {m : mem} {le : temp_env} {G : Hex.SparseGraph n} {bv : block}
    {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs} {R : Rows n} {cbv : block}
    {cvo : ptrofs} {cbd : block} {cdofs : ptrofs} {cbe : block} {ceo : ptrofs} {vv dv ev : Nat → val}
    {lab : Array Nat} {bl : block} {lofs : ptrofs} {bs : block} {so : ptrofs} {svals : Nat → val}
    {bW : block} {cap : Nat} {b : block} {st : Nat} {marks : Nat → Int} {c : Nat}
    (hf : Frame m le G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW)
    (hi : PTree.get id.i le = some (.Vint (ir c))) (hc : c < n)
    (hM : MarksAt m cap b st marks) (hnc : n ≤ cap)
    (hsep : ∀ z, FrameB bv bd be cbv cbd cbe bl bs bW z → (0 < cap → z ≠ b) ∧ z ≠ Block.vmark1Val ∧
      z ≠ Block.vmark1 ∧ z ≠ Block.vmark1Sz)
    (hbsd : bs ≠ cbe ∧ bs ≠ be ∧ bs ≠ bW ∧ bs ≠ Block.work1)
    (hQn : rowCode (Graph.ofGraph G) R lab c = none → ∀ le' m' st' marks',
      MarksAt m' cap b st' marks' → Unch m m' (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b)) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, ¬ RowLocal x → PTree.get x le' = PTree.get x le) → Q.normal E0 empty_env le' m')
    (hQr : ∀ r, rowCode (Graph.ofGraph G) R lab c = some r → ∀ m' st' marks',
      MarksAt m' cap b st' marks' →
      ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so)) (fun _ => .Vint (ir c)) 1 →
      Alloc.Keep m m' bs →
      Unch m m' (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b) ∨ z = bs) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.ret E0 (.Vint (ir r)) m') :
    Wp xi sge F row Q empty_env le m := by
  let g := Graph.ofGraph G
  have hn31 := hf.n31
  have hrows := hf.rows
  have hnd := hrows.nde31
  have hlc := hf.hls c hc
  have hoc := hrows.mono c hc
  have hend := hrows.end_le hc
  have hbase := hrows.base_le
  have hRd : R.degree c = R.offsets[c + 1]! - R.offsets[c]! := rfl
  have hgd : g.degree lab[c]! ≤ n := degree_lt G hlc
  -- vi = cv[i]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tidx (ge := sge) hf.cvarr hn31 hf.hcv rfl rfl (tv id.i) c hc hi rfl, hrows.v c hc]
  let le1 := PTree.set id.vi (.Vlong (lr R.offsets[c]!)) le
  have hf1 : Frame m le1 G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW :=
    hf.temps fun x _ hx => temps_gso _ _ (fun h => hx (by subst h; decide))
  have hi1 : PTree.get id.i le1 = some (.Vint (ir c)) := by rw [temps_gso _ _ (by decide)]; exact hi
  -- di = cd[i]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tidx (ge := sge) hf1.cdarr hn31 hf1.hcd rfl rfl (tv id.i) c hc hi1 rfl, hrows.d c hc]
  let le2 := PTree.set id.di (.Vint (ir (R.degree c))) le1
  have hf2 : Frame m le2 G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW :=
    hf1.temps fun x _ hx => temps_gso _ _ (fun h => hx (by subst h; decide))
  have hi2 : PTree.get id.i le2 = some (.Vint (ir c)) := by rw [temps_gso _ _ (by decide)]; exact hi1
  -- vli = v[lab[i]]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tidx (ge := sge) hf2.varr hn31 hf2.hv rfl rfl _ lab[c]! hlc
    (eval_tidx (ge := sge) hf2.larr hn31 hf2.hlab rfl rfl (tv id.i) c hc hi2 rfl) rfl]
  simp only [vVals]
  let le3 := PTree.set id.vli (.Vlong (lr g.offsets[lab[c]!]!)) le2
  have hf3 : Frame m le3 G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW :=
    hf2.temps fun x _ hx => temps_gso _ _ (fun h => hx (by subst h; decide))
  have hi3 : PTree.get id.i le3 = some (.Vint (ir c)) := by rw [temps_gso _ _ (by decide)]; exact hi2
  -- dli = d[lab[i]]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_tidx (ge := sge) hf3.darr hn31 hf3.hd rfl rfl _ lab[c]! hlc
    (eval_tidx (ge := sge) hf3.larr hn31 hf3.hlab rfl rfl (tv id.i) c hc hi3 rfl) rfl]
  simp only [dVals]
  let le4 := PTree.set id.dli (.Vint (ir (g.degree lab[c]!))) le3
  have hf4 : Frame m le4 G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW :=
    hf3.temps fun x _ hx => temps_gso _ _ (fun h => hx (by subst h; decide))
  have hi4 : PTree.get id.i le4 = some (.Vint (ir c)) := by rw [temps_gso _ _ (by decide)]; exact hi3
  have hdi4 : PTree.get id.di le4 = some (.Vint (ir (R.degree c))) := by
    simp (config := {decide := true}) only [le4, le3, le2, temps_gso, temps_gss]
  have hdli4 : PTree.get id.dli le4 = some (.Vint (ir (g.degree lab[c]!))) := temps_gss _ _ _
  have hRd31 : R.degree c < 2147483648 := by omega
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le4 m (tv id.di) = _ from hdi4,
    show Exec.evalExpr sge empty_env le4 m (tv id.dli) = _ from hdli4]
  simp only [typeof, cop]
  rw [ir_eq (a := (R.degree c : Int)) (b := (g.degree lab[c]! : Int)) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩]
  by_cases hdeg : R.degree c = g.degree lab[c]!
  · rw [show decide ((R.degree c : Int) = g.degree lab[c]!) = true from decide_eq_true (by rw [hdeg])]
    simp (config := {decide := true}) only [cop, ite_false]
    apply wp_skip
    have hdD : R.degree c = g.offsets[lab[c]! + 1]! - g.offsets[lab[c]!]! := hdeg
    have hlo : g.offsets[lab[c]!]! ≤ g.offsets[lab[c]! + 1]! :=
      offsets_le G (Nat.le_succ lab[c]!) (show lab[c]! + 1 ≤ n by omega)
    have hhi : g.offsets[lab[c]! + 1]! ≤ G.neighbors.size := offsets_last G (show lab[c]! + 1 ≤ n by omega)
    have hcand : cands G lab g.offsets[lab[c]!]! (R.degree c) = candidate g lab c := by
      rw [hdD]; rfl
    have hsepS : ∀ z, FrameB bv bd be cbv cbd cbe bl bs bW z →
        ¬ (z = Block.vmark1Val ∨ (0 < cap ∧ z = b)) := fun z hz h => by
      rcases h with h | ⟨h0, h⟩
      · exact (hsep z hz).2.1 h
      · exact (hsep z hz).1 h0 h
    have hsepb : 0 < cap → b ≠ cbe ∧ b ≠ be ∧ b ≠ bW ∧ b ≠ Block.work1 := fun h0 =>
      ⟨fun h => (hsep cbe (by simp [FrameB])).1 h0 h.symm, fun h => (hsep be (by simp [FrameB])).1 h0 h.symm,
       fun h => (hsep bW (by simp [FrameB])).1 h0 h.symm,
       fun h => (hsep Block.work1 (by simp [FrameB])).1 h0 h.symm⟩
    wp_step
    refine wp_resetmarks1 (le := le4) hM ?_
    intro le6 m6 st6 marks6 hM6 hbelow hu6 hg6 ho6
    have hf6 := (hf4.mem hu6 hsepS).temps fun x _ hx =>
      ho6 x (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide))
    have hget6 : ∀ x, x ≠ id.t1 → x ≠ id.ij → PTree.get x le6 = PTree.get x le4 := ho6
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [show Exec.evalExpr sge empty_env le6 m6 (tv id.n) = _ from hf6.hn]
    let le7 := PTree.set id.mina (.Vint (ir n)) le6
    have hf7 : Frame m6 le7 G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so svals bW :=
      hf6.temps fun x _ hx => temps_gso _ _ (fun h => hx (by subst h; decide))
    have hL : LoopCtx m6 le7 G be eo R cbe ceo ev bW lab (R.degree c) R.offsets[c]! g.offsets[lab[c]!]! :=
      { hce := hf7.hce, he := hf7.he
        hdi := by rw [temps_gso _ _ (by decide), hget6 _ (by decide) (by decide)]; exact hdi4
        hvi := by
          rw [temps_gso _ _ (by decide), hget6 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [le4, le3, le2, le1, temps_gso, temps_gss]
        hvli := by
          rw [temps_gso _ _ (by decide), hget6 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [le4, le3, temps_gso, temps_gss]
        hn := hf7.hn, cearr := hf7.cearr
        cev := fun j hj => hrows.e _ (by rw [hRd] at hj; omega)
        csmall := fun j hj => hrows.small _ (by rw [hRd] at hj; omega)
        hVD := by rw [hRd]; omega
        earr := hf7.earr
        hVL := by rw [hdD]; omega
        wptr := hf7.wptr, warr := hf7.warr, invlt := hf7.invlt, n31 := hn31, nde31 := hnd }
    wp_step
    refine wp_markLoop hL hM6 hnc hbelow hsepb ?_
    intro le8 m8 marks8 hM8 hhit hu8 hg8 ho8
    have hL8 : LoopCtx m8 le8 G be eo R cbe ceo ev bW lab (R.degree c) R.offsets[c]! g.offsets[lab[c]!]! :=
      (hL.temps fun x hx => ho8 x (fun h => hx (.inl h))).mem hu8
        (fun ⟨h0, h⟩ => (hsepb h0).1 h.symm) (fun ⟨h0, h⟩ => (hsepb h0).2.1 h.symm)
        (fun ⟨h0, h⟩ => (hsepb h0).2.2.2 h.symm) (fun ⟨h0, h⟩ => (hsepb h0).2.2.1 h.symm)
    have hmk : ∀ x < n, marks8 x = st6 ↔ decide (x ∈ stored R c) = true := by
      intro x hx
      rw [hhit x (by omega), decide_eq_true_iff, mem_stored]
      constructor
      · rintro ⟨j, hj, he⟩; exact ⟨_, ⟨Nat.le_add_right _ _, by rw [hRd] at hj; omega⟩, he⟩
      · rintro ⟨a, ⟨h1, h2⟩, he⟩
        exact ⟨a - R.offsets[c]!, by rw [hRd]; omega, by rw [Nat.add_sub_cancel' h1]; exact he⟩
    have hmina8 : PTree.get id.mina le8 = some (.Vint (ir n)) := by
      rw [ho8 _ (by decide)]; exact temps_gss _ _ _
    wp_step
    refine wp_unmarkLoop hL8 hM8 hnc hmk hmina8 hsepb ?_
    intro le9 m9 marks9 hM9 hrel hmn hu9 hg9 ho9
    rw [hcand] at hrel hmn
    have hpass : pass g R lab c = unmark (candidate g lab c) (fun k => decide (k ∈ stored R c)) n := rfl
    have hUle : (pass g R lab c).2 ≤ n := unmark_le _ _ _
    have hL9 := (hL8.temps fun x hx => by
        simp only [LoopLocal, not_or] at hx
        exact ho9 x hx.1 hx.2.1 hx.2.2.1).mem hu9
        (fun ⟨h0, h⟩ => (hsepb h0).1 h.symm) (fun ⟨h0, h⟩ => (hsepb h0).2.1 h.symm)
        (fun ⟨h0, h⟩ => (hsepb h0).2.2.2 h.symm) (fun ⟨h0, h⟩ => (hsepb h0).2.2.1 h.symm)
    have hu : Unch m m9 (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b)) :=
      (hu6.trans (hu8.mono fun z hz => .inr hz)).trans (hu9.mono fun z hz => .inr hz)
    have hg : ∀ z, Mem.valid_block m z → Mem.valid_block m9 z := fun z h => hg9 _ (hg8 _ (hg6 _ h))
    have hle : ∀ x, ¬ RowLocal x → PTree.get x le9 = PTree.get x le := by
      intro x hx
      simp only [RowLocal, not_or] at hx
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hx
      rw [ho9 x h8 h9 h7, ho8 x h8, temps_gso _ _ h7, hget6 x h5 h6]
      simp only [le4, le3, le2, le1]
      rw [temps_gso _ _ h4, temps_gso _ _ h3, temps_gso _ _ h2, temps_gso _ _ h1]
    have hf9 := (hf7.mem (hu8.trans (hu9.mono fun z hz => hz)) fun z hz ⟨h0, h⟩ => (hsep z hz).1 h0 h).temps
      (le' := le9) fun x _ hx => by
        simp only [RowLocal, not_or] at hx
        exact ho9 x hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 ▸
          ho8 x hx.2.2.2.2.2.2.2.1
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le9 m9 (tv id.mina) = _ from hmn,
      show Exec.evalExpr sge empty_env le9 m9 (tv id.n) = _ from hf9.hn]
    simp only [typeof, cop]
    rw [ir_eq (a := ((pass g R lab c).2 : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases heq : (pass g R lab c).2 = n
    · rw [show decide (((pass g R lab c).2 : Int) = n) = true from decide_eq_true (by rw [heq])]
      simp (config := {decide := true}) only [cop, ite_false]
      apply wp_skip
      exact hQn (rowCode_none hdeg heq) le9 m9 st6 marks9 hM9 hu hg hle
    · rw [show decide (((pass g R lab c).2 : Int) = n) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [cop, ite_true]
      have hi9 : PTree.get id.i le9 = some (.Vint (ir c)) := by
        rw [hle _ (by decide)]; exact hi
      have hbs := hsep bs (by simp [FrameB])
      wp_step
      refine wp_setSame hf9.hsr hi9 hf9.sarr ?_
      intro m10 harr10 hu10 hk10 hg10
      have hM10 := hM9.unch hu10 (fun h => hbs.2.2.1 h.symm) (fun h => hbs.2.2.2 h.symm)
        (fun h => hbs.2.1 h.symm) (fun h0 h => hbs.1 h0 h.symm)
      have hU10 : Unch m m10 (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b) ∨ z = bs) :=
        (hu.mono fun z hz => by rcases hz with h | h; exact .inl h; exact .inr (.inl h)).trans
          (hu10.mono fun z hz => .inr (.inr hz))
      have hg' : ∀ z, Mem.valid_block m z → Mem.valid_block m10 z := fun z h => hg10 _ (hg _ h)
      have hK10 : Alloc.Keep m m10 bs := (Alloc.Keep.unch hu (by
        rintro (h | ⟨h0, h⟩)
        · exact hbs.2.1 h
        · exact hbs.1 h0 h)).trans hk10
      have hL10 := hL9.mem hu10 (fun h => hbsd.1 h.symm) (fun h => hbsd.2.1 h.symm)
        (fun h => hbsd.2.2.2 h.symm) (fun h => hbsd.2.2.1 h.symm)
      wp_step
      refine wp_checkLoop hL10 hM10 hnc hUle (by rw [hpass]; exact hmn) ?_ ?_
      · intro hnone le11 _
        refine wp_ret_const (c := 1) (hQr 1 ?_ m10 st6 marks9 hM10 harr10 hK10 hU10 hg')
        refine rowCode_gt hdeg heq fun e h1 h2 hm => ?_
        have := hnone (e - R.offsets[c]!) (by rw [hRd]; omega)
        rw [Nat.add_sub_cancel' h1] at this
        exact this ((hrel _ (hrows.small e (by omega))).2 (by rw [hpass] at hm; exact hm))
      · rintro ⟨j, hj, hm, hlt⟩
        refine hQr (-1) ?_ m10 st6 marks9 hM10 harr10 hK10 hU10 hg'
        exact rowCode_lt hdeg heq (e := R.offsets[c]! + j) ⟨Nat.le_add_right _ _, by rw [hRd] at hj; omega⟩
          ((hrel _ (hrows.small _ (by rw [hRd] at hj; omega))).1 hm) hlt
  · rw [show decide ((R.degree c : Int) = g.degree lab[c]!) = false from decide_eq_false (by omega)]
    simp (config := {decide := true}) only [cop, ite_true]
    have hcode : rowCode g R lab c = some (if R.degree c < g.degree lab[c]! then -1 else 1) := by
      simp [rowCode, hdeg]
    have hbs := hsep bs (by simp [FrameB])
    wp_step
    refine wp_setSame hf4.hsr hi4 hf4.sarr ?_
    intro m1 harr1 hu1 hk1 hg1
    have hM1 := hM.unch hu1 (fun h => hbs.2.2.1 h.symm) (fun h => hbs.2.2.2 h.symm)
      (fun h => hbs.2.1 h.symm) (fun h0 h => hbs.1 h0 h.symm)
    have hU1 : Unch m m1 (fun z => z = Block.vmark1Val ∨ (0 < cap ∧ z = b) ∨ z = bs) :=
      hu1.mono fun z hz => .inr (.inr hz)
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le4 m1 (tv id.di) = _ from hdi4,
      show Exec.evalExpr sge empty_env le4 m1 (tv id.dli) = _ from hdli4]
    simp only [typeof, cop]
    rw [ir_lt (a := (R.degree c : Int)) (b := (g.degree lab[c]! : Int)) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩]
    by_cases hlt : R.degree c < g.degree lab[c]!
    · rw [show decide ((R.degree c : Int) < g.degree lab[c]!) = true from decide_eq_true (by omega)]
      simp (config := {decide := true}) only [cop, ite_true]
      refine wp_ret_neg (hQr _ ?_ m1 st marks hM1 harr1 hk1 hU1 hg1)
      rw [hcode]; simp [hlt]
    · rw [show decide ((R.degree c : Int) < g.degree lab[c]!) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [cop, ite_false]
      apply wp_skip
      refine wp_ret_const (c := 1) (hQr _ ?_ m1 st marks hM1 harr1 hk1 hU1 hg1)
      rw [hcode]; simp [hlt]
end NautyVerified.Proofs.Sparse.Testcanlab

import NautyVerified.Proofs.Sparse.Testcanlab.Row
import NautyVerified.Proofs.Sparse.Prep
import NautyVerified.Proofs.Alloc.Dyn3

/-!
# `testcanlab_sg` meets its specification

`testcanlabSpec`: called on a sparse graph `G` (`SparseGraphAt`), the
canonical store holding all `n` rows of `R` (`CanonAt … R n …`, whose
neighbours are below `n`: HexGraphIso's `Sparse.testcanlab` tolerates
out-of-range entries, the C would index `vmark1` out of bounds), a
permutation `lab` and a cell `*samerows`, nausparse.c's `testcanlab_sg`
returns the first component of HexGraphIso's
`Sparse.testcanlab (ofGraph G) R lab` and stores the second in `*samerows`.
It uses `work1` as `INVLAB` (holding `Sparse.inverse n lab`, reallocated by
`DYNALLOC1`) and the marks (`MarksAt`, through `preparemarks1`); nothing
else changes.
-/

namespace NautyVerified.Proofs.Sparse.Testcanlab

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Source
open NautyVerified.Proofs.Sparse NautyVerified.Program
open NautyVerified.Proofs.Sparse.Isautom (sk tv tl iat lat mat cast_l_i)
open Hex.GraphIso.Nauty.Sparse (Graph Rows inverse inverse_lt)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls}

/-- The caller's blocks. -/
def Ext (bsg bv bd be bc cbv cbd cbe bl bs : block) (z : block) : Prop :=
  z = bsg ∨ z = bv ∨ z = bd ∨ z = be ∨ z = bc ∨ z = cbv ∨ z = cbd ∨ z = cbe ∨ z = bl ∨ z = bs

/-- The specification of `testcanlab_sg`. -/
def testcanlabSpec {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs) (bv : block)
    (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (R : Rows n) (bc : block)
    (cofs : ptrofs) (cbv : block) (cvo : ptrofs) (cbd : block) (cdofs : ptrofs) (cbe : block)
    (ceo : ptrofs) (lab : Array Nat) (bl : block) (lofs : ptrofs) (bs : block) (so : ptrofs)
    (svals : Nat → val) (M capW : Nat) (bW : block) (cap : Nat) (b : block) (st : Nat)
    (marks : Nat → Int) : FunSpec where
  pre args m := args = [.Vptr bsg sofs, .Vptr bc cofs, .Vptr bl lofs, .Vptr bs so, .Vint (ir M),
      .Vint (ir n)] ∧
    SparseGraphAt m bsg sofs G bv vo bd dofs be eo ∧ CanonAt m bc cofs R n cbv cvo cbd cdofs cbe ceo ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧ lab.size = n ∧
    (∀ j < n, lab[j]! < n) ∧ (∀ a b, a < n → b < n → lab[a]! = lab[b]! → a = b) ∧
    (∀ p < n, ∃ j < n, lab[j]! = p) ∧
    ArrayAt m .Mint32 bs (intOfZ (Ptrofs.unsigned so)) svals 1 ∧
    Alloc.DynAt m Block.work1 Block.work1Sz 4 capW bW ∧ MarksAt m cap b st marks ∧
    0 < n ∧ n < 2147483648 ∧
    (∀ z, Ext bsg bv bd be bc cbv cbd cbe bl bs z → Mem.valid_block m z ∧ z ≠ Block.vmark1 ∧
      z ≠ Block.vmark1Sz ∧ z ≠ Block.vmark1Val ∧ z ≠ Block.work1 ∧ z ≠ Block.work1Sz ∧
      (0 < cap → z ≠ b) ∧ (0 < capW → z ≠ bW)) ∧
    bs ≠ cbe ∧ bs ≠ be ∧
    (0 < capW → bW ≠ Block.vmark1 ∧ bW ≠ Block.vmark1Sz ∧ bW ≠ Block.vmark1Val ∧ (0 < cap → bW ≠ b)) ∧
    (0 < cap → b ≠ Block.work1 ∧ b ≠ Block.work1Sz)
  post _ m t v m' := t = E0 ∧
    v = .Vint (ir (Hex.GraphIso.Nauty.Sparse.testcanlab (Graph.ofGraph G) R lab).1) ∧
    ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so))
      (fun _ => .Vint (ir ((Hex.GraphIso.Nauty.Sparse.testcanlab (Graph.ofGraph G) R lab).2 : Int))) 1 ∧
    ∃ capW' bW' cap' b' st' marks', Alloc.DynAt m' Block.work1 Block.work1Sz 4 capW' bW' ∧ n ≤ capW' ∧
      ((capW' = capW ∧ bW' = bW) ∨ ¬ Mem.valid_block m bW') ∧
      MarksAt m' cap' b' st' marks' ∧ n ≤ cap' ∧ ((cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') ∧
      Unch m m' (fun z => z = bs ∨ z = Block.work1 ∨ z = Block.work1Sz ∨ (0 < capW ∧ z = bW) ∨
        (¬ Mem.valid_block m bW' ∧ z = bW') ∨ MarksS m cap b b' z) ∧
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z)

def entryTemps (bsg : block) (sofs : ptrofs) (bc : block) (cofs : ptrofs) (bl : block) (lofs : ptrofs)
    (bs : block) (so : ptrofs) (M n : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.samerows (.Vptr bs so) (PTree.set id.lab (.Vptr bl lofs)
      (PTree.set id.canong (.Vptr bc cofs) (PTree.set id.g (.Vptr bsg sofs)
        (create_undef_temps F.fn_temps))))))

/-- `SG_VDE(p, v, d, e)`. -/
theorem wp_vde {Q : Post} {le : temp_env} {m : mem} {p v d e : ident} {bsg : block} {sofs : ptrofs}
    {bv : block} {vo : ptrofs} {bd : block} {dofs : ptrofs} {be : block} {eo : ptrofs}
    (hp : PTree.get p le = some (.Vptr bsg sofs)) (hpv : p ≠ v) (hpd : p ≠ d)
    (hv : Mem.load .Mint64 m bsg (fofs sofs 8) = some (.Vptr bv vo))
    (hd : Mem.load .Mint64 m bsg (fofs sofs 24) = some (.Vptr bd dofs))
    (he : Mem.load .Mint64 m bsg (fofs sofs 32) = some (.Vptr be eo))
    (hQ : Q.normal E0 empty_env
      (PTree.set e (.Vptr be eo) (PTree.set d (.Vptr bd dofs) (PTree.set v (.Vptr bv vo) le))) m) :
    Wp xi sge F (vde p v d e) Q empty_env le m := by
  let le1 := PTree.set e (.Vptr be eo) (PTree.set d (.Vptr bd dofs) (PTree.set v (.Vptr bv vo) le))
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
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_sgField (by rw [temps_gso _ _ hpd, temps_gso _ _ hpv]; exact hp) (lval_e _ _) rfl he]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro - t e' le' m' ⟨rfl, rfl, rfl, hm⟩
    subst m'
    wp_step; wp_step
    apply wp_break
    simpa only [E0_append] using hQ

theorem not_marksS {m : mem} {cap : Nat} {b b' z : block} (hv : Mem.valid_block m z)
    (h1 : z ≠ Block.vmark1) (h2 : z ≠ Block.vmark1Sz) (h3 : z ≠ Block.vmark1Val) (h4 : 0 < cap → z ≠ b) :
    ¬ MarksS m cap b b' z := by
  rintro (h | h | h | ⟨hc, h⟩ | ⟨hb, rfl⟩)
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 hc h
  · exact hb hv

theorem type_preparemarks1 :
    type_of_fundef (.Internal sparse.fn.«nausparse:preparemarks1») = tfun [tulong] .Tvoid := rfl

theorem testcanlab_satisfies {n : Nat} (G : Hex.SparseGraph n) (bsg : block) (sofs : ptrofs)
    (bv : block) (vo : ptrofs) (bd : block) (dofs : ptrofs) (be : block) (eo : ptrofs) (R : Rows n)
    (bc : block) (cofs : ptrofs) (cbv : block) (cvo : ptrofs) (cbd : block) (cdofs : ptrofs)
    (cbe : block) (ceo : ptrofs) (lab : Array Nat) (bl : block) (lofs : ptrofs) (bs : block)
    (so : ptrofs) (svals : Nat → val) (M capW : Nat) (bW : block) (cap : Nat) (b : block) (st : Nat)
    (marks : Nat → Int) :
    Satisfies xi sge (.Internal F) (testcanlabSpec G bsg sofs bv vo bd dofs be eo R bc cofs cbv cvo
      cbd cdofs cbe ceo lab bl lofs bs so svals M capW bW cap b st marks) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bsg sofs bc cofs bl lofs bs so M n ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bsg sofs bc cofs bl lofs bs so M n, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩,
      rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hgr, hca, hlarr, hlsz, hls, hinj, hsurj, hsarr, hDW, hM, hn0, hn31, hsep, hbsc,
      hbse, hsepW, hsepM⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [sparse.fn.testcanlab_sg.fn_body_eq, body_eq]
    obtain ⟨vv, dv, ev, hcvarr, hcdarr, hcearr, hrows⟩ := hca.rows
    let le0 := entryTemps bsg sofs bc cofs bl lofs bs so M n
    wp_step
    refine wp_vde (bsg := bsg) (sofs := sofs)
      (by simp (config := {decide := true}) only [le0, entryTemps, temps_gso, temps_gss])
      (by decide) (by decide) hgr.v hgr.d hgr.e ?_
    wp_step
    refine wp_vde (bsg := bc) (sofs := cofs)
      (by simp (config := {decide := true}) only [le0, entryTemps, temps_gso, temps_gss])
      (by decide) (by decide) hca.v hca.d hca.e ?_
    let leV := PTree.set id.ce (.Vptr cbe ceo) (PTree.set id.cd (.Vptr cbd cdofs)
      (PTree.set id.cv (.Vptr cbv cvo) (PTree.set id.e (.Vptr be eo) (PTree.set id.d (.Vptr bd dofs)
        (PTree.set id.v (.Vptr bv vo) le0)))))
    have hnV : PTree.get id.n leV = some (.Vint (ir n)) := by
      simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss]
    wp_step
    refine Alloc.wp_dynalloc1 (E := NautyEnv.sparse) find_work1Sz find_work1 rfl hDW hnV hn31
      (show 4 * n < 2 ^ 62 by omega) ?_
    intro le1 m1 capW1 bW1 hDW1 hnW hu1 hor1 hg1 ho1
    have hvV : Mem.valid_block m Block.vmark1Val := Alloc.valid_of_access hM.valW
    have hv1 : Mem.valid_block m Block.vmark1 := Alloc.valid_of_access hM.dyn.bpW
    have hvS : Mem.valid_block m Block.vmark1Sz := Alloc.valid_of_access hM.dyn.bsW
    have hvW : Mem.valid_block m Block.work1 := Alloc.valid_of_access hDW.bpW
    have hvWS : Mem.valid_block m Block.work1Sz := Alloc.valid_of_access hDW.bsW
    have hvb : 0 < cap → Mem.valid_block m b := fun h0 => (hM.dyn.mal h0).valid
    have hcW1 : 0 < capW1 := by omega
    have hvbW1 : Mem.valid_block m1 bW1 := (hDW1.mal hcW1).valid
    have hbbW1 : 0 < cap → b ≠ bW1 := fun h0 =>
      Alloc.ne_new hor1 (hvb h0) (fun hw => ((hsepW hw).2.2.2 h0).symm) hcW1
    have hM1 : MarksAt m1 cap b st marks := hM.unch hu1
      (Alloc.not_dynSet hv1 (by decide) (by decide) (fun h0 => (hsepW h0).1.symm))
      (Alloc.not_dynSet hvS (by decide) (by decide) (fun h0 => (hsepW h0).2.1.symm))
      (Alloc.not_dynSet hvV (by decide) (by decide) (fun h0 => (hsepW h0).2.2.1.symm))
      (fun h0 => Alloc.not_dynSet (hvb h0) (hsepM h0).2 (hsepM h0).1
        (fun hw => ((hsepW hw).2.2.2 h0).symm))
    have hnL : PTree.get id.n le1 = some (.Vint (ir n)) := by
      rw [ho1 _ (by decide) (by decide)]; exact hnV
    wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr Block.preparemarks1 Ptrofs.zero) (targs := [tulong]) (tres := .Tvoid)
      (cc := Common.AST.cc_default) _ (prepSpec n cap b st marks) (prep_satisfies _ _ _ _ _) rfl
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
        show PTree.get sparse.id.«nausparse:preparemarks1» (empty_env : env) = none from rfl,
        find_preparemarks1, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
      (by simp only [Exec.evalExprlist, Exec.evalExpr, hnL, typeof, cop,
            cast_int_long_ir (a := n) ⟨by omega, by omega⟩])
      (by simp [Common.Globalenvs.Genv.find_funct, funct_preparemarks1]) type_preparemarks1
      ⟨rfl, hM1, hn31⟩ ?_
    rintro t - m2 ⟨rfl, cap2, b2, st2, marks2, hM2, hnc2, hor2, hu2, hg2⟩
    simp only [set_opttemp, E0_append]
    have hc2 : 0 < cap2 := by omega
    have hbW1M : ¬ MarksS m1 cap b b2 bW1 := not_marksS hvbW1
      (Alloc.ne_new hor1 hv1 (fun h0 => (hsepW h0).1.symm) hcW1).symm
      (Alloc.ne_new hor1 hvS (fun h0 => (hsepW h0).2.1.symm) hcW1).symm
      (Alloc.ne_new hor1 hvV (fun h0 => (hsepW h0).2.2.1.symm) hcW1).symm
      (fun h0 => (hbbW1 h0).symm)
    have hWM : ¬ MarksS m1 cap b b2 Block.work1 := not_marksS (hg1 _ hvW) (by decide) (by decide)
      (by decide) (fun h0 => (hsepM h0).1.symm)
    have hWSM : ¬ MarksS m1 cap b b2 Block.work1Sz := not_marksS (hg1 _ hvWS) (by decide) (by decide)
      (by decide) (fun h0 => (hsepM h0).2.symm)
    have hDW2 : Alloc.DynAt m2 Block.work1 Block.work1Sz 4 capW1 bW1 :=
      hDW1.keep hu2 hWM hWSM (fun _ => Alloc.Keep.unch hu2 hbW1M)
    -- the caller's blocks are untouched
    have hext : ∀ z, Ext bsg bv bd be bc cbv cbd cbe bl bs z →
        ¬ (z = Block.work1Sz ∨ z = Block.work1 ∨ (0 < capW ∧ z = bW) ∨
          (¬ Mem.valid_block m bW1 ∧ z = bW1)) ∧ ¬ MarksS m1 cap b b2 z ∧ z ≠ bW1 ∧
          (0 < cap2 → z ≠ b2) := by
      intro z hz
      obtain ⟨hv, h1, h2, h3, h4, h5, h6, h7⟩ := hsep z hz
      exact ⟨Alloc.not_dynSet hv h5 h4 h7, not_marksS (hg1 _ hv) h1 h2 h3 h6,
        Alloc.ne_new hor1 hv h7 hcW1, fun h0 => Alloc.ne_new hor2 (hg1 _ hv) h6 h0⟩
    have tr : ∀ {z : block} {chunk : memory_chunk} {base : Int} {vals : Nat → val} {k : Nat},
        Ext bsg bv bd be bc cbv cbd cbe bl bs z → ArrayAt m chunk z base vals k →
        ArrayAt m2 chunk z base vals k := fun hz h =>
      (h.unch hu1 (hext _ hz).1).unch hu2 (hext _ hz).2.1
    have eB : ∀ z, z = bl → Ext bsg bv bd be bc cbv cbd cbe bl bs z := by intro z h; simp [Ext, h]
    have hlarr2 := tr (eB bl rfl) hlarr
    have hget1 : ∀ x, x ≠ idOf 703 → x ≠ idOf 704 → PTree.get x le1 = PTree.get x leV := ho1
    obtain ⟨wv, hwarr⟩ := Alloc.malloced_array (hDW2.mal hcW1) .Mint32 4 rfl rfl n (by omega)
    have hblW : bl ≠ bW1 := (hext bl (eB bl rfl)).2.2.1
    wp_step
    refine wp_scatter (bl := bl) (lofs := lofs)
      (by rw [hget1 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss])
      hlarr2 hlsz hls hinj hsurj hnL hn31 (hDW2.ptr hcW1) hwarr hblW (hDW2.bne hcW1).2.symm ?_
    intro le3 m3 hwarr3 hu3 hk3 hg3 ho3
    have hDW3 : Alloc.DynAt m3 Block.work1 Block.work1Sz 4 capW1 bW1 :=
      hDW2.keep hu3 (fun h => (hDW2.bne hcW1).2 h.symm) (fun h => (hDW2.bne hcW1).1 h.symm)
        (fun _ => hk3)
    have hb2W1 : b2 ≠ bW1 := by
      rcases hor2 with ⟨h1, h2⟩ | hnv
      · rw [h2]; exact hbbW1 (by omega)
      · exact fun h => hnv (h ▸ hvbW1)
    have hM3 : MarksAt m3 cap2 b2 st2 marks2 := hM2.unch hu3 (fun h => hbW1M (.inl h.symm))
      (fun h => hbW1M (.inr (.inl h.symm))) (fun h => hbW1M (.inr (.inr (.inl h.symm))))
      (fun _ => hb2W1)
    have hext3 : ∀ z, Ext bsg bv bd be bc cbv cbd cbe bl bs z → ∀ {chunk : memory_chunk} {base : Int}
        {vals : Nat → val} {k : Nat}, ArrayAt m chunk z base vals k → ArrayAt m3 chunk z base vals k :=
      fun z hz _ _ _ _ h => (tr hz h).unch hu3 (hext z hz).2.2.1
    have hget3 : ∀ x, x ≠ id.i → x ≠ idOf 703 → x ≠ idOf 704 → PTree.get x le3 = PTree.get x leV :=
      fun x h1 h2 h3 => by rw [ho3 x h1, hget1 x h2 h3]
    have hf : Frame m3 le3 G bv vo bd dofs be eo R cbv cvo cbd cdofs cbe ceo vv dv ev lab bl lofs bs so
        svals bW1 :=
      { hv := by rw [hget3 _ (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [leV, temps_gso, temps_gss]
        hd := by rw [hget3 _ (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [leV, temps_gso, temps_gss]
        he := by rw [hget3 _ (by decide) (by decide) (by decide)]
                 simp (config := {decide := true}) only [leV, temps_gso, temps_gss]
        hcv := by rw [hget3 _ (by decide) (by decide) (by decide)]
                  simp (config := {decide := true}) only [leV, temps_gso, temps_gss]
        hcd := by rw [hget3 _ (by decide) (by decide) (by decide)]
                  simp (config := {decide := true}) only [leV, temps_gso, temps_gss]
        hce := by rw [hget3 _ (by decide) (by decide) (by decide)]
                  simp (config := {decide := true}) only [leV, temps_gss]
        hlab := by rw [hget3 _ (by decide) (by decide) (by decide)]
                   simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss]
        hsr := by rw [hget3 _ (by decide) (by decide) (by decide)]
                  simp (config := {decide := true}) only [leV, le0, entryTemps, temps_gso, temps_gss]
        hn := by rw [hget3 _ (by decide) (by decide) (by decide)]; exact hnV
        varr := hext3 bv (by simp [Ext]) hgr.varr
        darr := hext3 bd (by simp [Ext]) hgr.darr
        earr := hext3 be (by simp [Ext]) hgr.earr
        cvarr := hext3 cbv (by simp [Ext]) hcvarr
        cdarr := hext3 cbd (by simp [Ext]) hcdarr
        cearr := hext3 cbe (by simp [Ext]) hcearr
        rows := hrows
        larr := hext3 bl (by simp [Ext]) hlarr
        hls := hls
        sarr := hext3 bs (by simp [Ext]) hsarr
        wptr := hDW3.ptr hcW1
        warr := hwarr3
        invlt := inverse_lt hlsz hn0
        n31 := hn31 }
    have hvW1 : Mem.valid_block m1 Block.work1 := hg1 _ hvW
    have hb2W : 0 < cap2 → Block.work1 ≠ b2 := fun h0 =>
      Alloc.ne_new hor2 hvW1 (fun h0' => (hsepM h0').1.symm) h0
    have hsepR : ∀ z, FrameB bv bd be cbv cbd cbe bl bs bW1 z → (0 < cap2 → z ≠ b2) ∧
        z ≠ Block.vmark1Val ∧ z ≠ Block.vmark1 ∧ z ≠ Block.vmark1Sz := by
      have hE : ∀ z, Ext bsg bv bd be bc cbv cbd cbe bl bs z → (0 < cap2 → z ≠ b2) ∧
          z ≠ Block.vmark1Val ∧ z ≠ Block.vmark1 ∧ z ≠ Block.vmark1Sz := fun z hz =>
        ⟨(hext z hz).2.2.2, (hsep z hz).2.2.2.1, (hsep z hz).2.1, (hsep z hz).2.2.1⟩
      intro z hz
      rcases hz with h | h | h | h | h | h | h | h | h | h
      · exact hE z (by simp [Ext, h])
      · exact hE z (by simp [Ext, h])
      · exact hE z (by simp [Ext, h])
      · exact hE z (by simp [Ext, h])
      · exact hE z (by simp [Ext, h])
      · exact hE z (by simp [Ext, h])
      · exact hE z (by simp [Ext, h])
      · exact hE z (by simp [Ext, h])
      · rw [h]
        exact ⟨fun _ => hb2W1.symm, fun h' => hbW1M (.inr (.inr (.inl h'))), fun h' => hbW1M (.inl h'),
          fun h' => hbW1M (.inr (.inl h'))⟩
      · rw [h]; exact ⟨hb2W, by decide, by decide, by decide⟩
    have hbsd : bs ≠ cbe ∧ bs ≠ be ∧ bs ≠ bW1 ∧ bs ≠ Block.work1 :=
      ⟨hbsc, hbse, (hext bs (by simp [Ext])).2.2.1, (hsep bs (by simp [Ext])).2.2.2.2.1⟩
    have hR : ∀ i < n, ∀ k ∈ stored R i, k < n := by
      intro i hi k hk
      obtain ⟨a, ⟨h1, h2⟩, rfl⟩ := (mem_stored R i k).1 hk
      have := hrows.end_le hi
      have := hrows.mono i hi
      exact hrows.small a (by omega)
    have hscan := testcanlab_rows (Graph.ofGraph G) R lab hR hlsz hn0
    have hpost : ∀ m' st' marks' (r : Int) (c : Nat),
        Hex.GraphIso.Nauty.Sparse.testcanlab (Graph.ofGraph G) R lab = (r, c) →
        MarksAt m' cap2 b2 st' marks' →
        ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so)) (fun _ => .Vint (ir c)) 1 →
        Unch m3 m' (fun z => z = Block.vmark1Val ∨ (0 < cap2 ∧ z = b2) ∨ z = bs) →
        (∀ z, Mem.valid_block m3 z → Mem.valid_block m' z) →
        (testcanlabSpec G bsg sofs bv vo bd dofs be eo R bc cofs cbv cvo cbd cdofs cbe ceo lab bl lofs
          bs so svals M capW bW cap b st marks).post
          [.Vptr bsg sofs, .Vptr bc cofs, .Vptr bl lofs, .Vptr bs so, .Vint (ir M), .Vint (ir n)] m E0
          (.Vint (ir r)) m' := by
      intro m' st' marks' r c hrc hM' harr' hu' hg'
      have hbW1S : ¬ (bW1 = Block.vmark1Val ∨ (0 < cap2 ∧ bW1 = b2) ∨ bW1 = bs) := by
        rintro (h | ⟨-, h⟩ | h)
        · exact hbW1M (.inr (.inr (.inl h)))
        · exact hb2W1 h.symm
        · exact hbsd.2.2.1 h.symm
      have hWS' : ¬ (Block.work1 = Block.vmark1Val ∨ (0 < cap2 ∧ Block.work1 = b2) ∨ Block.work1 = bs) := by
        rintro (h | ⟨h0, h⟩ | h)
        · exact absurd h (by decide)
        · exact hb2W h0 h
        · exact hbsd.2.2.2 h.symm
      have hWSS' : ¬ (Block.work1Sz = Block.vmark1Val ∨ (0 < cap2 ∧ Block.work1Sz = b2) ∨
          Block.work1Sz = bs) := by
        rintro (h | ⟨h0, h⟩ | h)
        · exact absurd h (by decide)
        · exact (Alloc.ne_new hor2 (hg1 _ hvWS) (fun h0' => (hsepM h0').2.symm) h0) h
        · exact (hsep bs (by simp [Ext])).2.2.2.2.2.1 h.symm
      have hDW' : Alloc.DynAt m' Block.work1 Block.work1Sz 4 capW1 bW1 :=
        hDW3.keep hu' hWS' hWSS' (fun _ => Alloc.Keep.unch hu' hbW1S)
      refine ⟨rfl, by rw [hrc], by rw [hrc]; exact harr', capW1, bW1, cap2, b2, st', marks', hDW', hnW,
        hor1, hM', hnc2, hor2.imp_right (fun h hv => h (hg1 _ hv)), ?_,
        fun z h => hg' _ (hg3 _ (hg2 _ (hg1 _ h)))⟩
      refine (((hu1.mono fun z hz => ?_).trans (hu2.mono fun z hz => ?_)).trans
        (hu3.mono fun z hz => ?_)).trans (hu'.mono fun z hz => ?_)
      · rcases hz with h | h | h | h
        · exact .inr (.inr (.inl h))
        · exact .inr (.inl h)
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr (.inl h))))
      · rcases hz with h | h | h | h | ⟨hnv, h⟩
        · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨fun hv => hnv (hg1 _ hv), h⟩))))))))
      · subst hz
        rcases hor1 with ⟨h1, h2⟩ | hnv
        · exact .inr (.inr (.inr (.inl ⟨by omega, h2⟩)))
        · exact .inr (.inr (.inr (.inr (.inl ⟨hnv, rfl⟩))))
      · rcases hz with h | ⟨h0, h⟩ | h
        · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
        · rcases hor2 with ⟨h1, h2⟩ | hnv
          · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, h.trans h2⟩))))))))
          · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
              ⟨fun hv => hnv (hg1 _ hv), h⟩))))))))
        · exact .inl h
    let g := Graph.ofGraph G
    let I := fun (k : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
      e' = empty_env ∧ ∃ c st' marks', c ≤ n ∧ k = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
        MarksAt m' cap2 b2 st' marks' ∧
        Unch m3 m' (fun z => z = Block.vmark1Val ∨ (0 < cap2 ∧ z = b2)) ∧
        (∀ z, Mem.valid_block m3 z → Mem.valid_block m' z) ∧
        (∀ i' < c, rowCode g R lab i' = none) ∧
        ∀ x, x ≠ id.i → ¬ RowLocal x → PTree.get x le' = PTree.get x le3
    let J := fun (k : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
      e' = empty_env ∧ ∃ c st' marks', c < n ∧ k = n - c ∧ PTree.get id.i le' = some (.Vint (ir c)) ∧
        MarksAt m' cap2 b2 st' marks' ∧
        Unch m3 m' (fun z => z = Block.vmark1Val ∨ (0 < cap2 ∧ z = b2)) ∧
        (∀ z, Mem.valid_block m3 z → Mem.valid_block m' z) ∧
        (∀ i' < c + 1, rowCode g R lab i' = none) ∧
        ∀ x, x ≠ id.i → ¬ RowLocal x → PTree.get x le' = PTree.get x le3
    have hSR : ∀ z, FrameB bv bd be cbv cbd cbe bl bs bW1 z →
        ¬ (z = Block.vmark1Val ∨ (0 < cap2 ∧ z = b2)) := fun z hz h => by
      rcases h with h | ⟨h0, h⟩
      · exact (hsepR z hz).2.1 h
      · exact (hsepR z hz).1 h0 h
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    refine wp_loop (I := I) (J := J) ?_ ?_ (n := n - 0)
      ⟨rfl, rfl, 0, st2, marks2, Nat.zero_le _, rfl, temps_gss _ _ _, hM3, Unch.refl _ _,
        fun _ h => h, fun i' hi' => absurd hi' (by omega), fun x hx _ => temps_gso _ _ hx⟩
    · rintro k t e' le' m' ⟨rfl, rfl, c, st', marks', hc, rfl, hi, hM', hu', hg', hrow, ho⟩
      have hf' := (hf.mem hu' hSR).temps ho
      wp_step; wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tv id.i) = _ from hi,
        show Exec.evalExpr sge empty_env le' m' (tv id.n) = _ from hf'.hn]
      simp only [typeof, cop]
      rw [ir_lt (a := (c : Int)) (b := (n : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hcn : c < n
      · rw [ite_eq_left (by simpa using hcn)]
        apply wp_skip
        refine wp_row hf' hi hcn hM' (by omega) hsepR hbsd ?_ ?_
        · intro hnone le'' m'' st'' marks'' hM'' hu'' hg'' ho''
          refine ⟨by simp, rfl, c, st'', marks'', hcn, rfl, ?_, hM'',
            hu'.trans hu'', fun z h => hg'' _ (hg' _ h), fun i' hi' => ?_, fun x hx hx' => ?_⟩
          · rw [ho'' _ (by decide)]; exact hi
          · rcases Nat.lt_or_ge i' c with h | h
            · exact hrow i' h
            · rw [show i' = c by omega]; exact hnone
          · rw [ho'' x hx', ho x hx hx']
        · intro r hr m'' st'' marks'' hM'' harr'' hu'' hg''
          simp only [E0_append]
          refine hpost m'' st'' marks'' r c (scan_eq hscan hcn hrow hr) hM'' harr''
            ((hu'.mono fun z hz => ?_).trans hu'') fun z h => hg'' _ (hg' _ h)
          rcases hz with h | h
          · exact .inl h
          · exact .inr (.inl h)
      · rw [ite_eq_right (by simpa using hcn)]
        apply wp_break
        have hcn' : c = n := by omega
        subst hcn'
        have hres := scan_end hscan hrow
        wp_step
        refine wp_setSame hf'.hsr hf'.hn hf'.sarr ?_
        intro m'' harr'' hu'' hk'' hg''
        have hM'' := hM'.unch hu'' (fun h => (hsepR bs (by simp [FrameB])).2.2.1 h.symm)
          (fun h => (hsepR bs (by simp [FrameB])).2.2.2 h.symm)
          (fun h => (hsepR bs (by simp [FrameB])).2.1 h.symm)
          (fun h0 h => (hsepR bs (by simp [FrameB])).1 h0 h.symm)
        refine wp_ret_const (c := 0) ?_
        simp only [E0_append]
        exact hpost m'' st' marks' 0 c hres hM'' harr''
          ((hu'.mono fun z hz => by rcases hz with h | h; exact .inl h; exact .inr (.inl h)).trans
            (hu''.mono fun z hz => .inr (.inr hz))) fun z h => hg'' _ (hg' _ h)
    · rintro k t e' le' m' ⟨rfl, rfl, c, st', marks', hc, rfl, hi, hM', hu', hg', hrow, ho⟩
      wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, show Exec.evalExpr sge empty_env le' m' (tv id.i) = _ from hi]
      simp only [Exec.evalExpr, typeof, cop, ir_add]
      exact ⟨n - (c + 1), by omega, by simp, rfl, c + 1, st', marks', hc, rfl, temps_gss _ _ _, hM', hu',
        hg', hrow, fun x hx hx' => by rw [temps_gso _ _ hx, ho x hx hx']⟩

end NautyVerified.Proofs.Sparse.Testcanlab

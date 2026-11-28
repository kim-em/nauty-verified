import NautyVerified.Proofs.Sparse.Refine.Count.FragLoop
import NautyVerified.Proofs.Sparse.Refine.Wide
import NautyVerified.Proofs.Sparse.Sort.Satisfies
import NautyVerified.Logic.Grow

/-!
# The count split's `sortindirect` call

`wp_sort`: `sortindirect(lab + v3, HITS, j - v3)` sorts the labels of
`[v3, j)` by HexGraphIso's `Sort.indirect` on the hit counts. The call may
change `lab` and blocks not valid before it (its stack frame), so memory
afterwards holds the state with the sorted labels (`Mem.sortLab`); the
graph's edge array survives even when it is not a valid block, since it is
then empty.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Alloc (Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- An array survives a change of the written block `b` and of invalid blocks
when it is valid or empty. -/
theorem arr_unchV {m m' : mem} {bl : block} (hu : Unch m m' (fun z => z = bl ∨ ¬ Mem.valid_block m z))
    {chunk : memory_chunk} {b : block} {base : Int} {vals : Nat → val} {k : Nat}
    (h : ArrayAt m chunk b base vals k) (hb : b ≠ bl) : ArrayAt m' chunk b base vals k := by
  by_cases hv : Mem.valid_block m b
  · exact h.unch hu (fun e => e.elim hb (· hv))
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨h.base_nonneg, h.fits, fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩
    · exact absurd (arr_valid h hk) hv

/-- Memory after a change of `lab` and of invalid blocks holds the state with
the new labels. -/
theorem Mem.sortLab {m m' : mem} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (fun z => z = L.bl ∨ ¬ Mem.valid_block m z))
    (hk : ∀ z, Mem.valid_block m z → Keep m m' z)
    (t' : RefineSt n) (harr : ArrayAt m' .Mint32 L.bl L.lb (ints t'.lab) n)
    (hp : t'.ptn = t.ptn) (hn : t'.numcells = t.numcells) (ha : t'.active = t.active) :
    Mem m' L G t' S := by
  have h0 := hok.n0
  have hw := h.wvalid hok
  have nb : ∀ z, L.writes z → z ≠ L.bl → ¬ (z = L.bl ∨ ¬ Mem.valid_block m z) :=
    fun z hz hne e => e.elim hne (· (hw z hz))
  have nr : ∀ z ∈ L.rblocks, Mem.valid_block m z → ¬ (z = L.bl ∨ ¬ Mem.valid_block m z) :=
    fun z hz hv e => e.elim (fun e' => hok.rw z hz (by rw [e']; simp [Loc.writes, Loc.wblocks])) (· hv)
  have rb : ∀ z ∈ L.rblocks, z ≠ L.bl := fun z hz e =>
    hok.rw z hz (by rw [e]; simp [Loc.writes, Loc.wblocks])
  have hsg : Mem.valid_block m L.bsg := Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h.graph.v)
  have nsg := nr L.bsg (by simp [Loc.rblocks]) hsg
  have hvw : ∀ z, z ∈ L.wblocks → Keep m m' z := fun z hz => hk z (hw z hz)
  exact {
    graph := {
      nde := by rw [hu.load _ _ _ nsg]; exact h.graph.nde
      v := by rw [hu.load _ _ _ nsg]; exact h.graph.v
      nv := by rw [hu.load _ _ _ nsg]; exact h.graph.nv
      d := by rw [hu.load _ _ _ nsg]; exact h.graph.d
      e := by rw [hu.load _ _ _ nsg]; exact h.graph.e
      w := by rw [hu.load _ _ _ nsg]; exact h.graph.w
      varr := arr_unchV hu h.graph.varr (rb _ (by simp [Loc.rblocks]))
      darr := arr_unchV hu h.graph.darr (rb _ (by simp [Loc.rblocks]))
      earr := arr_unchV hu h.graph.earr (rb _ (by simp [Loc.rblocks])) }
    lab := harr
    ptn := hp ▸ h.ptn.unch hu (nb _ (by simp [Loc.writes, Loc.wblocks])
      (Ne.symm (pw_ne hok.wdistinct 0 1 (by decide) (by simp [Loc.wblocks]))))
    nc := hn ▸ h.nc.unch hu (nb _ (by simp [Loc.writes, Loc.wblocks])
      (Ne.symm (pw_ne hok.wdistinct 0 2 (by decide) (by simp [Loc.wblocks]))))
    act := h.act.unch hu (nb _ (by simp [Loc.writes, Loc.wblocks])
      (Ne.symm (pw_ne hok.wdistinct 0 3 (by decide) (by simp [Loc.wblocks]))))
    actRep := ha ▸ h.actRep
    code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (nb _ (by simp [Loc.writes, Loc.wblocks])
      (Ne.symm (pw_ne hok.wdistinct 0 4 (by decide) (by simp [Loc.wblocks]))))⟩
    d1 := h.d1.keep hu (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.d1.bpW))
      (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.d1.bsW))
      (fun _ => hvw _ (by simp [Loc.wblocks]))
    d2 := h.d2.keep hu (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.d2.bpW))
      (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.d2.bsW))
      (fun _ => hvw _ (by simp [Loc.wblocks]))
    d3 := h.d3.keep hu (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.d3.bpW))
      (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.d3.bsW))
      (fun _ => hvw _ (by simp [Loc.wblocks]))
    d4 := h.d4.keep hu (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.d4.bpW))
      (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.d4.bsW))
      (fun _ => hvw _ (by simp [Loc.wblocks]))
    w1 := h.w1.unch hu (nb _ (by simp [Loc.writes, Loc.wblocks])
      (Ne.symm (pw_ne hok.wdistinct 0 5 (by decide) (by simp [Loc.wblocks]))))
    w2 := h.w2.unch hu (nb _ (by simp [Loc.writes, Loc.wblocks])
      (Ne.symm (pw_ne hok.wdistinct 0 6 (by decide) (by simp [Loc.wblocks]))))
    w3 := h.w3.unch hu (nb _ (by simp [Loc.writes, Loc.wblocks])
      (Ne.symm (pw_ne hok.wdistinct 0 7 (by decide) (by simp [Loc.wblocks]))))
    hi := h.hi.unch hu (nb _ (by simp [Loc.writes, Loc.wblocks])
      (Ne.symm (pw_ne hok.wdistinct 0 7 (by decide) (by simp [Loc.wblocks]))))
    w4 := h.w4.unch hu (nb _ (by simp [Loc.writes, Loc.wblocks])
      (Ne.symm (pw_ne hok.wdistinct 0 8 (by decide) (by simp [Loc.wblocks]))))
    k1 := h.k1.unch hu (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.k1.dyn.bpW))
      (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.k1.dyn.bsW))
      (nb _ (by simp [Loc.writes, Loc.wblocks])
        (Ne.symm (pw_ne hok.wdistinct 0 11 (by decide) (by simp [Loc.wblocks]))))
      (fun _ => nb _ (by simp [Loc.writes, Loc.wblocks])
        (Ne.symm (pw_ne hok.wdistinct 0 9 (by decide) (by simp [Loc.wblocks]))))
    k2 := h.k2.unch hu (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.k2.dyn.bpW))
      (nr _ (by simp [Loc.rblocks]) (Alloc.valid_of_access h.k2.dyn.bsW))
      (nb _ (by simp [Loc.writes, Loc.wblocks])
        (Ne.symm (pw_ne hok.wdistinct 0 12 (by decide) (by simp [Loc.wblocks]))))
      (fun _ => nb _ (by simp [Loc.writes, Loc.wblocks])
        (Ne.symm (pw_ne hok.wdistinct 0 10 (by decide) (by simp [Loc.wblocks]))))
    bit := fun q hq => by
      rw [hu.load _ _ _ (nr _ (by simp [Loc.rblocks])
        (Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ (h.bit 0 (by decide)))))]
      exact h.bit q hq
    left := fun q hq => by
      erw [hu.load _ _ _ (nr (NautyEnv.leftbit : block) (by simp [Loc.rblocks])
        (Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ (h.left 0 (by decide)))))]
      exact h.left q hq }

theorem type_sortindirect :
    type_of_fundef (.Internal sparse.fn.«nausparse:sortindirect») =
      tfun [(tptr tint), (tptr tint), tint] Tvoid := rfl

/-- `sortindirect(lab + v3, HITS, j - v3)` -/
abbrev sortS : statement :=
  .Scall none
    (.Evar id.«nausparse:sortindirect» (tfun [(tptr tint), (tptr tint), tint] Tvoid))
    [(.Ebinop .Oadd (pi id.«lab») (tv id.«v3») (tptr tint)),
     (.Evar id.«nausparse:work3» (tptr tint)),
     (.Ebinop .Osub (tv id.«j») (tv id.«v3») tint)]

theorem wp_sort {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (hr : Rep L t S) (ht : Tmp le L t) {v3 last : Nat} (h1 : 1 ≤ v3) (h2 : v3 ≤ last) (h3 : last ≤ n)
    (hlab : ∀ q < n, t.lab[q]! < n) (hsz : t.lab.size = n) (hhits : ∀ v < n, S.w3[v]! = t.hits[v]!)
    (hv3 : PTree.get id.«v3» le = some (.Vint (ir v3)))
    (hj : PTree.get id.«j» le = some (.Vint (ir last)))
    (hQ : ∀ m', Mem m' L G { t with lab := Hex.GraphIso.Nauty.Sparse.Sort.indirect t.lab t.hits v3 (last - v3) } S →
      Frame L m m' → Q.normal E0 empty_env le m') :
    Wp xi sge F sortS Q empty_env le m := by
  have hnl := hok.nlt
  have hn0 := hok.n0
  let C : Sort.Ctx := ⟨L.bl, L.lb, n, L.b3, Ptrofs.zero, S.w3⟩
  have hw3s := hr.w3size
  have hC : C.Ok := ⟨show L.bl ≠ L.b3 from pw_ne hok.wdistinct 0 7 (by decide) (by simp [Loc.wblocks]),
    show n < _ by omega,
    by show S.w3.size < _; omega, fun i hi => hr.w3small i (by simpa [C, hw3s] using hi), hn0⟩
  have hX : Sort.Arr m C t.lab := ⟨hm.lab, by
      show ArrayAt m .Mint32 L.b3 (intOfZ (Ptrofs.unsigned Ptrofs.zero)) (ints S.w3) S.w3.size
      rw [hw3s]; exact hm.w3, hsz, fun i hi => by show _ < S.w3.size; rw [hw3s]; exact hlab i hi⟩
  have hfits := hm.lab.fits
  have hb0 := hm.lab.base_nonneg
  refine wp_call (vf := .Vptr Block.sortindirect Ptrofs.zero) (targs := [(tptr tint), (tptr tint), tint])
    (tres := Tvoid) (cc := Common.AST.cc_default)
    (vargs := [.Vptr L.bl (Sort.pt L.lb v3), .Vptr L.b3 Ptrofs.zero, .Vint (ir ((last - v3 : Nat) : Int))]) _
    _ (NautyVerified.Proofs.Sparse.Sort.sortindirect_satisfies C t.lab v3 (last - v3)).grow rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get id.«nausparse:sortindirect» (empty_env : env) = none from rfl,
      find_sortindirect, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
    ?_ (by simp [Common.Globalenvs.Genv.find_funct, funct_sortindirect]) type_sortindirect
    ⟨rfl, hC, hX, h1, by show v3 + (last - v3) ≤ n; omega⟩ ?_
  · have hw3 := eval_w3 (le := le) hok hm
    simp only [Exec.evalExprlist, Exec.evalExpr, ht.lab, hv3, hj, typeof, cop] at hw3 ⊢
    rw [hw3]
    simp only [cop, ir_sub]
    rw [add_ptrTo L.lofs _ v3 (by omega), show ((last : Int) - v3) = ((last - v3 : Nat) : Int) by omega]
    rfl
  · rintro tr v m' ⟨⟨rfl, harr, hu, hk⟩, hg⟩
    simp only [set_opttemp]
    have hag : Hex.GraphIso.Nauty.Sparse.Sort.Agree S.w3 t.hits v3 (v3 + (last - v3)) t.lab :=
      ⟨by omega, fun q h1 h2 => hhits _ (hlab q (by omega))⟩
    have hi := Hex.GraphIso.Nauty.Sparse.Sort.indirect_congr hag
    have harr' : ArrayAt m' .Mint32 L.bl L.lb
        (ints (Hex.GraphIso.Nauty.Sparse.Sort.indirect t.lab t.hits v3 (last - v3))) n := by
      rw [← hi]; exact harr.arr
    exact hQ m' (Mem.sortLab hok hm hu hk _ harr' rfl rfl rfl)
      ⟨hu.mono fun z hz => hz.imp_left fun (e : z = L.bl) => by rw [e]; simp [Loc.writes, Loc.wblocks], hk, hg⟩

end NautyVerified.Proofs.Sparse.Refine.Count

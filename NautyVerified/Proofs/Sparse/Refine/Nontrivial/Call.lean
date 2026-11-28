import NautyVerified.Proofs.Sparse.Refine.Nontrivial.Count

/-!
# Calls that write `HITCELL`

`Mem.valid`: every block `Mem` describes (but possibly the neighbour array,
when there is no edge) is valid. `Mem.setW4Call`: after a call that changes
only `work4` and blocks new to the caller (`sortints(HITCELL, hitcells)`),
memory holds `Mem` with the new `work4` contents.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Nontrivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Alloc (Keep DynAt)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

theorem valid_of_load {m : mem} {c : memory_chunk} {b : block} {o : Z} {v : val}
    (h : Mem.load c m b o = some v) : Mem.valid_block m b :=
  Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h)

theorem arr_valid {m : mem} {c : memory_chunk} {b : block} {base : Int} {vals : Nat → val}
    {k : Nat} (h : ArrayAt m c b base vals k) (hk : 0 < k) : Mem.valid_block m b :=
  valid_of_load (h.load 0 hk)

theorem Mem.valid {n : Nat} {m : mem} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}
    (hok : Ok n L) (h : Mem m L G t S) :
    ∀ y ∈ [L.bsg, L.bv, L.bd] ++ L.rblocks.drop 4 ++ L.wblocks, Mem.valid_block m y := by
  have hn := hok.n0
  have hM := hok.M1
  intro y hy
  simp only [Loc.rblocks, Loc.wblocks, List.drop, List.cons_append, List.nil_append,
    List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid_of_load h.graph.nde
  · exact arr_valid h.graph.varr hn
  · exact arr_valid h.graph.darr hn
  · exact Alloc.valid_of_access h.d1.bpW
  · exact Alloc.valid_of_access h.d1.bsW
  · exact Alloc.valid_of_access h.d2.bpW
  · exact Alloc.valid_of_access h.d2.bsW
  · exact Alloc.valid_of_access h.d3.bpW
  · exact Alloc.valid_of_access h.d3.bsW
  · exact Alloc.valid_of_access h.d4.bpW
  · exact Alloc.valid_of_access h.d4.bsW
  · exact Alloc.valid_of_access h.k1.dyn.bpW
  · exact Alloc.valid_of_access h.k1.dyn.bsW
  · exact Alloc.valid_of_access h.k2.dyn.bpW
  · exact Alloc.valid_of_access h.k2.dyn.bsW
  · exact valid_of_load (h.bit 0 (by decide))
  · exact valid_of_load (h.left 0 (by decide))
  · exact arr_valid h.lab hn
  · exact arr_valid h.ptn hn
  · exact arr_valid h.nc (by decide)
  · exact arr_valid h.act hM
  · obtain ⟨kv, hkv⟩ := h.code; exact arr_valid hkv (by decide)
  · exact arr_valid h.w1 (by have := hok.c1; omega)
  · exact arr_valid h.w2 (by have := hok.c2; omega)
  · exact arr_valid h.w3 hn
  · exact arr_valid h.w4 (by have := hok.c4; omega)
  · exact arr_valid h.k1.arr (by have := hok.mc1; omega)
  · exact arr_valid h.k2.arr (by have := hok.mc2; omega)
  · exact Alloc.valid_of_access h.k1.valW
  · exact Alloc.valid_of_access h.k2.valW

/-- A call that may change `work4` and new blocks only: `Mem` with the new
`HITCELL` contents. -/
theorem Mem.setW4Call {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hv : ∀ y ∈ [L.bsg, L.bv, L.bd] ++ L.rblocks.drop 4 ++ L.wblocks, Mem.valid_block m y)
    (hbe : 0 < G.neighbors.size → Mem.valid_block m L.be)
    (hu : Unch m m' (fun y => y = L.b4 ∨ ¬ Mem.valid_block m y)) (hk : Keep m m' L.b4)
    (w : Nat → val) (harr : ArrayAt m' .Mint32 L.b4 0 w L.c4) :
    Mem m' L G t { S with w4 := w } where
  graph := by
    have hs : ¬ (L.bsg = L.b4 ∨ ¬ Mem.valid_block m L.bsg) := (fun hh => hh.elim (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks]))))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.graph.varr.unch hu (fun hh => hh.elim (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))),
      h.graph.darr.unch hu (fun hh => hh.elim (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))), ?_⟩
    · rw [hu.load _ _ _ hs]; exact h.graph.nde
    · rw [hu.load _ _ _ hs]; exact h.graph.v
    · rw [hu.load _ _ _ hs]; exact h.graph.nv
    · rw [hu.load _ _ _ hs]; exact h.graph.d
    · rw [hu.load _ _ _ hs]; exact h.graph.e
    · rw [hu.load _ _ _ hs]; exact h.graph.w
    · by_cases h0 : 0 < G.neighbors.size
      · exact h.graph.earr.unch hu (fun hh => hh.elim (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hbe h0)))
      · have : G.neighbors.size = 0 := by omega
        exact ⟨h.graph.earr.base_nonneg, h.graph.earr.fits, fun q hq => absurd hq (by omega),
          fun q hq => absurd hq (by omega)⟩
  lab := h.lab.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 0 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks]))))
  ptn := h.ptn.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 1 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks]))))
  nc := h.nc.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 2 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks]))))
  act := h.act.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 3 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks]))))
  w1 := h.w1.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 5 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks]))))
  w2 := h.w2.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 6 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks]))))
  w3 := h.w3.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 7 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks]))))
  actRep := h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 4 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks]))))⟩
  d1 := h.d1.keep hu (fun hh => hh.elim (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun hh => hh.elim (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun _ => Keep.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 5 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks])))))
  d2 := h.d2.keep hu (fun hh => hh.elim (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun hh => hh.elim (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun _ => Keep.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 6 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks])))))
  d3 := h.d3.keep hu (fun hh => hh.elim (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun hh => hh.elim (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun _ => Keep.unch hu (fun hh => hh.elim (pw_ne hok.wdistinct 7 8 (by decide) (by simp [Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.wblocks])))))
  d4 := h.d4.keep hu (fun hh => hh.elim (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun hh => hh.elim (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun _ => hk)
  w4 := harr
  k1 := h.k1.unch hu (fun hh => hh.elim (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun hh => hh.elim (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun hh => hh.elim (Ne.symm (pw_ne hok.wdistinct 8 11 (by decide) (by simp [Loc.wblocks]))) (fun hnv => hnv (hv _ (by simp [Loc.wblocks])))) (fun _ => (fun hh => hh.elim (Ne.symm (pw_ne hok.wdistinct 8 9 (by decide) (by simp [Loc.wblocks]))) (fun hnv => hnv (hv _ (by simp [Loc.wblocks])))))
  k2 := h.k2.unch hu (fun hh => hh.elim (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun hh => hh.elim (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks])))) (fun hh => hh.elim (Ne.symm (pw_ne hok.wdistinct 8 12 (by decide) (by simp [Loc.wblocks]))) (fun hnv => hnv (hv _ (by simp [Loc.wblocks])))) (fun _ => (fun hh => hh.elim (Ne.symm (pw_ne hok.wdistinct 8 10 (by decide) (by simp [Loc.wblocks]))) (fun hnv => hnv (hv _ (by simp [Loc.wblocks])))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun hh => hh.elim (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks]))))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun hh => hh.elim (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun hnv => hnv (hv _ (by simp [Loc.rblocks]))))]; exact h.left q hq

/-- An array whose block kept its permissions, with known contents below `k`. -/
theorem arr_keep {m m' : mem} {b : block} {vals : Nat → val} {c : Nat}
    (h : ArrayAt m .Mint32 b 0 vals c) (hk : Keep m m' b) {k : Nat} {vals' : Nat → val}
    (h' : ArrayAt m' .Mint32 b 0 vals' k) :
    ∃ w : Nat → val, ArrayAt m' .Mint32 b 0 w c ∧ ∀ i < k, w i = vals' i := by
  have hw : ∀ i < c, Mem.valid_access m' .Mint32 b (elemOfs .Mint32 0 i) .Writable := fun i hi =>
    ⟨fun o ho => hk.perm _ _ ((h.writable i hi).1 o ho), (h.writable i hi).2⟩
  refine ⟨fun i => if i < k then vals' i else (Mem.load .Mint32 m' b (elemOfs .Mint32 0 i)).getD .Vundef,
    ⟨h.base_nonneg, h.fits, fun i hi => ?_, hw⟩, fun i hi => by simp [hi]⟩
  by_cases hik : i < k
  · simp only [hik, ite_true]; exact h'.load i hik
  · simp only [hik, ite_false]
    obtain ⟨v, hv⟩ := Mem.valid_access_load _ _ _ _
      (Mem.valid_access_implies _ _ _ _ _ _ (hw i hi) .perm_W_R)
    rw [hv]; rfl

end NautyVerified.Proofs.Sparse.Refine.Nontrivial

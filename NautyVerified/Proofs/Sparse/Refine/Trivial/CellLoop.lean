import NautyVerified.Proofs.Sparse.Refine.Trivial.Cell

/-!
# The touched-cell loop of the singleton splitter

`wp_cellLoop`: `for (i = 0; i < hitcells; ++i) cellBody` over the touched
cells `HITCELL[0..hitcells)` computes the fold of `cellT`, with HexGraphIso's
touched-cell trace (`Hex.GraphIso.Nauty.Sparse.binary_step`, `Cell.valid`, `Cell.preserve`)
keeping every later touched start a cell of the current partition.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Trivial

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)
open Hex.GraphIso.Nauty (IsCell)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {S : Scr}

/-- What one touched cell keeps and changes. -/
theorem cellT_props (level stamp first : Nat) (s : RefineSt n) :
    (cellT level stamp first s).vmarks = s.vmarks ∧
      s.queue.size ≤ (cellT level stamp first s).queue.size ∧
      s.numcells ≤ (cellT level stamp first s).numcells ∧
      (cellT level stamp first s).longcode < 32768 := by
  rw [cellT_fix]
  generalize partAt s.vmarks stamp first s.lab (s.cellend[first]! + 1 - first) = p
  by_cases h : (p.2.1 != (revAt p.2.1 p.2.2 p.1 s.cellstart p.2.2.size).2.2 && p.2.1 != first) = true
  · rw [fixRes_true _ _ _ _ _ h]
    unfold fixPush
    split <;> simp [RefineSt.push, RefineSt.hash, Refine.mash_lt]
  · unfold fixRes
    rw [ite_eq_right h]
    exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Refine.mash_lt _ _⟩

/-- The touched-cell fold. -/
abbrev cellFold (level stamp : Nat) (l : List Nat) (t : RefineSt n) : RefineSt n :=
  l.foldl (fun t first => cellT level stamp first t) t

theorem cellFold_props (level stamp : Nat) : ∀ (l : List Nat) (t : RefineSt n), t.longcode < 2 ^ 62 →
    (cellFold level stamp l t).vmarks = t.vmarks ∧
      t.queue.size ≤ (cellFold level stamp l t).queue.size ∧
      t.numcells ≤ (cellFold level stamp l t).numcells ∧
      (cellFold level stamp l t).longcode < 2 ^ 62
  | [], _, h => ⟨rfl, Nat.le_refl _, Nat.le_refl _, h⟩
  | a :: l, t, h => by
    have h1 := cellT_props level stamp a t
    have h2 := cellFold_props level stamp l (cellT level stamp a t) (by omega)
    simp only [cellFold, List.foldl_cons] at h2 ⊢
    exact ⟨h2.1.trans h1.1, by omega, by omega, h2.2.2.2⟩

theorem cellFold_take (level stamp : Nat) (l : List Nat) (t : RefineSt n) {q : Nat} (hq : q < l.length) :
    cellFold level stamp (l.take (q + 1)) t = cellT level stamp l[q] (cellFold level stamp (l.take q) t) := by
  simp only [cellFold, List.take_add_one, List.getElem?_eq_getElem hq, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem cellFold_drop (level stamp : Nat) (l : List Nat) (t : RefineSt n) (q : Nat) :
    cellFold level stamp l t = cellFold level stamp (l.drop q) (cellFold level stamp (l.take q) t) := by
  have h : cellFold level stamp l t = cellFold level stamp (l.take q ++ l.drop q) t := by
    rw [List.take_append_drop]
  rw [h]
  simp only [cellFold, List.foldl_append]

/-- What the fold keeps after `q` cells. -/
def TraceInv (level : Nat) (l : List Nat) (init : RefineSt n) (q : Nat) (t : RefineSt n) : Prop :=
  t.lab.toList.Perm (List.range n) ∧ t.ptn.size = n ∧
    Hex.GraphIso.Nauty.Sparse.Index.Valid n t.lab t.ptn level t.cellstart t.cellend ∧
    ∀ a ∈ l.drop q, IsCell t.ptn level a (init.cellend[a]! + 1 - a)

/-- HexGraphIso's touched-cell trace, along the fold. -/
theorem cellFold_trace (level stamp : Nat) (l : List Nat) (init : RefineSt n) (hn : l.Nodup)
    (hp : init.lab.toList.Perm (List.range n)) (hs : init.ptn.size = n)
    (hi : Hex.GraphIso.Nauty.Sparse.Index.Valid n init.lab init.ptn level init.cellstart init.cellend)
    (hc : ∀ a ∈ l, IsCell init.ptn level a (init.cellend[a]! + 1 - a) ∧ a < init.cellend[a]! ∧
      init.cellend[a]! < n) :
    ∀ q, q ≤ l.length → TraceInv level l init q (cellFold level stamp (l.take q) init)
  | 0, _ => ⟨hp, hs, hi, fun a ha => (hc a (by simpa using ha)).1⟩
  | q + 1, hq => by
    obtain ⟨h1, h2, h3, h4⟩ := cellFold_trace level stamp l init hn hp hs hi hc q (by omega)
    rw [cellFold_take _ _ _ _ (by omega)]
    generalize hu : cellFold level stamp (l.take q) init = u at h1 h2 h3 h4
    have hmem : l[q] ∈ l.drop q := by
      rw [List.drop_eq_getElem_cons (i := q) (by omega)]; exact List.mem_cons_self ..
    have hcur := h4 _ hmem
    have hci := hc _ (List.getElem_mem (l := l) (n := q) (by omega))
    have he := h3.ends_eq l[q] (init.cellend[l[q]]! + 1 - l[q]) hcur (by have := hci.2.2; omega)
      (by have := hci.2.2; omega)
    have heq : u.cellend[l[q]]! = init.cellend[l[q]]! := by omega
    have hcell : IsCell u.ptn level l[q] (u.cellend[l[q]]! + 1 - l[q]) := by rw [heq]; exact hcur
    have hsize : u.lab.size = n := by simpa using h1.length_eq
    have hbody := Hex.GraphIso.Nauty.Sparse.binary_step level l[q] stamp u (by omega) (by omega) h3.starts_size
      (fun v hv => List.mem_range.mp (h1.mem_iff.mp hv))
    have hbody' : Hex.GraphIso.Nauty.Sparse.Binary.Cell level l[q] (u.cellend[l[q]]! + 1) (fun v => u.vmarks[v]! == stamp) u
        (cellT level stamp l[q] u) := by
      rw [← cellT_eq]; exact hbody
    have hv := hbody'.valid h1 h2 h3 (by simpa using hcell) (by omega)
    refine ⟨hv.1, hv.2.1, hv.2.2, fun a ha => ?_⟩
    have ha' : a ∈ l.drop q := by
      rw [List.drop_eq_getElem_cons (i := q) (by omega)]; exact List.mem_cons_of_mem _ ha
    have hne : a ≠ l[q] := by
      intro e
      have hd : (l.drop q).Nodup := List.Nodup.sublist (List.drop_sublist q l) hn
      rw [List.drop_eq_getElem_cons (i := q) (by omega)] at hd
      exact (List.nodup_cons.mp hd).1 (e ▸ ha)
    exact hbody'.preserve (by simpa using hcell) (h4 a ha') hne

theorem cellLoopT_eq : cellLoopT =
    .Sloop (.Ssequence (sk (.Sifthenelse (.Ebinop .Olt (tv id.«i») (tv id.«hitcells») tint) .Sskip .Sbreak))
      cellBody) (sk (.Sset id.«i» (.Ebinop .Oadd (tv id.«i») (ci 1 tint) tint))) := rfl

/-- The temporaries the touched-cell loop assigns besides `longcode` and `nactive`. -/
abbrev loopTempsT : List ident := id.«i» :: cellTempsT

theorem wp_cellLoop {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) {init : RefineSt n}
    (hm : Mem m L G init S) (hr : Rep L init S) (ht : Tmp le L init) {stamp : Nat} {l : List Nat}
    (hnd : l.Nodup) (hln : l.length ≤ n)
    (hmk : ∀ v < n, (S.mk2 v = S.st2 ↔ init.vmarks[v]! = stamp))
    (hw4 : ∀ i < l.length, S.w4 i = .Vint (ir l[i]!))
    (hhc : PTree.get id.«hitcells» le = some (.Vint (ir l.length)))
    (hi0 : PTree.get id.«i» le = some (.Vint (ir 0)))
    (hp : init.lab.toList.Perm (List.range n)) (hs : init.ptn.size = n)
    (hi : Hex.GraphIso.Nauty.Sparse.Index.Valid n init.lab init.ptn L.level init.cellstart init.cellend)
    (hc : ∀ a ∈ l, IsCell init.ptn L.level a (init.cellend[a]! + 1 - a) ∧ a < init.cellend[a]! ∧
      init.cellend[a]! < n)
    (hcode : init.longcode < 2 ^ 62)
    (hq : (cellFold L.level stamp l init).queue.size ≤ n)
    (hnc : (cellFold L.level stamp l init).numcells < 2147483648)
    (hQ : ∀ le' m' S', Mem m' L G (cellFold L.level stamp l init) S' →
      Rep L (cellFold L.level stamp l init) S' → Tmp le' L (cellFold L.level stamp l init) →
      S'.w4 = S.w4 → S'.st1 = S.st1 → S'.mk1 = S.mk1 → S'.st2 = S.st2 → S'.mk2 = S.mk2 →
      Frame L m m' →
      (∀ x, x ∉ loopTempsT → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F cellLoopT Q empty_env le m := by
  have hnl := hok.nlt
  have hfin := cellFold_props L.level stamp l init hcode
  let Inv := fun (q : Nat) (le' : temp_env) (m' : mem) (S' : Scr) =>
    Mem m' L G (cellFold L.level stamp (l.take q) init) S' ∧ Rep L (cellFold L.level stamp (l.take q) init) S' ∧ Tmp le' L (cellFold L.level stamp (l.take q) init) ∧ S'.w4 = S.w4 ∧ S'.st1 = S.st1 ∧
      S'.mk1 = S.mk1 ∧ S'.st2 = S.st2 ∧ S'.mk2 = S.mk2 ∧ Frame L m m' ∧
      ∀ x, x ∉ loopTempsT → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le' = PTree.get x le
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q S', v = l.length - q ∧ q ≤ l.length ∧ Inv q le' m' S' ∧
      PTree.get id.«i» le' = some (.Vint (ir q))
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ q S', v = l.length - q ∧ q < l.length ∧ Inv (q + 1) le' m' S' ∧
      PTree.get id.«i» le' = some (.Vint (ir q))
  rw [cellLoopT_eq]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := l.length - 0)
    ⟨rfl, rfl, 0, S, rfl, Nat.zero_le _, ⟨hm, hr, ht, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun _ _ _ _ => rfl⟩, hi0⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, q, S', rfl, hql, ⟨hm', hr', ht', e4, e5, e6, e7, e8, hf, ho⟩, hiq⟩
    have hhc' : PTree.get id.«hitcells» le' = some (.Vint (ir l.length)) := by
      rw [ho _ (by decide) (by decide) (by decide)]; exact hhc
    wp_step; wp_step; wp_step
    refine wp_if_ob (b := decide ((q : Int) < l.length)) ?_ rfl ?_
    · rw [eval_binop (eval_tv hiq) (eval_tv hhc')]
      simp only [typeof, cop]
      rw [ir_lt ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hqs : q < l.length
    · simp only [show decide ((q : Int) < l.length) = true by simpa using hqs, ite_true]
      apply wp_skip
      simp only [E0_append]
      obtain ⟨h1, h2, h3, h4⟩ := cellFold_trace L.level stamp l init hnd hp hs hi hc q (by omega)
      have hmem : l[q] ∈ l.drop q := by
        rw [List.drop_eq_getElem_cons (i := q) (by omega)]; exact List.mem_cons_self ..
      have hcur := h4 _ hmem
      have hci := hc _ (List.getElem_mem (l := l) (n := q) (by omega))
      have he := h3.ends_eq l[q] (init.cellend[l[q]]! + 1 - l[q]) hcur (by have := hci.2.2; omega)
        (by have := hci.2.2; omega)
      have heq : (cellFold L.level stamp (l.take q) init).cellend[l[q]]! = init.cellend[l[q]]! := by omega
      have hpq := cellFold_props L.level stamp (l.take q) init hcode
      have hrest := cellFold_drop L.level stamp l init (q + 1)
      rw [cellFold_take _ _ _ _ hqs] at hrest
      have hpr := cellFold_props L.level stamp (l.drop (q + 1)) (cellT L.level stamp l[q] (cellFold L.level stamp (l.take q) init))
        (by have := (cellT_props L.level stamp l[q] (cellFold L.level stamp (l.take q) init)).2.2.2; omega)
      rw [← hrest] at hpr
      have hsize : (cellFold L.level stamp (l.take q) init).lab.size = n := by simpa using h1.length_eq
      refine wp_cell (s := cellFold L.level stamp (l.take q) init) (first := l[q]) (i := q) hok hm' hr' ht'
        (fun v hv => by rw [e7, e8, hpq.1]; exact hmk v hv) hiq (by have := hok.c4; omega)
        (by rw [e4, hw4 q hqs, getElem!_pos l q hqs]) (by rw [heq]; exact hcur) (by omega) (by omega)
        hsize (fun i hi => List.mem_range.mp (h1.mem_iff.mp (by
          rw [getElem!_pos (cellFold L.level stamp (l.take q) init).lab i (by omega)]; exact Array.getElem_mem_toList ..)))
        h3.starts_size h2 hpq.2.2.2 (by omega) (by omega) ?_
      intro le2 m2 S2 hm2 hr2 ht2 f4 f5 f6 f7 f8 hf2 ho2
      have hT : cellFold L.level stamp (l.take (q + 1)) init = cellT L.level stamp l[q] (cellFold L.level stamp (l.take q) init) := cellFold_take _ _ _ _ hqs
      refine ⟨by simp, rfl, q, S2, rfl, hqs, ⟨by rw [hT]; exact hm2, by rw [hT]; exact hr2,
        by rw [hT]; exact ht2, f4.trans e4, f5.trans e5, f6.trans e6, f7.trans e7, f8.trans e8,
        hf.trans hf2, fun x hx hl hn => ?_⟩, ?_⟩
      · rw [ho2 x (fun h => hx (List.mem_cons_of_mem _ h)) hl hn, ho x hx hl hn]
      · rw [ho2 _ (by decide) (by decide) (by decide)]; exact hiq
    · simp only [show decide ((q : Int) < l.length) = false by simpa using hqs, Bool.false_eq_true,
        ite_false]
      apply wp_break
      have hqe : q = l.length := by omega
      subst hqe
      have hT : cellFold L.level stamp (l.take l.length) init = cellFold L.level stamp l init := by simp only [List.take_length]
      rw [hT] at hm' hr' ht'
      exact hQ le' m' S' hm' hr' ht' e4 e5 e6 e7 e8 hf ho
  · rintro v tr e' le' m' ⟨rfl, rfl, q, S', rfl, hql, ⟨hm', hr', ht', e4, e5, e6, e7, e8, hf, ho⟩, hiq⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [eval_inc hiq]
    dsimp only
    refine ⟨l.length - (q + 1), by omega, by simp, rfl, q + 1, S', rfl, hql, ⟨hm', hr',
      ht'.set _ (by decide), e4, e5, e6, e7, e8, hf, fun x hx hl hn => ?_⟩, ?_⟩
    · rw [temps_gso _ _ (fun h => hx (by rw [h]; exact List.mem_cons_self ..)), ho x hx hl hn]
    · rw [temps_gss]; push_cast; rfl

end NautyVerified.Proofs.Sparse.Refine.Trivial

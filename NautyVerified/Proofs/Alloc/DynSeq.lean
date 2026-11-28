import NautyVerified.Proofs.Alloc.DynG
import NautyVerified.Proofs.Alloc.Dyn3

/-!
# A run of `DYNALLOC1`s from capacity 0

`nauty()` starts with nine `DYNALLOC1`s, all on pairs that are still at
capacity 0 in the program's initial memory. `dynSeq msg len ds rest` is such a
run followed by `rest`; `wp_dynSeq` gives `rest` the new pairs, each with at
least the capacity asked for and a block that was not valid before, the new
blocks pairwise distinct, and one `Unch` for the run.

The sizes may read memory (nauty.c's `m` and `n` globals): they must evaluate
the same in every memory that leaves the protected blocks `P` alone, and no
pair's globals are protected.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs

variable {xi : ExternalCalls}

/-- One `DYNALLOC1`: its globals (identifiers and blocks), element type and
size `c`, size expression and its value `n`, and SimplExpr's temporaries. -/
structure DynD where
  gs : ident
  gp : ident
  bs : block
  bp : block
  elt : Cfrontend.Ctypes.type
  c : Nat
  sz : expr
  n : Nat
  t1 : ident
  t2 : ident

/-- The descriptors' facts about the program. -/
structure DynD.Ok (d : DynD) : Prop where
  gs : Genv.find_symbol ge.genv_genv d.gs = some d.bs
  gp : Genv.find_symbol ge.genv_genv d.gp = some d.bp
  c : intOfZ (Cfrontend.Ctypes.sizeof ge.genv_cenv d.elt) = d.c
  ty : typeof d.sz = tint
  n0 : 0 < d.n
  nlt : d.n < 2147483648
  cn : d.c * d.n < 2 ^ 62

/-- The run of `DYNALLOC1`s, then `rest`. -/
def dynSeq (msg : ident) (len : Int) (ds : List DynD) (rest : statement) : statement :=
  ds.foldr (fun d s => .Ssequence (dynalloc1 d.gs d.gp d.elt d.sz d.t1 d.t2 msg len) s) rest

/-- The pairs' globals. -/
def DynD.globals (ds : List DynD) : List block := ds.flatMap fun d => [d.bs, d.bp]

theorem wp_dynSeq {e : env} {f : function} {Q : Post} {msg : ident} {len : Int} (rest : statement)
    (P : block → Prop) (hnil : NoShadow e) :
    ∀ (ds : List DynD) (le : temp_env) (m : mem),
    (∀ d ∈ ds, d.Ok) →
    (∀ d ∈ ds, ∀ b, DynAt m d.bp d.bs d.c 0 b) →
    (DynD.globals ds).Pairwise (· ≠ ·) →
    (∀ d ∈ ds, ¬ P d.bs ∧ ¬ P d.bp) →
    (∀ z, P z → Mem.valid_block m z) →
    (∀ d ∈ ds, ∀ le' m' (S : block → Prop), Unch m m' S → (∀ z, S z → ¬ P z) →
      Exec.evalExpr ge e le' m' d.sz = some (.Vint (ir d.n))) →
    (∀ le' m' (cb : Nat → Nat × block),
      (∀ i (h : i < ds.length), DynAt m' ds[i].bp ds[i].bs ds[i].c (cb i).1 (cb i).2 ∧
        ds[i].n ≤ (cb i).1 ∧ ¬ Mem.valid_block m (cb i).2 ∧
        Zeros m' (cb i).2 (ds[i].c * (cb i).1)) →
      (∀ i j, i < j → j < ds.length → (cb i).2 ≠ (cb j).2) →
      Unch m m' (fun z => z ∈ DynD.globals ds ∨ ¬ Mem.valid_block m z) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ k, (∀ d ∈ ds, k ≠ d.t1 ∧ k ≠ d.t2) → PTree.get k le' = PTree.get k le) →
      Wp xi ge f rest Q e le' m') →
    Wp xi ge f (dynSeq msg len ds rest) Q e le m
  | [], le, m, _, _, _, _, _, _, hQ => by
    simp only [dynSeq, List.foldr_nil]
    exact hQ le m (fun _ => (0, Block.naugraphWorkperm)) (fun i h => absurd h (by simp))
      (fun _ _ _ h => absurd h (by simp)) (Unch.refl _ _) (fun _ h => h) (fun _ _ => rfl)
  | d :: ds, le, m, hok, hD, hg, hP, hPv, hsz, hQ => by
    have hd := hok d (by simp)
    have hdP := hP d (by simp)
    simp only [DynD.globals, List.flatMap_cons, List.cons_append, List.nil_append,
      List.pairwise_cons, List.mem_cons] at hg
    obtain ⟨hbs, ⟨hbp, hg'⟩⟩ := hg
    simp only [dynSeq, List.foldr_cons]
    wp_step
    refine wp_dynalloc1Z (hnil := hnil) (b := d.bs) hd.gs hd.gp hd.c (hD d (by simp) d.bs)
      (fun m' hu => hsz d (by simp) le m' _ hu (fun z hz => ?_)) hd.ty hd.nlt
      hd.cn ?_
    · rcases hz with rfl | ⟨h, -⟩
      · exact hdP.1
      · exact absurd h (Nat.lt_irrefl 0)
    intro le1 m1 cap1 b1 hD1 hc1 hu1 hb1 hg1 ho1
    simp only [seqPost, Post.after, E0_append]
    have hn0 := hd.n0
    have hb1m : ¬ Mem.valid_block m b1 := by
      rcases hb1 with ⟨h, -⟩ | h
      · omega
      · exact h.1
    have hz1 : Zeros m1 b1 (d.c * cap1) := by
      rcases hb1 with ⟨h, -⟩ | h
      · omega
      · exact h.2
    have hb1v : Mem.valid_block m1 b1 := Malloced.valid (hD1.mal (by omega))
    -- the other pairs' globals are untouched
    have nS : ∀ d' ∈ ds, ∀ z, (z = d'.bs ∨ z = d'.bp) → ¬ (z = d.bs ∨ z = d.bp ∨ (0 < 0 ∧ z = d.bs) ∨
        (¬ Mem.valid_block m b1 ∧ z = b1)) := by
      intro d' hd' z hz
      have hzg : z ∈ DynD.globals ds := by
        simp only [DynD.globals, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false]
        exact ⟨d', hd', hz⟩
      have hzv : Mem.valid_block m z := by
        rcases hz with rfl | rfl
        · exact valid_of_access (hD d' (by simp [hd']) d'.bs).bsW
        · exact valid_of_access (hD d' (by simp [hd']) d'.bs).bpW
      rintro (h | h | ⟨h, -⟩ | ⟨-, rfl⟩)
      · exact hbs z (.inr hzg) h.symm
      · exact hbp z hzg h.symm
      · exact absurd h (Nat.lt_irrefl 0)
      · exact hb1m hzv
    refine wp_dynSeq rest P hnil ds le1 m1 (fun d' h => hok d' (by simp [h]))
      (fun d' hd' b => (hD d' (by simp [hd']) b).keep hu1 (nS d' hd' _ (.inr rfl))
        (nS d' hd' _ (.inl rfl)) (fun h => absurd h (Nat.lt_irrefl 0)))
      hg' (fun d' h => hP d' (by simp [h])) (fun z hz => hg1 _ (hPv z hz)) ?_ ?_
    · intro d' hd' le' m' S hu hS
      refine hsz d' (by simp [hd']) le' m' (fun z => (z = d.bs ∨ z = d.bp ∨ (0 < 0 ∧ z = d.bs) ∨
        (¬ Mem.valid_block m b1 ∧ z = b1)) ∨ S z) ((hu1.mono fun z hz => .inl hz).trans
        (hu.mono fun z hz => .inr hz)) ?_
      · rintro z (h | h) hPz
        · rcases h with rfl | rfl | ⟨h, -⟩ | ⟨hv, rfl⟩
          · exact hdP.1 hPz
          · exact hdP.2 hPz
          · exact absurd h (Nat.lt_irrefl 0)
          · exact hv (hPv _ hPz)
        · exact hS z h hPz
    · intro le2 m2 cb hcb hdist hu2 hg2 ho2
      have hgv : ∀ z ∈ DynD.globals ds, Mem.valid_block m z := by
        intro z hz
        simp only [DynD.globals, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hz
        obtain ⟨d', hd', hz⟩ := hz
        rcases hz with rfl | rfl
        · exact valid_of_access (hD d' (by simp [hd']) d'.bs).bsW
        · exact valid_of_access (hD d' (by simp [hd']) d'.bs).bpW
      have nS2 : ∀ z, Mem.valid_block m1 z → z ∉ DynD.globals ds →
          ¬ (z ∈ DynD.globals ds ∨ ¬ Mem.valid_block m1 z) := by
        rintro z hv hn (h | h)
        · exact hn h
        · exact h hv
      have hvbs := hg1 _ (valid_of_access (hD d (by simp) d.bs).bsW)
      have hvbp := hg1 _ (valid_of_access (hD d (by simp) d.bs).bpW)
      have hb1g : b1 ∉ DynD.globals ds := fun h => hb1m (hgv _ h)
      refine hQ le2 m2 (fun i => if i = 0 then (cap1, b1) else cb (i - 1)) ?_ ?_ ?_
        (fun z hz => hg2 _ (hg1 _ hz)) ?_
      · intro i hi
        cases i with
        | zero =>
          simp only [ite_true, List.getElem_cons_zero]
          exact ⟨hD1.keep hu2 (nS2 _ hvbp (fun h => hbp _ h rfl))
            (nS2 _ hvbs (fun h => hbs _ (.inr h) rfl))
            (fun _ => Keep.unch hu2 (nS2 _ hb1v hb1g)), hc1, hb1m, hz1.unch hu2 (nS2 _ hb1v hb1g)⟩
        | succ j =>
          simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, List.getElem_cons_succ]
          obtain ⟨h1, h2, h3, h4⟩ := hcb j (by simpa using hi)
          exact ⟨h1, h2, fun h => h3 (hg1 _ h), h4⟩
      · intro i j hij hj
        cases i with
        | zero =>
          cases j with
          | zero => omega
          | succ j =>
            simp only [ite_true, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
            intro h
            exact (hcb j (by simpa using hj)).2.2.1 (h ▸ hb1v)
        | succ i =>
          cases j with
          | zero => omega
          | succ j =>
            simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
            exact hdist i j (by omega) (by simpa using hj)
      · refine (hu1.mono fun z hz => ?_).trans (hu2.mono fun z hz => ?_)
        · rcases hz with rfl | rfl | ⟨h, -⟩ | ⟨hv, rfl⟩
          · exact .inl (by simp [DynD.globals])
          · exact .inl (by simp [DynD.globals])
          · exact absurd h (Nat.lt_irrefl 0)
          · exact .inr hv
        · rcases hz with h | h
          · exact .inl (by simp only [DynD.globals, List.flatMap_cons] at h ⊢; simp [h])
          · exact .inr fun hv => h (hg1 _ hv)
      · intro k hk
        rw [ho2 k fun d' hd' => hk d' (by simp [hd']), ho1 k (hk d (by simp)).1 (hk d (by simp)).2]


end NautyVerified.Proofs.Alloc

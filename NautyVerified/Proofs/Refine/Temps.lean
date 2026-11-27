import NautyVerified.Proofs.Refine.State

/-!
# SimplExpr's temporaries as parameters

`refine` and `refine1` run the same loops with differently numbered SimplExpr
temporaries. Proofs about either take the temporaries as a list `ts` with
`NTemps ts`: they are distinct and none of the named variables `nNames` of
the two functions. At each instance `NTemps` is closed by `decide`. Inside a
proof, `nscr` discharges the identifier side conditions: by `decide` when
both sides are named, from `hT : NTemps [t0, …]` when a temporary is
involved.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean NautyVerified.Source

/-- Every named variable of `refine` and `refine1`. -/
def nNames : List Common.AST.ident :=
  [dense.id.active, dense.id.bmax, dense.id.bmin, dense.id.c1, dense.id.c2, dense.id.cell1,
   dense.id.cell2, dense.id.cnt, dense.id.code, dense.id.count, dense.id.es_, dense.id.g,
   dense.id.gptr, dense.id.hint, dense.id.i, dense.id.lab, dense.id.labc1, dense.id.level,
   dense.id.longcode, dense.id.m, dense.id.maxcell, dense.id.maxpos, dense.id.n,
   dense.id.numcells, dense.id.ptn, dense.id.set1, dense.id.set2, dense.id.split1,
   dense.id.split2, dense.id.workset0, dense.id.x]

/-- Distinct temporaries, none a named variable. -/
def NTemps (ts : List Common.AST.ident) : Prop :=
  ts.Pairwise (· ≠ ·) ∧ ∀ t ∈ ts, ∀ y ∈ nNames, t ≠ y

instance (ts : List Common.AST.ident) : Decidable (NTemps ts) := by
  unfold NTemps; infer_instance

theorem NTemps.ne {ts : List Common.AST.ident} (h : NTemps ts) (i j : Nat) (hij : i < j)
    (hj : j < ts.length := by simp) : ts[i]'(Nat.lt_trans hij hj) ≠ ts[j] := by
  have h1 := h.1
  induction ts generalizing i j with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.pairwise_cons] at h1
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => exact h1.1 _ (List.getElem_mem _)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        exact ih ⟨h1.2, fun x hx => h.2 x (by simp [hx])⟩ i j (by omega) (by simpa using hj) h1.2

theorem NTemps.fresh {ts : List Common.AST.ident} (h : NTemps ts) {t y : Common.AST.ident}
    (ht : t ∈ ts) (hy : y ∈ nNames) : t ≠ y := h.2 t ht y hy

theorem NTemps.tmp {ts : List Common.AST.ident} (h : NTemps ts) {t : Common.AST.ident}
    (ht : t ∈ ts) :
    t ∉ args ∧ t ≠ dense.id.longcode ∧ t ≠ dense.id.hint ∧ t ≠ dense.id.maxpos :=
  ⟨fun ha => h.fresh ht (by revert ha; generalize t = t; decide +revert) rfl,
   h.fresh ht (by decide), h.fresh ht (by decide), h.fresh ht (by decide)⟩

set_option hygiene false in
/-- One identifier side condition, from `decide` or `hT : NTemps [t0, …]`. -/
macro "nscr0" : tactic => `(tactic| first
  | decide
  | (refine hT.tmp ?_; simp; done)
  | (refine hT.fresh ?_ ?_ <;> (simp [nNames]; done))
  | (refine Ne.symm (hT.fresh ?_ ?_) <;> (simp [nNames]; done))
  | exact hT.ne 0 1 (by decide) | exact hT.ne 0 2 (by decide) | exact hT.ne 0 3 (by decide)
  | exact hT.ne 0 4 (by decide) | exact hT.ne 0 5 (by decide) | exact hT.ne 1 2 (by decide)
  | exact hT.ne 1 3 (by decide) | exact hT.ne 1 4 (by decide) | exact hT.ne 1 5 (by decide)
  | exact hT.ne 2 3 (by decide) | exact hT.ne 2 4 (by decide) | exact hT.ne 2 5 (by decide)
  | exact hT.ne 3 4 (by decide) | exact hT.ne 3 5 (by decide) | exact hT.ne 4 5 (by decide)
  | exact Ne.symm (hT.ne 0 1 (by decide)) | exact Ne.symm (hT.ne 0 2 (by decide))
  | exact Ne.symm (hT.ne 0 3 (by decide)) | exact Ne.symm (hT.ne 0 4 (by decide))
  | exact Ne.symm (hT.ne 0 5 (by decide)) | exact Ne.symm (hT.ne 1 2 (by decide))
  | exact Ne.symm (hT.ne 1 3 (by decide)) | exact Ne.symm (hT.ne 1 4 (by decide))
  | exact Ne.symm (hT.ne 1 5 (by decide)) | exact Ne.symm (hT.ne 2 3 (by decide))
  | exact Ne.symm (hT.ne 2 4 (by decide)) | exact Ne.symm (hT.ne 2 5 (by decide))
  | exact Ne.symm (hT.ne 3 4 (by decide)) | exact Ne.symm (hT.ne 3 5 (by decide))
  | exact Ne.symm (hT.ne 4 5 (by decide)))

/-- An identifier side condition: an inequality, a conjunction of them, or
non-membership in a list. -/
macro "nscr" : tactic => `(tactic| first
  | nscr0
  | (simp only [List.mem_cons, List.not_mem_nil, List.mem_append, or_false, not_or,
      List.mem_nil_iff, false_or]; (repeat' apply And.intro); all_goals nscr0; done)
  | ((repeat' apply And.intro); all_goals nscr0; done))

end NautyVerified.Proofs.Refine

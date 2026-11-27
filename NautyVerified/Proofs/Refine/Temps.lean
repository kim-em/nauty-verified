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

theorem NTemps.notMem {ts l : List Common.AST.ident} (h : NTemps ts) (hl : ∀ x ∈ l, x ∈ ts)
    {y : Common.AST.ident} (hy : y ∈ nNames) : y ∉ l :=
  fun hm => h.fresh (hl y hm) hy rfl

theorem args_names : ∀ x ∈ args ++ [dense.id.longcode, dense.id.hint, dense.id.maxpos], x ∈ nNames := by
  decide

/-- The temporaries a per-member count assigns: `cnt`, `x`, the word pointers and
cursor of the multi-word loop, and SimplExpr's temporaries `ht`. -/
abbrev hdTemps (ht : List Common.AST.ident) : List Common.AST.ident :=
  [dense.id.set1, dense.id.set2, dense.id.cnt, dense.id.c1] ++ ht ++ [dense.id.x]

/-- The temporaries the counting loop assigns. -/
abbrev cntTempsG (t1 t2 t3 : Common.AST.ident) (ht : List Common.AST.ident) :
    List Common.AST.ident :=
  [dense.id.i, t1] ++ hdTemps ht ++ [dense.id.bmin, dense.id.bmax, t2, t3]

/-- The temporaries `splitN` assigns, with the placement's temporary `t`. -/
abbrev splitTempsG (t : Common.AST.ident) : List Common.AST.ident :=
  [dense.id.i, dense.id.c1, dense.id.c2, dense.id.maxcell, dense.id.maxpos, dense.id.hint,
   dense.id.longcode, t]

/-- The temporaries one cell of the nontrivial pass assigns. -/
abbrev cellTempsG (t1 t2 t3 : Common.AST.ident) (hts2 : List Common.AST.ident)
    (hts1 : List Common.AST.ident) (tA tB t : Common.AST.ident) : List Common.AST.ident :=
  cntTempsG t1 t2 t3 hts2 ++ (hdTemps hts1 ++ [tA, tB]) ++ splitTempsG t

theorem NTemps.sublist {ts l : List Common.AST.ident} (h : NTemps ts) (hs : l.Sublist ts) :
    NTemps l :=
  ⟨h.1.sublist hs, fun x hx => h.2 x (hs.subset hx)⟩

/-- `Tmp` from the temporaries it reads, one by one. -/
theorem Tmp.of {n : Nat} {le le' : CompCert4Lean.Cfrontend.Clight.temp_env} {L : Loc}
    {st : Hex.GraphIso.Nauty.RefineSt n} (h : Tmp le L st)
    (h1 : CompCert4Lean.Lib.Maps.PTree.get dense.id.g le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.g le)
    (h2 : CompCert4Lean.Lib.Maps.PTree.get dense.id.lab le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.lab le)
    (h3 : CompCert4Lean.Lib.Maps.PTree.get dense.id.ptn le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.ptn le)
    (h4 : CompCert4Lean.Lib.Maps.PTree.get dense.id.level le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.level le)
    (h5 : CompCert4Lean.Lib.Maps.PTree.get dense.id.numcells le' =
      CompCert4Lean.Lib.Maps.PTree.get dense.id.numcells le)
    (h6 : CompCert4Lean.Lib.Maps.PTree.get dense.id.count le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.count le)
    (h7 : CompCert4Lean.Lib.Maps.PTree.get dense.id.active le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.active le)
    (h8 : CompCert4Lean.Lib.Maps.PTree.get dense.id.code le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.code le)
    (h9 : CompCert4Lean.Lib.Maps.PTree.get dense.id.m le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.m le)
    (h10 : CompCert4Lean.Lib.Maps.PTree.get dense.id.n le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.n le)
    (h11 : CompCert4Lean.Lib.Maps.PTree.get dense.id.longcode le' =
      CompCert4Lean.Lib.Maps.PTree.get dense.id.longcode le)
    (h12 : CompCert4Lean.Lib.Maps.PTree.get dense.id.hint le' = CompCert4Lean.Lib.Maps.PTree.get dense.id.hint le)
    (h13 : CompCert4Lean.Lib.Maps.PTree.get dense.id.maxpos le' =
      CompCert4Lean.Lib.Maps.PTree.get dense.id.maxpos le) :
    Tmp le' L st where
  g := h1 ▸ h.g
  lab := h2 ▸ h.lab
  ptn := h3 ▸ h.ptn
  level := h4 ▸ h.level
  numcells := h5 ▸ h.numcells
  count := h6 ▸ h.count
  active := h7 ▸ h.active
  code := h8 ▸ h.code
  m := h9 ▸ h.m
  n := h10 ▸ h.n
  longcode := h11 ▸ h.longcode
  hint := h12 ▸ h.hint
  maxpos := h13 ▸ h.maxpos

set_option hygiene false in
/-- One identifier side condition, from `decide` or `hT : NTemps [t0, …]`. -/
macro "nscr0" : tactic => `(tactic| first
  | decide
  | (refine hT.tmp ?_; simp; done)
  | (refine hT.notMem (fun x hx => ?_) ?_; simp [hx]; simp [nNames]; done)
  | (refine hT.fresh ?_ ?_ <;> (simp [nNames]; done))
  | (refine Ne.symm (hT.fresh ?_ ?_) <;> (simp [nNames]; done))
  | (refine hT.ne 0 1 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 0 1 (by decide) ?_); simp; done)
  | (refine hT.ne 0 2 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 0 2 (by decide) ?_); simp; done)
  | (refine hT.ne 0 3 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 0 3 (by decide) ?_); simp; done)
  | (refine hT.ne 0 4 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 0 4 (by decide) ?_); simp; done)
  | (refine hT.ne 0 5 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 0 5 (by decide) ?_); simp; done)
  | (refine hT.ne 1 2 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 1 2 (by decide) ?_); simp; done)
  | (refine hT.ne 1 3 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 1 3 (by decide) ?_); simp; done)
  | (refine hT.ne 1 4 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 1 4 (by decide) ?_); simp; done)
  | (refine hT.ne 1 5 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 1 5 (by decide) ?_); simp; done)
  | (refine hT.ne 2 3 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 2 3 (by decide) ?_); simp; done)
  | (refine hT.ne 2 4 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 2 4 (by decide) ?_); simp; done)
  | (refine hT.ne 2 5 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 2 5 (by decide) ?_); simp; done)
  | (refine hT.ne 3 4 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 3 4 (by decide) ?_); simp; done)
  | (refine hT.ne 3 5 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 3 5 (by decide) ?_); simp; done)
  | (refine hT.ne 4 5 (by decide) ?_; simp; done)
  | (refine Ne.symm (hT.ne 4 5 (by decide) ?_); simp; done))

/-- An identifier side condition: an inequality, a conjunction of them, or
non-membership in a list. -/
macro "nscr" : tactic => `(tactic| first
  | nscr0
  | (simp only [hdTemps, cntTempsG, splitTempsG, cellTempsG, List.mem_cons, List.not_mem_nil, List.mem_append, or_false,
      not_or, List.mem_nil_iff, false_or, List.cons_append, List.nil_append];
      (repeat' apply And.intro); all_goals nscr0; done)
  | ((repeat' apply And.intro); all_goals nscr0; done))

end NautyVerified.Proofs.Refine

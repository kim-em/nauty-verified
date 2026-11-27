import NautyVerified.Build.Compile
import CompCert4Lean.Common.Behaviors
import HexGraphIso

/-!
# The dense harness: environment, input and output

The verified program is `dense_main.c` linked with nauty. It reads its input
through the external function `nv_read` and writes its output through
`nv_write` (`c/harness/nv_io.h`). This module fixes

* `xi`: the external-call environment of the end-to-end theorem. `nv_read`
  returns any `long`, recorded in the trace as a system-call event;
  `nv_write` records its argument; nothing else external is ever called;
* `Encodes G ins`: the numbers read encode the coloured graph `G`;
* `Consistent ins beh`: in the behaviour `beh`, the values `nv_read` returned
  follow `ins`, and every read of nauty's volatile `nauty_kill_request`
  returned 0 (nothing asked nauty to stop);
* `expected G`: the numbers the harness writes when nauty computes what
  HexGraphIso's search computes on `G`.
-/

namespace NautyVerified.Statement

open CompCert4Lean CompCert4Lean.Common.Events CompCert4Lean.Common.Values
open CompCert4Lean.Common.Behaviors CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open Hex.GraphIso

abbrev RString := Foundation.RocqString.Rocq.Coq.Strings.String.string

def nameRead : RString := Prototype.rocqString "nv_read"
def nameWrite : RString := Prototype.rocqString "nv_write"

/-! ## The external-call environment -/

/-- `nv_read()`: returns any value of type `long`, recorded as a system-call
event (as in CompCert's semantics of I/O functions, the event value may also
be the address of a global; `Consistent` rules that out). -/
inductive ReadStep : Senv.t → List val → Common.Memory.mem → trace → val → Common.Memory.mem → Prop
  where
  | intro (ge : Senv.t) (m : Common.Memory.mem) (ev : eventval) (v : val)
      (h : eventval_match ge ev .Tlong v) :
      ReadStep ge [] m [.Event_syscall nameRead [] ev] v m

/-- `nv_write(x)`: records `x`; the event's (ignored) result is any `int`. -/
inductive WriteStep : Senv.t → List val → Common.Memory.mem → trace → val → Common.Memory.mem → Prop
  where
  | intro (ge : Senv.t) (m : Common.Memory.mem) (x : Lib.Integers.int64) (r : Lib.Integers.int) :
      WriteStep ge [.Vlong x] m [.Event_syscall nameWrite [.EVlong x] (.EVint r)] .Vundef m

def readSem : extcall_sem := ReadStep
def writeSem : extcall_sem := WriteStep

/-- The signatures `nv_io.h` declares: `long nv_read(void)`, `void nv_write(long)`. -/
def sigRead : Common.AST.signature := { sig_args := [], sig_res := .Xlong, sig_cc := Common.AST.cc_default }
def sigWrite : Common.AST.signature :=
  { sig_args := [.Xlong], sig_res := .Xvoid, sig_cc := Common.AST.cc_default }

/-- No behaviour: a call gets stuck. -/
def noSem : extcall_sem := fun _ _ _ _ _ _ => False

/-- The external functions: `nv_read` and `nv_write` at their declared
signatures, and nothing else. -/
def extSem (name : RString) (sg : Common.AST.signature) : extcall_sem :=
  if name = nameRead ∧ sg = sigRead then readSem
  else if name = nameWrite ∧ sg = sigWrite then writeSem
  else noSem

theorem empty_properties (sg : Common.AST.signature) : extcall_properties noSem sg := by
  constructor <;> intros <;> simp_all [noSem]

theorem read_properties : extcall_properties readSem sigRead := by
  constructor
  · intro _ _ _ _ _ _ hs
    cases hs with
    | intro _ ev v h =>
      have := eventval_match_type _ _ _ _ h
      cases h <;> simp_all [sigRead, Val.has_rettype, Val.has_type]
  · intro ge1 ge2 _ _ _ _ _ heq hs
    cases hs with
    | intro _ ev v h => exact .intro _ _ _ _ (eventval_match_preserved ge1 ge2 heq.2.1 heq.1 _ _ _ h)
  · intro _ _ _ _ _ _ _ hs h; cases hs; exact h
  · intro _ _ _ _ _ _ _ _ _ hs _ h; cases hs; exact h
  · intro _ _ _ _ _ _ _ _ _ _ hs _ h _; cases hs; exact h
  · intro ge _ _ _ _ _ m1' vargs' hs hext hld
    cases hs with
    | intro _ ev v h =>
      cases hld
      exact ⟨_, m1', .intro _ _ _ _ h, .lessdef_refl _, hext,
        Common.Memory.Mem.unchanged_on_refl _ _⟩
  · intro ge1 ge2 _ _ _ _ _ f m1' vargs' hsi hs hinj hvi
    cases hs with
    | intro _ ev v h =>
      cases hvi
      obtain ⟨v2, hm2, hv2⟩ := eventval_match_inject_2 f ge1 ge2 hsi _ _ _ h
      exact ⟨f, v2, m1', .intro _ _ _ _ hm2, hv2, hinj, Common.Memory.Mem.unchanged_on_refl _ _,
        Common.Memory.Mem.unchanged_on_refl _ _, Common.Values.inject_incr_refl f,
        fun _ _ _ h1 h2 => by simp_all⟩
  · intro _ _ _ _ _ _ hs; cases hs; simp
  · intro ge _ m _ _ _ t2 hs hmt
    cases hs with
    | intro _ ev v h =>
      cases hmt with
      | match_traces_syscall _ _ _ res2 _ hv2 hty =>
        obtain ⟨v2, hm2⟩ := eventval_match_receptive ge ev _ _ res2 h
          (eventval_match_valid _ _ _ _ h) hv2 hty
        exact ⟨v2, _, .intro _ _ _ _ hm2⟩
  · intro ge _ m _ _ _ _ _ _ hs1 hs2
    cases hs1 with
    | intro _ ev1 v1 h1 =>
      cases hs2 with
      | intro _ ev2 v2 h2 =>
        refine ⟨.match_traces_syscall _ _ _ _ (eventval_match_valid _ _ _ _ h1)
          (eventval_match_valid _ _ _ _ h2) (eventval_match_same_type _ _ _ _ _ _ h1 h2),
          fun he => ?_⟩
        have he' : ev1 = ev2 := by
          injection he with h; injection h
        subst he'
        exact ⟨eventval_match_determ_1 _ _ _ _ _ h1 h2, rfl⟩

theorem write_properties : extcall_properties writeSem sigWrite := by
  constructor
  · intro _ _ _ _ _ _ hs; cases hs; simp [sigWrite, Val.has_rettype]
  · intro ge1 ge2 _ _ _ _ _ _ hs; cases hs; exact .intro _ _ _ _
  · intro _ _ _ _ _ _ _ hs h; cases hs; exact h
  · intro _ _ _ _ _ _ _ _ _ hs _ h; cases hs; exact h
  · intro _ _ _ _ _ _ _ _ _ _ hs _ h _; cases hs; exact h
  · intro ge _ _ _ _ _ m1' vargs' hs hext hld
    cases hs
    cases hld with
    | lessdef_list_cons _ _ _ _ h1 h2 =>
      cases h1; cases h2
      exact ⟨.Vundef, m1', .intro _ _ _ _, .lessdef_refl _, hext,
        Common.Memory.Mem.unchanged_on_refl _ _⟩
  · intro ge1 ge2 _ _ _ _ _ f m1' vargs' _ hs hinj hvi
    cases hs
    cases hvi with
    | inject_list_cons _ _ _ _ h1 h2 =>
      cases h1; cases h2
      exact ⟨f, .Vundef, m1', .intro _ _ _ _, .val_inject_undef _, hinj,
        Common.Memory.Mem.unchanged_on_refl _ _, Common.Memory.Mem.unchanged_on_refl _ _,
        Common.Values.inject_incr_refl f, fun _ _ _ h1 h2 => by simp_all⟩
  · intro _ _ _ _ _ _ hs; cases hs; simp
  · intro ge _ m _ _ _ t2 hs hmt
    cases hs
    cases hmt with
    | match_traces_syscall _ _ _ res2 _ _ hty =>
      cases res2 <;> simp only [eventval_type] at hty
      · exact ⟨_, _, .intro _ _ _ _⟩
      all_goals exact absurd hty (by decide)
  · intro ge _ m _ _ _ _ _ _ hs1 hs2
    cases hs1; cases hs2
    refine ⟨.match_traces_syscall _ _ _ _ trivial trivial rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- The environment of the end-to-end theorem. -/
theorem extSem_properties (name : RString) (sg : Common.AST.signature) :
    extcall_properties (extSem name sg) sg := by
  unfold extSem
  by_cases h1 : name = nameRead ∧ sg = sigRead
  · rw [ite_eq_left h1]; obtain ⟨-, rfl⟩ := h1; exact read_properties
  · rw [ite_eq_right h1]
    by_cases h2 : name = nameWrite ∧ sg = sigWrite
    · rw [ite_eq_left h2]; obtain ⟨-, rfl⟩ := h2; exact write_properties
    · rw [ite_eq_right h2]; exact empty_properties sg

def xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls where
  external := { sem := extSem, properties := extSem_properties }
  inlineAssembly := { sem := fun _ _ => noSem, properties := fun _ sg => empty_properties sg }

/-! ## Input -/

/-- The numbers `dense_main` reads encode `G`: `n`, the colour of each vertex,
the number of edges, and each edge as its two (distinct) endpoints. Every edge
of `G` appears, in either orientation, possibly more than once. -/
def Encodes {n k : Nat} (G : Colored n k) (ins : List Int) : Prop :=
  ∃ es : List (Fin n × Fin n),
    ins = [(n : Int)] ++ (List.finRange n).map (fun v => ((G.coloring.cells.get v).val : Int)) ++
      [(es.length : Int)] ++ es.flatMap (fun e => [(e.1.val : Int), (e.2.val : Int)]) ∧
    (∀ e ∈ es, e.1 ≠ e.2) ∧
    ∀ u v : Fin n, G.graph.adj u v = true ↔ ((u, v) ∈ es ∨ (v, u) ∈ es)

/-! ## Traces -/

/-- The values `nv_read` returned, in order (`none` for a result that is not an
integer). -/
def reads : trace → List (Option Int)
  | [] => []
  | .Event_syscall name [] ev :: t =>
      if name = nameRead then
        (match ev with
         | .EVlong x => some (intOfZ (Lib.Integers.Int64.signed x))
         | _ => none) :: reads t
      else reads t
  | _ :: t => reads t

/-- The values passed to `nv_write`, in order. -/
def writes : trace → List Int
  | [] => []
  | .Event_syscall name [.EVlong x] _ :: t =>
      if name = nameWrite then intOfZ (Lib.Integers.Int64.signed x) :: writes t else writes t
  | _ :: t => writes t

/-- Every volatile read in the trace returned 0. -/
def VloadsZero (t : trace) : Prop :=
  ∀ chunk id ofs ev, List.Mem (Event_vload chunk id ofs ev) (show List event from t) →
    ev = .EVint Lib.Integers.Int.zero

/-- The behaviour is consistent with the input `ins` and with nobody setting
`nauty_kill_request`: every finite part of its trace read a prefix of `ins`
and read 0 from every volatile location. -/
def Consistent (ins : List Int) : program_behavior → Prop
  | .Terminates t _ | .Diverges t | .Goes_wrong t => reads t <+: ins.map some ∧ VloadsZero t
  | .Reacts T => ∀ k, reads ((List.range k).map T) <+: ins.map some ∧
      VloadsZero ((List.range k).map T)

/-! ## Output -/

/-- nauty's setwords of a row: word `w` holds vertices `64 w .. 64 w + 63`,
most significant bit first, as a signed `long`. -/
def rowWords {n : Nat} (m : Nat) (s : Nauty.VSet n) : List Int :=
  (List.range m).map fun w =>
    (BitVec.ofNat 64 ((List.range 64).foldl
      (fun acc b => if 64 * w + b < n ∧ s.mem (64 * w + b) then acc + 2 ^ (63 - b) else acc) 0)).toInt

/-- `SETWORDSNEEDED(n)`. -/
def setwordsNeeded (n : Nat) : Nat := (n + 63) / 64

/-- The final search state of HexGraphIso's dense search on `G`. -/
def finalState {n k : Nat} (G : Colored n k) : Nauty.Search n :=
  let (lab0, cellEnds) := Nauty.initialPartition G
  (Nauty.runState n (Nauty.rowsOf G) lab0 cellEnds).2

/-- What `dense_main` writes when nauty computes what HexGraphIso computes:
each emitted generator (tag 1), the canonical labelling (2), the orbits (3),
the canonical graph's setwords (4) and the statistics (5), the last of which,
`errstatus`, is 0. -/
def expected {n k : Nat} (G : Colored n k) : List Int :=
  let r := Nauty.runColoredTraced G
  let m := setwordsNeeded n
  r.autos.toList.flatMap (fun p => 1 :: p.toList.map (fun (i : Nat) => (i : Int))) ++
  (2 :: r.result.canonlab.toList.map (fun (i : Nat) => (i : Int))) ++
  (3 :: (finalState G).orbits.toList.map (fun (i : Nat) => (i : Int))) ++
  (4 :: r.result.canong.toList.flatMap (rowWords m)) ++
  [5, (r.result.numorbits : Int), r.result.numgenerators, r.result.numnodes,
    r.result.numbadleaves, r.result.maxlevel, r.result.tctotal, r.result.canupdates, 0]

end NautyVerified.Statement

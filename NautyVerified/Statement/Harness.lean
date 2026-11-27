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

/-- `nv_read()`: returns any `long`, recorded as a system-call event. -/
inductive ReadStep : Senv.t → List val → Common.Memory.mem → trace → val → Common.Memory.mem → Prop
  where
  | intro (ge : Senv.t) (m : Common.Memory.mem) (x : Lib.Integers.int64) :
      ReadStep ge [] m [.Event_syscall nameRead [] (.EVlong x)] (.Vlong x) m

/-- `nv_write(x)`: records `x`. -/
inductive WriteStep : Senv.t → List val → Common.Memory.mem → trace → val → Common.Memory.mem → Prop
  where
  | intro (ge : Senv.t) (m : Common.Memory.mem) (x : Lib.Integers.int64) :
      WriteStep ge [.Vlong x] m [.Event_syscall nameWrite [.EVlong x] (.EVint Lib.Integers.Int.zero)]
        .Vundef m

def readSem : extcall_sem := ReadStep
def writeSem : extcall_sem := WriteStep

/-- The signatures `nv_io.h` declares: `long nv_read(void)`, `void nv_write(long)`. -/
def sigRead : Common.AST.signature := { sig_args := [], sig_res := .Xlong, sig_cc := Common.AST.cc_default }
def sigWrite : Common.AST.signature :=
  { sig_args := [.Xlong], sig_res := .Xvoid, sig_cc := Common.AST.cc_default }

/-- The external functions: `nv_read` and `nv_write` at their declared
signatures, and nothing else. -/
def extSem (name : RString) (sg : Common.AST.signature) : extcall_sem :=
  if name = nameRead ∧ sg = sigRead then readSem
  else if name = nameWrite ∧ sg = sigWrite then writeSem
  else fun _ _ _ _ _ _ => False

/-- The environment of the end-to-end theorem. -/
def xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls where
  external := { sem := extSem, properties := sorry }
  inlineAssembly := { sem := fun _ _ _ _ _ _ _ _ => False, properties := sorry }

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

/-- The values `nv_read` returned, in order. -/
def reads : trace → List Int
  | [] => []
  | .Event_syscall name [] (.EVlong x) :: t =>
      if name = nameRead then intOfZ (Lib.Integers.Int64.signed x) :: reads t else reads t
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
  | .Terminates t _ | .Diverges t | .Goes_wrong t => reads t <+: ins ∧ VloadsZero t
  | .Reacts T => ∀ k, reads ((List.range k).map T) <+: ins ∧ VloadsZero ((List.range k).map T)

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

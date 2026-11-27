import NautyVerified.Logic.Ints
import NautyVerified.Proofs.Refine.Syntax
import NautyVerified.Proofs.Graph.Rows
import NautyVerified.Proofs.Init.Tables
import NautyVerified.Proofs.Alloc.Keep
import NautyVerified.Spec.RefineFuel

/-!
# The state `refine` works in

`Loc`: where `refine`'s arguments and its three `DYNALLSTAT` arrays live.
`Ok`: the facts about them that no step changes (sizes, capacities, distinct
blocks). `Mem m L ctx st aw`: memory holds HexGraphIso's refinement state
`st` (`lab`, `ptn`, `*numcells`, the `active` words `aw`), the graph `ctx`,
the three work arrays and the tables nauty reads. `Tmp le L st`: the
temporaries hold the arguments and `st`'s `longcode`, `hint` and `maxpos`.

Every pass is specified from `Mem … st` to `Mem … st'` with
`Unch m m' L.writes`, so the passes compose without further frame
reasoning.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified.Source
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Alloc (DynAt)
open NautyVerified.Proofs.Graph (GraphAt)
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Set (BitTable)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open NautyVerified.Proofs.Init (BytecountTable)
open Hex.GraphIso.Nauty

/-- `refine`'s argument pointers, its work blocks and its scalar arguments. -/
structure Loc where
  bg : block
  gofs : ptrofs
  gw : Nat → Lib.Integers.int64
  bl : block
  lofs : ptrofs
  bp : block
  pofs : ptrofs
  bn : block
  nofs : ptrofs
  bc : block
  cofs : ptrofs
  ba : block
  aofs : ptrofs
  bk : block
  kofs : ptrofs
  /-- The `workperm`, `workset` and `bucket` blocks and capacities. -/
  bW : block
  capW : Nat
  bS : block
  capS : Nat
  bB : block
  capB : Nat
  level : Nat
  M : Nat

namespace Loc

variable (L : Loc)

abbrev lb : Int := intOfZ (Ptrofs.unsigned L.lofs)
abbrev pb : Int := intOfZ (Ptrofs.unsigned L.pofs)
abbrev nb : Int := intOfZ (Ptrofs.unsigned L.nofs)
abbrev cb : Int := intOfZ (Ptrofs.unsigned L.cofs)
abbrev ab : Int := intOfZ (Ptrofs.unsigned L.aofs)
abbrev kb : Int := intOfZ (Ptrofs.unsigned L.kofs)

/-- Every block `refine` reads or writes, the globals included. -/
def blocks : List block :=
  [L.bg, L.bl, L.bp, L.bn, L.bc, L.ba, L.bk, L.bW, L.bS, L.bB,
   Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphWorkset,
   Block.naugraphWorksetSz, Block.naugraphBucket, Block.naugraphBucketSz,
   Block.naugraphBit, Block.naugraphBytecount, Block.leftbit]

/-- The blocks a refinement pass writes. -/
def writes (z : block) : Prop :=
  z = L.bl ∨ z = L.bp ∨ z = L.bn ∨ z = L.bc ∨ z = L.ba ∨ z = L.bW ∨ z = L.bS ∨ z = L.bB

end Loc

/-- Entries `i < j` of a list of pairwise distinct blocks differ. -/
theorem pw_ne {l : List block} (h : l.Pairwise (· ≠ ·)) (i j : Nat) (hij : i < j)
    (hj : j < l.length) : l[i]'(Nat.lt_trans hij hj) ≠ l[j] := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => exact h.1 _ (List.getElem_mem _)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih h.2 i j (by omega) (by simpa using hj)

/-- The facts about `refine`'s locations that no step changes. -/
structure Ok (n : Nat) (L : Loc) : Prop where
  distinct : L.blocks.Pairwise (· ≠ ·)
  n0 : 0 < n
  nM : n ≤ 64 * L.M
  M1 : 0 < L.M
  Mlt : L.M < 33554432
  levlt : L.level < 2147483648
  capW : n ≤ L.capW
  capB : n + 2 ≤ L.capB
  nlt : n < 1073741824

/-- Memory holds the refinement state `st`, with the `active` words `aw`. -/
structure Mem {n : Nat} (m : mem) (L : Loc) (ctx : Ctx n) (st : RefineSt n)
    (aw : Nat → Lib.Integers.int64) : Prop where
  graph : GraphAt m L.bg L.gofs L.gw ctx.g L.M
  lab : ArrayAt m .Mint32 L.bl L.lb (ints st.lab) n
  ptn : ArrayAt m .Mint32 L.bp L.pb (ints st.ptn) n
  nc : ArrayAt m .Mint32 L.bn L.nb (fun _ => .Vint (ir st.numcells)) 1
  act : ArrayAt m .Mint64 L.ba L.ab (longs aw) L.M
  actRep : SetRep (fun w => bv64 (aw w)) L.M st.active
  cnt : ∃ v, ArrayAt m .Mint32 L.bc L.cb v n
  dW : DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 L.capW L.bW
  dS : DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 L.capS L.bS
  dB : DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 L.capB L.bB
  bit : BitTable m Block.naugraphBit
  bytes : BytecountTable m
  left : LeftbitTable m

/-- HexGraphIso's invariants of the state that the C needs. -/
structure StInv (n : Nat) (L : Loc) (st : RefineSt n) : Prop where
  ok : StOk n L.level st
  ptnSmall : ∀ i < n, st.ptn[i]! < 2147483648
  ncSmall : st.numcells < 2 * n
  hint : st.hint < n
  maxpos : st.maxpos < n
  code : st.longcode < 2 ^ 62

/-- The temporaries hold `refine`'s arguments and `st`'s scalars. -/
structure Tmp {n : Nat} (le : temp_env) (L : Loc) (st : RefineSt n) : Prop where
  g : PTree.get dense.id.g le = some (.Vptr L.bg L.gofs)
  lab : PTree.get dense.id.lab le = some (.Vptr L.bl L.lofs)
  ptn : PTree.get dense.id.ptn le = some (.Vptr L.bp L.pofs)
  level : PTree.get dense.id.level le = some (.Vint (ir L.level))
  numcells : PTree.get dense.id.numcells le = some (.Vptr L.bn L.nofs)
  count : PTree.get dense.id.count le = some (.Vptr L.bc L.cofs)
  active : PTree.get dense.id.active le = some (.Vptr L.ba L.aofs)
  code : PTree.get dense.id.code le = some (.Vptr L.bk L.kofs)
  m : PTree.get dense.id.m le = some (.Vint (ir L.M))
  n : PTree.get dense.id.n le = some (.Vint (ir n))
  longcode : PTree.get dense.id.longcode le = some (.Vlong (lr st.longcode))
  hint : PTree.get dense.id.hint le = some (.Vint (ir st.hint))
  maxpos : PTree.get dense.id.maxpos le = some (.Vint (ir st.maxpos))

/-- The argument temporaries, which no statement of `refine` assigns. -/
def args : List Common.AST.ident :=
  [dense.id.g, dense.id.lab, dense.id.ptn, dense.id.level, dense.id.numcells, dense.id.count,
   dense.id.active, dense.id.code, dense.id.m, dense.id.n]

/-- `Tmp` survives assignments to temporaries other than the arguments and
`longcode`, `hint`, `maxpos`. -/
theorem Tmp.temps {n : Nat} {le le' : temp_env} {L : Loc} {st : RefineSt n} (h : Tmp le L st)
    (hle : ∀ x, x ∈ args ∨ x = dense.id.longcode ∨ x = dense.id.hint ∨ x = dense.id.maxpos →
      PTree.get x le' = PTree.get x le) : Tmp le' L st where
  g := by rw [hle _ (.inl (by simp [args]))]; exact h.g
  lab := by rw [hle _ (.inl (by simp [args]))]; exact h.lab
  ptn := by rw [hle _ (.inl (by simp [args]))]; exact h.ptn
  level := by rw [hle _ (.inl (by simp [args]))]; exact h.level
  numcells := by rw [hle _ (.inl (by simp [args]))]; exact h.numcells
  count := by rw [hle _ (.inl (by simp [args]))]; exact h.count
  active := by rw [hle _ (.inl (by simp [args]))]; exact h.active
  code := by rw [hle _ (.inl (by simp [args]))]; exact h.code
  m := by rw [hle _ (.inl (by simp [args]))]; exact h.m
  n := by rw [hle _ (.inl (by simp [args]))]; exact h.n
  longcode := by rw [hle _ (.inr (.inl rfl))]; exact h.longcode
  hint := by rw [hle _ (.inr (.inr (.inl rfl)))]; exact h.hint
  maxpos := by rw [hle _ (.inr (.inr (.inr rfl)))]; exact h.maxpos

/-- Assigning a temporary that is not an argument, `longcode`, `hint` or
`maxpos` keeps `Tmp`; the side condition closes by `decide` for concrete names. -/
theorem Tmp.set {n : Nat} {le : temp_env} {L : Loc} {st : RefineSt n} (h : Tmp le L st)
    {x : Common.AST.ident} (v : val)
    (hx : x ∉ args ∧ x ≠ dense.id.longcode ∧ x ≠ dense.id.hint ∧ x ≠ dense.id.maxpos) :
    Tmp (PTree.set x v le) L st :=
  h.temps fun y hy => by
    apply temps_gso
    rintro rfl
    rcases hy with hy | hy | hy | hy
    · exact hx.1 hy
    · exact hx.2.1 hy
    · exact hx.2.2.1 hy
    · exact hx.2.2.2 hy

/-- `Mem` depends only on `st`'s `lab`, `ptn`, `numcells` and `active`. -/
theorem Mem.congr {n : Nat} {m : mem} {L : Loc} {ctx : Ctx n} {st st' : RefineSt n}
    {aw : Nat → Lib.Integers.int64} (h : Mem m L ctx st aw) (hl : st'.lab = st.lab)
    (hp : st'.ptn = st.ptn) (hn : st'.numcells = st.numcells) (ha : st'.active = st.active) :
    Mem m L ctx st' aw :=
  { h with
    lab := by rw [hl]; exact h.lab
    ptn := by rw [hp]; exact h.ptn
    nc := by rw [hn]; exact h.nc
    actRep := by rw [ha]; exact h.actRep }

/-- `Tmp` depends only on `st`'s `longcode`, `hint` and `maxpos`. -/
theorem Tmp.congr {n : Nat} {le : temp_env} {L : Loc} {st st' : RefineSt n} (h : Tmp le L st)
    (hc : st'.longcode = st.longcode) (hh : st'.hint = st.hint) (hm : st'.maxpos = st.maxpos) :
    Tmp le L st' :=
  { h with
    longcode := by rw [hc]; exact h.longcode
    hint := by rw [hh]; exact h.hint
    maxpos := by rw [hm]; exact h.maxpos }

/-- After a step: memory, temporaries and invariants all describe `st`. -/
def Done {n : Nat} (le : temp_env) (m : mem) (L : Loc) (ctx : Ctx n) (st : RefineSt n) : Prop :=
  ∃ aw, Mem m L ctx st aw ∧ Tmp le L st ∧ StInv n L st

end NautyVerified.Proofs.Refine

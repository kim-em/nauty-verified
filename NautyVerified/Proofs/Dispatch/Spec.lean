import NautyVerified.Proofs.Alloc.Keep
import NautyVerified.Logic.Ints
import NautyVerified.Logic.OfPre
import NautyVerified.Proofs.Set.Add
import NautyVerified.Proofs.Nextelement.Leftbit
import HexGraphIso.Nauty.Spec.Equivariance

/-!
# nauty's dispatch procedures, for any graph representation

`nauty()` reaches the graph only through the procedures of its `dispatch`
argument (`dispatch_graph` in naugraph.c for dense graphs, `dispatch_sparse`
in nausparse.c for sparse ones). This file states what nauty.c needs of them.

`Ops`: the HexGraphIso operations the procedures compute, over a graph type
`Gr n` and a canonical-store type `Store n` (dense: `Ctx n` and
`Array (VSet n)`; sparse: `Sparse.Graph n` and `Sparse.Rows n`).

`DispatchRep ge O`: how a linked program represents them: the procedures'
blocks, the representation of the graph (`GraphRep`) and of the canonical
store (`CanonRep m bc cofs M c samerows`: the store at `bc` holds `c`, its
first `samerows` rows meaningful), the procedures' own globals (`globs`; the
ones they write, `wglobs`; the `DYNALLSTAT` pair `wsP`/`wsS` whose block is
the search's automorphism workspace), their scratch state (`Work m`, with the
scratch blocks in use `IsWork m`) and their read-only tables (`Tables m`).

`DispatchRep.Step m m' out`: what a call of a procedure may do besides its
outputs `out`: change its globals, its scratch blocks and new blocks, leaving
its scratch state valid with every scratch block in use old or new.

`DispatchC ge O`: a `DispatchRep` whose blocks satisfy the specifications
`isautomSpec`, `testcanlabSpec`, `updatecanSpec`, `refineSpec` (both
`refine` and `refine1`, the latter for `m = 1`), `cheapautomSpec`,
`targetcellSpec`, `checkSpec` and `freedynSpec`. The dense instance is
`Dispatch/Dense.lean`'s.
-/

namespace NautyVerified.Proofs.Dispatch

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (BitTable longs)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open Hex.GraphIso.Nauty

/-- The HexGraphIso operations the dispatch procedures compute. -/
structure Ops where
  /-- The graph. -/
  Gr : Nat → Type
  /-- The canonical store. -/
  Store : Nat → Type
  /-- What the procedures need of a store on `n` vertices (dense: `n` rows). -/
  StoreOk : {n : Nat} → Store n → Prop
  refine : {n : Nat} → Gr n → Nat → Array Nat → Array Nat → VSet n → Nat → RefineSt n
  targetcell : {n : Nat} → Gr n → Array Nat → Array Nat → Nat → Nat → Int → Nat
  isautom : {n : Nat} → Gr n → Array Nat → Bool
  testcanlab : {n : Nat} → Gr n → Store n → Array Nat → Int × Nat
  updatecan : {n : Nat} → Gr n → Store n → Array Nat → Nat → Store n
  cheapautom : Array Nat → Nat → Nat → Bool

/-- Dense nauty's operations. -/
@[reducible] def denseOps : Ops where
  Gr := Ctx
  Store n := Array (VSet n)
  StoreOk {n} c := c.size = n
  refine := refine
  targetcell := targetcell
  isautom := isautom
  testcanlab := testcanlab
  updatecan := updatecan
  cheapautom := cheapautom

/-- The C types of the procedures, as nauty.c calls them. -/
abbrev isautomType : type := tfun [tptr tulong, tptr tint, tint, tint, tint] tint
abbrev testcanlabType : type := tfun [tptr tulong, tptr tulong, tptr tint, tptr tint, tint, tint] tint
abbrev updatecanType : type := tfun [tptr tulong, tptr tulong, tptr tint, tint, tint, tint] .Tvoid
abbrev refineType : type :=
  tfun [tptr tulong, tptr tint, tptr tint, tint, tptr tint, tptr tint, tptr tulong, tptr tint, tint,
    tint] .Tvoid
abbrev cheapautomType : type := tfun [tptr tint, tint, tint, tint] tint
abbrev targetcellType : type :=
  tfun [tptr tulong, tptr tint, tptr tint, tint, tint, tint, tint, tint, tint] tint
abbrev checkType : type := tfun [tint, tint, tint, tint] .Tvoid
abbrev freedynType : type := tfun [] .Tvoid

variable {ge : genv} [E : NautyEnv ge]

/-- nautil.c's and nauty.c's tables, which the procedures may read. -/
structure ETables (m : mem) : Prop where
  nautyBit : BitTable m E.nautyBit
  nautilBit : BitTable m E.nautilBit
  left : LeftbitTable m

theorem ETables.unch {m m' : mem} {W : block → Prop} (h : ETables m) (hu : Unch m m' W)
    (h1 : ¬ W E.nautyBit) (h2 : ¬ W E.nautilBit) (h3 : ¬ W E.leftbit) : ETables m' where
  nautyBit i hi := by rw [hu.load _ _ _ h1]; exact h.nautyBit i hi
  nautilBit i hi := by rw [hu.load _ _ _ h2]; exact h.nautilBit i hi
  left i hi := by rw [hu.load _ _ _ h3]; exact h.left i hi

/-- How a linked program represents the dispatch procedures and their state. -/
structure DispatchRep (ge : genv) [NautyEnv ge] (O : Ops) where
  isautom : block
  testcanlab : block
  updatecan : block
  refine : block
  refine1 : block
  cheapautom : block
  targetcell : block
  freedyn : block
  check : block
  /-- `dispatch.init`: `NULL` for dense graphs. -/
  init : val
  /-- The `DYNALLSTAT` pair holding the automorphism workspace. -/
  wsP : block
  wsS : block
  /-- The procedures' globals, and those of them they write. -/
  globs : List block
  wglobs : List block
  /-- The procedures' scratch state, and its blocks in use. -/
  Work : mem → Prop
  IsWork : mem → block → Prop
  /-- The tables the procedures read. -/
  Tables : mem → Prop
  /-- The graph `G` at `bg`, `M` words per set. -/
  GraphRep : {n : Nat} → mem → block → ptrofs → O.Gr n → Nat → Prop
  /-- The canonical store `c` at `bc`, its first `sr` rows meaningful. -/
  CanonRep : {n : Nat} → mem → block → ptrofs → Nat → O.Store n → Nat → Prop
  globs_distinct : globs.Pairwise (· ≠ ·)
  globs_env : ∀ z ∈ globs, z ∉ E.blocks
  wglobs_sub : ∀ z ∈ wglobs, z ∈ globs
  wsP_mem : wsP ∈ globs
  wsS_mem : wsS ∈ globs
  wsP_nw : wsP ∉ wglobs
  wsS_nw : wsS ∉ wglobs
  /-- A scratch block in use is valid and none of the globals. -/
  isWork_valid : ∀ {m z}, IsWork m z → Mem.valid_block m z
  isWork_globs : ∀ {m z}, Work m → IsWork m z → z ∉ globs ∧ z ∉ E.blocks
  /-- The scratch state survives a step that leaves the written globals and
  the scratch blocks in use alone. -/
  work_unch : ∀ {m m' W}, Work m → Unch m m' W → (∀ z ∈ wglobs, ¬ W z) →
    (∀ z, IsWork m z → ¬ W z) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
    Work m' ∧ ∀ z, IsWork m' z → IsWork m z
  tables_unch : ∀ {m m' W}, Tables m → Unch m m' W → (∀ z ∈ globs, z ∉ wglobs → ¬ W z) →
    Tables m'
  graph_unch : ∀ {n m m' W bg gofs} {G : O.Gr n} {M}, GraphRep m bg gofs G M → Unch m m' W →
    ¬ W bg → GraphRep m' bg gofs G M
  canon_unch : ∀ {n m m' W bc cofs M} {c : O.Store n} {sr}, CanonRep m bc cofs M c sr →
    Unch m m' W → ¬ W bc → CanonRep m' bc cofs M c sr
  /-- Fewer meaningful rows. -/
  canon_le : ∀ {n m bc cofs M} {c : O.Store n} {sr sr'}, CanonRep m bc cofs M c sr → sr' ≤ sr →
    CanonRep m bc cofs M c sr'
  graph_valid : ∀ {n m bg gofs} {G : O.Gr n} {M}, GraphRep m bg gofs G M → 0 < n → 0 < M →
    Mem.valid_block m bg
  canon_valid : ∀ {n m bc cofs M} {c : O.Store n} {sr}, CanonRep m bc cofs M c sr → 0 < n → 0 < M →
    Mem.valid_block m bc

namespace DispatchRep

variable {O : Ops} (R : DispatchRep ge O)

/-- The refinement procedure `nauty()` installs for `M` words per set. -/
def refineAt (M : Nat) : block := if M = 1 then R.refine1 else R.refine

/-- The blocks `bs` of a call's arguments: valid, pairwise distinct, none of
the procedures' globals, scratch blocks or nautil.c's and nauty.c's tables. -/
structure Sep (m : mem) (bs : List block) : Prop where
  distinct : bs.Pairwise (· ≠ ·)
  valid : ∀ z ∈ bs, Mem.valid_block m z
  notWork : ∀ z ∈ bs, ¬ R.IsWork m z
  notGlobs : ∀ z ∈ bs, z ∉ R.globs
  notTab : ∀ z ∈ bs, z ≠ E.nautyBit ∧ z ≠ E.nautilBit ∧ z ≠ E.leftbit

/-- What the state around a call of a procedure needs: its scratch state, its
tables, nautil.c's and nauty.c's tables, and the sizes. -/
structure Ctx (m : mem) (n M : Nat) : Prop where
  work : R.Work m
  tables : R.Tables m
  etables : ETables m
  n0 : 0 < n
  nlt : n < 1073741824
  M1 : 0 < M
  Mlt : M < 33554432
  nM : n ≤ 64 * M

/-- A procedure's call, besides writing the blocks `out`: it may change its
written globals, its scratch blocks in use and new blocks; afterwards its
scratch state holds again and every scratch block in use was in use before or
is new. The output blocks keep their permissions. -/
structure Step (m m' : mem) (out : block → Prop) : Prop where
  unch : Unch m m' (fun z => out z ∨ z ∈ R.wglobs ∨ R.IsWork m z ∨ ¬ Mem.valid_block m z)
  valid : ∀ z, Mem.valid_block m z → Mem.valid_block m' z
  work : R.Work m'
  mono : ∀ z, R.IsWork m' z → R.IsWork m z ∨ ¬ Mem.valid_block m z
  keep : ∀ z, out z → Mem.valid_block m z → Keep m m' z

theorem Step.refl {m : mem} (h : R.Work m) (out : block → Prop) : R.Step m m out :=
  ⟨Unch.refl _ _, fun _ h => h, h, fun _ h => .inl h, fun z _ _ => Keep.refl _ z⟩

/-- `isautom(g, perm, digraph, m, n)`: is `perm` an automorphism of `G`. -/
def isautomSpec {n : Nat} (G : O.Gr n) (bg : block) (gofs : ptrofs) (bpm : block) (pofs : ptrofs)
    (perm : Array Nat) (M : Nat) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bpm pofs, .Vint (ir 0), .Vint (ir M), .Vint (ir n)] ∧
    R.Ctx m n M ∧ R.GraphRep m bg gofs G M ∧
    ArrayAt m .Mint32 bpm (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n ∧
    (∀ x < n, perm[x]! < n) ∧ R.Sep m [bg, bpm]
  post _ m t v m' := t = E0 ∧ v = .Vint (ir (if O.isautom G perm then 1 else 0)) ∧
    R.Step m m' fun _ => False

/-- `testcanlab(g, canong, lab, &samerows, m, n)`: compare the relabelling of
`G` by `lab` with the stored canonical graph `c` (all rows meaningful). -/
def testcanlabSpec {n : Nat} (G : O.Gr n) (bg : block) (gofs : ptrofs) (c : O.Store n)
    (bc : block) (cofs : ptrofs) (bl : block) (lofs : ptrofs) (lab : Array Nat) (bs : block)
    (so : ptrofs) (M : Nat) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bc cofs, .Vptr bl lofs, .Vptr bs so, .Vint (ir M),
      .Vint (ir n)] ∧
    R.Ctx m n M ∧ R.GraphRep m bg gofs G M ∧ R.CanonRep m bc cofs M c n ∧ O.StoreOk c ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧ lab.size = n ∧
    (∀ j < n, lab[j]! < n) ∧ (∀ p < n, ∃ j < n, lab[j]! = p) ∧
    (∃ sv, ArrayAt m .Mint32 bs (intOfZ (Ptrofs.unsigned so)) sv 1) ∧ R.Sep m [bg, bc, bl, bs]
  post _ m t v m' := t = E0 ∧ v = .Vint (ir (O.testcanlab G c lab).1) ∧
    ArrayAt m' .Mint32 bs (intOfZ (Ptrofs.unsigned so))
      (fun _ => .Vint (ir ((O.testcanlab G c lab).2 : Int))) 1 ∧
    R.Step m m' (· = bs)

/-- `updatecan(g, canong, lab, samerows, m, n)`: store the relabelling of `G`
by `lab`, keeping the first `sr` rows of `c`. -/
def updatecanSpec {n : Nat} (G : O.Gr n) (bg : block) (gofs : ptrofs) (c : O.Store n)
    (bc : block) (cofs : ptrofs) (bl : block) (lofs : ptrofs) (lab : Array Nat) (sr M : Nat) :
    FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bc cofs, .Vptr bl lofs, .Vint (ir sr), .Vint (ir M),
      .Vint (ir n)] ∧
    R.Ctx m n M ∧ R.GraphRep m bg gofs G M ∧ R.CanonRep m bc cofs M c sr ∧ O.StoreOk c ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧ lab.size = n ∧
    (∀ j < n, lab[j]! < n) ∧ (∀ p < n, ∃ j < n, lab[j]! = p) ∧ sr ≤ n ∧ R.Sep m [bg, bc, bl]
  post _ m t _ m' := t = E0 ∧ R.CanonRep m' bc cofs M (O.updatecan G c lab sr) n ∧
    O.StoreOk (O.updatecan G c lab sr) ∧ R.Step m m' (· = bc)

/-- The refinement state a node starts from. -/
abbrev initSt {n : Nat} (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) : RefineSt n :=
  { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }

/-- `refine(g, lab, ptn, level, &numcells, count, active, &code, m, n)`: refine
the partition to the equitable one, writing `O.refine`'s `lab`, `ptn`,
`active`, cell count and code (`count` is scratch). -/
def refineSpec {n : Nat} (G : O.Gr n) (bg : block) (gofs : ptrofs) (bl : block) (lofs : ptrofs)
    (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat) (level : Nat) (bn : block)
    (nofs : ptrofs) (numcells : Nat) (bc : block) (cofs : ptrofs) (ba : block) (aofs : ptrofs)
    (active : VSet n) (bk : block) (kofs : ptrofs) (M : Nat) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bl lofs, .Vptr bp pofs, .Vint (ir level),
      .Vptr bn nofs, .Vptr bc cofs, .Vptr ba aofs, .Vptr bk kofs, .Vint (ir M), .Vint (ir n)] ∧
    R.Ctx m n M ∧ R.GraphRep m bg gofs G M ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧
    ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n ∧
    ArrayAt m .Mint32 bn (intOfZ (Ptrofs.unsigned nofs)) (fun _ => .Vint (ir numcells)) 1 ∧
    (∃ v, ArrayAt m .Mint32 bc (intOfZ (Ptrofs.unsigned cofs)) v n) ∧
    (∃ aw, ArrayAt m .Mint64 ba (intOfZ (Ptrofs.unsigned aofs)) (longs aw) M ∧
      SetRep (fun w => bv64 (aw w)) M active) ∧
    (∃ kv, ArrayAt m .Mint32 bk (intOfZ (Ptrofs.unsigned kofs)) kv 1) ∧
    StOk n level (initSt lab ptn active numcells) ∧ (∀ i < n, ptn[i]! < 2147483648) ∧
    numcells ≤ n ∧ level < 2147483648 ∧ R.Sep m [bg, bl, bp, bn, bc, ba, bk]
  post _ m t _ m' := t = E0 ∧
    ArrayAt m' .Mint32 bl (intOfZ (Ptrofs.unsigned lofs))
      (ints (O.refine G level lab ptn active numcells).lab) n ∧
    ArrayAt m' .Mint32 bp (intOfZ (Ptrofs.unsigned pofs))
      (ints (O.refine G level lab ptn active numcells).ptn) n ∧
    ArrayAt m' .Mint32 bn (intOfZ (Ptrofs.unsigned nofs))
      (fun _ => .Vint (ir (O.refine G level lab ptn active numcells).numcells)) 1 ∧
    (∃ v, ArrayAt m' .Mint32 bc (intOfZ (Ptrofs.unsigned cofs)) v n) ∧
    (∃ aw, ArrayAt m' .Mint64 ba (intOfZ (Ptrofs.unsigned aofs)) (longs aw) M ∧
      SetRep (fun w => bv64 (aw w)) M (O.refine G level lab ptn active numcells).active) ∧
    ArrayAt m' .Mint32 bk (intOfZ (Ptrofs.unsigned kofs))
      (fun _ => .Vint (ir (O.refine G level lab ptn active numcells).longcode)) 1 ∧
    R.Step m m' (· ∈ [bl, bp, bn, bc, ba, bk])

/-- `cheapautom(ptn, level, digraph, n)`. -/
def cheapautomSpec (bp : block) (pofs : ptrofs) (ptn : Array Nat) (level n : Nat) : FunSpec where
  pre args m := args = [.Vptr bp pofs, .Vint (ir level), .Vint (ir 0), .Vint (ir n)] ∧
    R.Work m ∧ ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n ∧
    ptn.size = n ∧ (∀ x < n, ptn[x]! < 2147483648) ∧ ptn[n - 1]! ≤ level ∧
    n < 1073741824 ∧ level < 2147483648
  post _ m t v m' := t = E0 ∧ v = .Vint (ir (if O.cheapautom ptn level n then 1 else 0)) ∧
    R.Step m m' fun _ => False

/-- `targetcell(g, lab, ptn, level, tc_level, digraph, hint, m, n)`: the
position of the target cell `O.targetcell` chooses. -/
def targetcellSpec {n : Nat} (G : O.Gr n) (bg : block) (gofs : ptrofs) (bl : block) (lofs : ptrofs)
    (lab : Array Nat) (bp : block) (pofs : ptrofs) (ptn : Array Nat) (level tcLevel : Nat)
    (dg : Lib.Integers.int) (hint : Int) (M : Nat) : FunSpec where
  pre args m := args = [.Vptr bg gofs, .Vptr bl lofs, .Vptr bp pofs, .Vint (ir level),
      .Vint (ir tcLevel), .Vint dg, .Vint (ir hint), .Vint (ir M), .Vint (ir n)] ∧
    R.Ctx m n M ∧ R.GraphRep m bg gofs G M ∧
    ArrayAt m .Mint32 bl (intOfZ (Ptrofs.unsigned lofs)) (ints lab) n ∧ (∀ j < n, lab[j]! < n) ∧
    ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints ptn) n ∧ ptn.size = n ∧
    (∀ x < n, ptn[x]! < 2147483648) ∧ ptn[n - 1]! ≤ level ∧ level < 2147483648 ∧
    hint < n ∧ -2147483648 ≤ hint ∧ tcLevel < 2147483648 ∧ R.Sep m [bg, bl, bp]
  post _ m t v m' := t = E0 ∧ v = .Vint (ir (O.targetcell G lab ptn level tcLevel hint : Int)) ∧
    R.Step m m' fun _ => False

/-- `check(WORDSIZE, m, n, NAUTYVERSIONID)` returns, changing nothing. -/
def checkSpec (mv nv : val) : FunSpec where
  pre args _ := args = [.Vint (ir 64), mv, nv, .Vint (ir 29300)]
  post _ m t _ m' := t = E0 ∧ m' = m

/-- `freedyn()`: frees the scratch blocks and the workspace (`capD` words at
`bD`), leaving the workspace pair empty. -/
def freedynSpec (capD : Nat) (bD : block) : FunSpec where
  pre args m := args = [] ∧ R.Work m ∧ DynAt m R.wsP R.wsS 8 capD bD ∧
    (0 < capD → ¬ R.IsWork m bD ∧ bD ∉ R.globs)
  post _ m t _ m' := t = E0 ∧
    Unch m m' (fun z => z ∈ R.wglobs ∨ z = R.wsP ∨ z = R.wsS ∨ R.IsWork m z ∨ (0 < capD ∧ z = bD)) ∧
    (∀ b, DynAt m' R.wsP R.wsS 8 0 b) ∧ Mem.nextblock m' = Mem.nextblock m

/-! Each procedure's block holds a function of its C type satisfying its
specification for every argument. -/

def IsautomFn (xi : ExternalCalls) (b : block) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv (.Vptr b Ptrofs.zero) = some fd ∧
    type_of_fundef fd = isautomType ∧
    ∀ {n : Nat} (G : O.Gr n) bg gofs bpm pofs perm M,
      Satisfies xi ge fd (R.isautomSpec G bg gofs bpm pofs perm M)

def TestcanlabFn (xi : ExternalCalls) (b : block) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv (.Vptr b Ptrofs.zero) = some fd ∧
    type_of_fundef fd = testcanlabType ∧
    ∀ {n : Nat} (G : O.Gr n) bg gofs c bc cofs bl lofs lab bs so M,
      Satisfies xi ge fd (R.testcanlabSpec G bg gofs c bc cofs bl lofs lab bs so M)

def UpdatecanFn (xi : ExternalCalls) (b : block) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv (.Vptr b Ptrofs.zero) = some fd ∧
    type_of_fundef fd = updatecanType ∧
    ∀ {n : Nat} (G : O.Gr n) bg gofs c bc cofs bl lofs lab sr M,
      Satisfies xi ge fd (R.updatecanSpec G bg gofs c bc cofs bl lofs lab sr M)

/-- A refinement procedure for `M` words per set. -/
def RefineFn (xi : ExternalCalls) (M : Nat) (vf : val) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv vf = some fd ∧ type_of_fundef fd = refineType ∧
    ∀ {n : Nat} (G : O.Gr n) bg gofs bl lofs lab bp pofs ptn level bn nofs numcells bc cofs ba
      aofs active bk kofs,
      Satisfies xi ge fd (R.refineSpec G bg gofs bl lofs lab bp pofs ptn level bn nofs numcells bc
        cofs ba aofs active bk kofs M)

def CheapautomFn (xi : ExternalCalls) (b : block) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv (.Vptr b Ptrofs.zero) = some fd ∧
    type_of_fundef fd = cheapautomType ∧
    ∀ bp pofs ptn level n, Satisfies xi ge fd (R.cheapautomSpec bp pofs ptn level n)

def TargetcellFn (xi : ExternalCalls) (b : block) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv (.Vptr b Ptrofs.zero) = some fd ∧
    type_of_fundef fd = targetcellType ∧
    ∀ {n : Nat} (G : O.Gr n) bg gofs bl lofs lab bp pofs ptn level tcLevel dg hint M,
      Satisfies xi ge fd (R.targetcellSpec G bg gofs bl lofs lab bp pofs ptn level tcLevel dg hint M)

def CheckFn (xi : ExternalCalls) (b : block) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv (.Vptr b Ptrofs.zero) = some fd ∧
    type_of_fundef fd = checkType ∧ ∀ mv nv, Satisfies xi ge fd (checkSpec mv nv)

def FreedynFn (xi : ExternalCalls) (b : block) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv (.Vptr b Ptrofs.zero) = some fd ∧
    type_of_fundef fd = freedynType ∧ ∀ capD bD, Satisfies xi ge fd (R.freedynSpec capD bD)

end DispatchRep

open DispatchRep in
/-- The dispatch procedures of a linked program, with their specifications. -/
structure DispatchC (ge : genv) [NautyEnv ge] (O : Ops) extends DispatchRep ge O where
  isautom_fn : ∀ xi, toDispatchRep.IsautomFn xi isautom
  testcanlab_fn : ∀ xi, toDispatchRep.TestcanlabFn xi testcanlab
  updatecan_fn : ∀ xi, toDispatchRep.UpdatecanFn xi updatecan
  /-- `refine`, and `refine1` for one word per set. -/
  refine_fn : ∀ xi M, toDispatchRep.RefineFn xi M (.Vptr (toDispatchRep.refineAt M) Ptrofs.zero)
  cheapautom_fn : ∀ xi, toDispatchRep.CheapautomFn xi cheapautom
  targetcell_fn : ∀ xi, toDispatchRep.TargetcellFn xi targetcell
  check_fn : ∀ xi, CheckFn (ge := ge) xi check
  freedyn_fn : ∀ xi, toDispatchRep.FreedynFn xi freedyn

end NautyVerified.Proofs.Dispatch

import NautyVerified.Proofs.Search.State
import NautyVerified.Statement.Harness

/-!
# Specifications of nauty.c's search functions

`Writes t l`: the trace `t` is `nv_write` events of the values `l`.
`genWords g n`: what the harness's `userautomproc` writes for a generator `g`.
`AutomCb xi b`: block `b` holds that callback.

`SFrame m m' S`: what a search function may change: the blocks of `S`, blocks
not valid before, and the naugraph.c/nautil.c work blocks in use (`IsWork`).

`firstterminalSpec`, `recoverSpec`, `processnodeSpec` state nauty.c's leaf
functions against HexGraphIso's `firstterminal`, `recover`, and
`classify` followed by `leafExit`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt)
open Hex.GraphIso.Nauty

/-- `t` is `nv_write` events of the values `l`. -/
inductive Writes : trace → List Int → Prop
  | nil : Writes [] []
  | cons (x : Lib.Integers.int64) (r : Lib.Integers.int) {t : trace} {l : List Int} :
      Writes t l →
      Writes (.Event_syscall Statement.nameWrite [.EVlong x] (.EVint r) :: t)
        (intOfZ (Lib.Integers.Int64.signed x) :: l)

theorem Writes.append {t₁ t₂ : trace} {l₁ l₂ : List Int} (h₁ : Writes t₁ l₁) (h₂ : Writes t₂ l₂) :
    Writes (t₁ ++ t₂) (l₁ ++ l₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons x r _ ih => exact .cons x r ih

/-- What the harness's `userautomproc` writes for the generator `g` on `n` points. -/
def genWords (g : Array Nat) (n : Nat) : List Int :=
  1 :: (List.range n).map fun i => ((g[i]! : Nat) : Int)

/-- The words written for a list of generators. -/
def gensWords (gs : List (Array Nat)) (n : Nat) : List Int :=
  gs.flatMap fun g => genWords g n

/-- Block `b` holds the harness's automorphism callback: called as
`(*userautomproc)(count, perm, orbits, numorbits, stabvertex, n)` with `perm`
holding `p` (entries below `2^31`), it writes `genWords p n` and changes no memory. -/
def AutomCb (xi : ExternalCalls) (b : block) : Prop :=
  ∃ fd, Genv.find_funct ge.genv_genv (.Vptr b Ptrofs.zero) = some fd ∧
    type_of_fundef fd = tfun [tint, tptr tint, tptr tint, tint, tint, tint] .Tvoid ∧
    ∀ (count : Lib.Integers.int) (bp : block) (pofs : ptrofs) (p : Array Nat) (n : Nat)
      (bo : block) (oofs : ptrofs) (no sv : Lib.Integers.int),
      Satisfies xi ge fd
        { pre := fun args m => args = [.Vint count, .Vptr bp pofs, .Vptr bo oofs, .Vint no, .Vint sv,
              .Vint (ir n)] ∧ ArrayAt m .Mint32 bp (intOfZ (Ptrofs.unsigned pofs)) (ints p) n ∧
              n < 2147483648 ∧ ∀ i < n, p[i]! < 2147483648
          post := fun _ m t _ m' => Writes t (genWords p n) ∧ m' = m }

/-- `z` is one of the naugraph.c or nautil.c work blocks in use in `m`. -/
def IsWork (m : mem) (z : block) : Prop :=
  (∃ cap, 0 < cap ∧ DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cap z) ∨
  (∃ cap, 0 < cap ∧ DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 cap z) ∨
  (∃ cap, 0 < cap ∧ DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 cap z) ∨
  (∃ cap, 0 < cap ∧ DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 cap z)

/-- What a search function may change. -/
def SFrame (m m' : mem) (S : SLoc) : Prop :=
  Unch m m' (fun z => z ∈ S.blocks ∨ ¬ Mem.valid_block m z ∨ IsWork m z) ∧
  ∀ z, Mem.valid_block m z → Mem.valid_block m' z

/-- `firstterminal(lab, level)` on the first path. -/
def firstterminalSpec {n : Nat} (S : SLoc) (ctx : Ctx n) (st : Search n) (level : Nat) : FunSpec where
  pre args m := args = [.Vptr S.bl S.lofs, .Vint (ir level)] ∧ SearchAt m S ctx st true false ∧
    1 ≤ level ∧ level ≤ n
  post _ m t _ m' := t = E0 ∧ SearchAt m' S ctx (firstterminal level st) false false ∧ SFrame m m' S

/-- `recover(ptn, level)`. -/
def recoverSpec {n : Nat} (S : SLoc) (ctx : Ctx n) (st : Search n) (level : Nat) (pre : Bool) :
    FunSpec where
  pre args m := args = [.Vptr S.bp S.pofs, .Vint (ir level)] ∧ SearchAt m S ctx st pre false ∧
    level ≤ n
  post _ m t _ m' := t = E0 ∧ SearchAt m' S ctx (Hex.GraphIso.Nauty.recover nautyInf level st) pre false ∧
    SFrame m m' S

/-- The `int` `processnode` returns for an exit, and the short-prune flag it leaves. -/
def exitValue (level : Nat) : Exit → Int × Bool
  | .done => (level, false)
  | .unwind target short => (target, short)
  | .fuel => (level, false)

/-- `processnode(lab, ptn, level, numcells)` off the first path: HexGraphIso's
`classify` then `leafExit`. nauty calls `userautomproc` exactly when it counts a
new generator, so the trace writes the leaf's permutation iff `numgenerators`
went up. (HexGraphIso's `genTrace` also records code-2 permutations that leave
the orbits unchanged, which nauty does not report.) -/
def processnodeSpec {n : Nat} (xi : ExternalCalls) (S : SLoc) (ctx : Ctx n) (st : Search n)
    (level numcells : Nat) : FunSpec where
  pre args m := args = [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level),
      .Vint (ir numcells)] ∧ SearchAt m S ctx st false false ∧ AutomCb xi S.bUA ∧
    1 ≤ level ∧ level ≤ n ∧ numcells ≤ n
  post _ m t v m' :=
    let r := leafExit (classify ctx level numcells st).1 level (classify ctx level numcells st).2
    v = .Vint (ir (exitValue level r.1).1) ∧
    SearchAt m' S ctx r.2 false (exitValue level r.1).2 ∧
    Writes t (if r.2.numgenerators = st.numgenerators + 1 then genWords r.2.workperm n else []) ∧
    SFrame m m' S

end NautyVerified.Proofs.Search

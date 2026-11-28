import NautyVerified.Proofs.Search.State
import NautyVerified.Statement.Harness

/-!
# Specifications of nauty.c's search functions

`Writes t l`: the trace `t` is `nv_write` events of the values `l`.
`genWords g n`: what the harness's `userautomproc` writes for a generator `g`.
`AutomCb xi b`: block `b` holds that callback.

`SFrame m m' S`: what a search function may change: the blocks of `S` other
than the callback's and `tcnode0` (`SLoc.Chg`), blocks not valid before, and the naugraph.c/nautil.c work blocks in use (`IsWork`).

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
holding `p` (entries below `2^31`), it writes `genWords p n` and changes no memory.
The environment `ge` is the one `NautyEnv` fixes. -/
def AutomCb {ge : genv} [NautyEnv ge] (xi : ExternalCalls) (b : block) : Prop :=
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
  Unch m m' (fun z => S.Chg z ∨ ¬ Mem.valid_block m z ∨ IsWork m z) ∧
  ∀ z, Mem.valid_block m z → Mem.valid_block m' z

/-- `firstterminal(lab, level)` on the first path. -/
def firstterminalSpec {n : Nat} (S : SLoc) (ctx : Ctx n) (st : Search n) (level : Nat) : FunSpec where
  pre args m := args = [.Vptr S.bl S.lofs, .Vint (ir level)] ∧ SearchAt m S ctx st true false ∧
    1 ≤ level ∧ level ≤ n
  post _ m t _ m' := t = E0 ∧ SearchAt m' S ctx (firstterminal level st) false false ∧ SFrame m m' S ∧
    ∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z

/-- `recover(ptn, level)`. -/
def recoverSpec {n : Nat} (S : SLoc) (ctx : Ctx n) (st : Search n) (level : Nat) (pre : Bool) :
    FunSpec where
  pre args m := args = [.Vptr S.bp S.pofs, .Vint (ir level)] ∧ SearchAt m S ctx st pre false ∧
    1 ≤ level ∧ level ≤ n
  post _ m t _ m' := t = E0 ∧ SearchAt m' S ctx (Hex.GraphIso.Nauty.recover nautyInf level st) pre false ∧
    SFrame m m' S ∧ ∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z

/-- The `int` `processnode` returns for an exit, and the short-prune flag it leaves. -/
def exitValue (level : Nat) : Exit → Int × Bool
  | .done => (level, false)
  | .unwind target short => (target, short)
  | .fuel => (level, false)

/-- The HexGraphIso facts `processnode` needs beyond `SInv`: the first and best
labellings are permutations, the best leaf's code agreement is a level, the
noncheap level is at least 1 (so `fmptn` sees `ptn[n-1]` closed), and the coset
index is a vertex. -/
structure LeafOk {n : Nat} (st : Search n) : Prop where
  firstlabSmall : ∀ i < n, st.firstlab[i]! < n
  firstlabSurj : ∀ v < n, ∃ i < n, st.firstlab[i]! = v
  canonlabSmall : ∀ i < n, st.canonlab[i]! < n
  canonlabSurj : ∀ v < n, ∃ i < n, st.canonlab[i]! = v
  eqlevCanon : 0 ≤ st.eqlevCanon
  noncheaplevel : 1 ≤ st.noncheaplevel
  cosetindex : st.cosetindex < n

/-- `processnode(lab, ptn, level, numcells)` off the first path: HexGraphIso's
`classify` then `leafExit`. nauty calls `userautomproc` exactly when it counts a
new generator, so the trace writes the leaf's permutation iff `numgenerators`
went up. (HexGraphIso's `genTrace` also records code-2 permutations that leave
the orbits unchanged, which nauty does not report.) The blocks of `S` are
valid, and `userautomproc`'s has a permission at offset 0: the C compares the
pointer with `NULL`. -/
def processnodeSpec {n : Nat} (xi : ExternalCalls) (S : SLoc) (ctx : Ctx n) (st : Search n)
    (level numcells : Nat) : FunSpec where
  pre args m := args = [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level),
      .Vint (ir numcells)] ∧ SearchAt m S ctx st false false ∧ AutomCb xi S.bUA ∧
    1 ≤ level ∧ level ≤ n ∧ numcells ≤ n ∧ LeafOk st ∧ (∀ z ∈ S.blocks, Mem.valid_block m z) ∧
    Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty
  post _ m t v m' :=
    let r := leafExit (classify ctx level numcells st).1 level (classify ctx level numcells st).2
    v = .Vint (ir (exitValue level r.1).1) ∧
    SearchAt m' S ctx r.2 false (exitValue level r.1).2 ∧
    Writes t (if r.2.numgenerators = st.numgenerators + 1 then genWords r.2.workperm n else []) ∧
    SFrame m m' S ∧ (∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z)

/-! ### For any dispatch representation

The specifications above, stated over `SearchAtG D` (`State.lean`), and their
dense instances: `SFrame`, `IsWork` and the three specifications follow from
the generic ones at `denseRep` (`isWork_dense`, `SFrameG.dense`,
`firstterminalSpec_ofG`, `recoverSpec_ofG`, `processnodeSpec_ofG`). -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} (D : DispatchRep ge O)

/-- `SFrame` for `D`. -/
def SFrameG (m m' : mem) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) : Prop :=
  Unch m m' (fun z => S.ChgG D gl cl z ∨ ¬ Mem.valid_block m z ∨ IsWorkG D m z) ∧
  ∀ z, Mem.valid_block m z → Mem.valid_block m' z

/-- `firstterminalSpec` for `D`. -/
def firstterminalSpecG {n : Nat} (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (G : O.Gr n)
    (st : SearchState n (O.Canon n)) (level : Nat) : FunSpec where
  pre args m := args = [.Vptr S.bl S.lofs, .Vint (ir level)] ∧
    SearchAtG D m S gl cl G st true false ∧ 1 ≤ level ∧ level ≤ n
  post _ m t _ m' := t = E0 ∧ SearchAtG D m' S gl cl G (firstterminal level st) false false ∧
    SFrameG D m m' S gl cl ∧ ∀ z, IsWorkG D m' z → IsWorkG D m z ∨ ¬ Mem.valid_block m z

/-- `recoverSpec` for `D`. -/
def recoverSpecG {n : Nat} (S : SLoc) (gl : D.GLoc) (cl : D.CLoc) (G : O.Gr n)
    (st : SearchState n (O.Canon n)) (level : Nat) (pre : Bool) : FunSpec where
  pre args m := args = [.Vptr S.bp S.pofs, .Vint (ir level)] ∧
    SearchAtG D m S gl cl G st pre false ∧ 1 ≤ level ∧ level ≤ n
  post _ m t _ m' := t = E0 ∧
    SearchAtG D m' S gl cl G (Hex.GraphIso.Nauty.recover nautyInf level st) pre false ∧
    SFrameG D m m' S gl cl ∧ ∀ z, IsWorkG D m' z → IsWorkG D m z ∨ ¬ Mem.valid_block m z

/-- `LeafOk` for any canonical store. -/
structure LeafOkG {n : Nat} {κ : Type} (st : SearchState n κ) : Prop where
  firstlabSmall : ∀ i < n, st.firstlab[i]! < n
  firstlabSurj : ∀ v < n, ∃ i < n, st.firstlab[i]! = v
  canonlabSmall : ∀ i < n, st.canonlab[i]! < n
  canonlabSurj : ∀ v < n, ∃ i < n, st.canonlab[i]! = v
  eqlevCanon : 0 ≤ st.eqlevCanon
  noncheaplevel : 1 ≤ st.noncheaplevel
  cosetindex : st.cosetindex < n

/-- `processnodeSpec` for `D`: `O.classify`, then `leafExit`. -/
def processnodeSpecG {n : Nat} (xi : ExternalCalls) (S : SLoc) (gl : D.GLoc) (cl : D.CLoc)
    (G : O.Gr n) (st : SearchState n (O.Canon n)) (level numcells : Nat) : FunSpec where
  pre args m := args = [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level),
      .Vint (ir numcells)] ∧ SearchAtG D m S gl cl G st false false ∧ AutomCb xi S.bUA ∧
    1 ≤ level ∧ level ≤ n ∧ numcells ≤ n ∧ LeafOkG st ∧
    (∀ z ∈ S.blocksG D gl cl, Mem.valid_block m z) ∧ Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty
  post _ m t v m' :=
    let r := leafExit (O.classify G level numcells st).1 level (O.classify G level numcells st).2
    v = .Vint (ir (exitValue level r.1).1) ∧
    SearchAtG D m' S gl cl G r.2 false (exitValue level r.1).2 ∧
    Writes t (if r.2.numgenerators = st.numgenerators + 1 then genWords r.2.workperm n else []) ∧
    SFrameG D m m' S gl cl ∧ (∀ z, IsWorkG D m' z → IsWorkG D m z ∨ ¬ Mem.valid_block m z)

end Generic

section Dense

open NautyVerified.Proofs.Dispatch

theorem isWork_dense {m : mem} {z : block} : IsWorkG denseRep m z ↔ IsWork m z := by
  constructor
  · rintro (h | h)
    · rcases inUse_dense.1 h with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  · rintro (h | h | h | h)
    · exact .inl (inUse_dense.2 (.inl h))
    · exact .inl (inUse_dense.2 (.inr (.inl h)))
    · exact .inl (inUse_dense.2 (.inr (.inr h)))
    · exact .inr h

theorem SLoc.chgG_dense {S : SLoc} {z : block} : S.ChgG denseRep () () z ↔ S.Chg z :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨SLoc.mem_blocksG.1 h1, h2, h3⟩,
   fun ⟨h1, h2, h3⟩ => ⟨SLoc.mem_blocksG.2 h1, h2, h3⟩⟩

theorem SFrameG.dense {m m' : mem} {S : SLoc} (h : SFrameG denseRep m m' S () ()) :
    SFrame m m' S :=
  ⟨h.1.mono fun _ hz => by
    rcases hz with hz | hz | hz
    · exact .inl (SLoc.chgG_dense.1 hz)
    · exact .inr (.inl hz)
    · exact .inr (.inr (isWork_dense.1 hz)), h.2⟩

theorem SFrame.toG {m m' : mem} {S : SLoc} (h : SFrame m m' S) : SFrameG denseRep m m' S () () :=
  ⟨h.1.mono fun _ hz => by
    rcases hz with hz | hz | hz
    · exact .inl (SLoc.chgG_dense.2 hz)
    · exact .inr (.inl hz)
    · exact .inr (.inr (isWork_dense.2 hz)), h.2⟩

/-- `IsWork` growth at `denseRep`. -/
theorem workMonoG_dense {m m' : mem}
    (h : ∀ z, IsWorkG denseRep m' z → IsWorkG denseRep m z ∨ ¬ Mem.valid_block m z) :
    ∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z := fun z hz =>
  (h z (isWork_dense.2 hz)).imp isWork_dense.1 id

theorem LeafOk.toG {n : Nat} {st : Search n} (h : LeafOk st) : LeafOkG st := { h with }

theorem firstterminalSpec_ofG {xi : ExternalCalls} {fd : fundef} {n : Nat} {S : SLoc} {ctx : Ctx n}
    {st : Search n} {level : Nat}
    (h : Satisfies xi Program.ge fd (firstterminalSpecG denseRep S () () ctx st level)) :
    Satisfies xi Program.ge fd (firstterminalSpec S ctx st level) :=
by
  refine Satisfies.mono ?_ ?_ h
  · rintro _ _ ⟨ha, hs, h1, h2⟩; exact ⟨ha, hs.toG, h1, h2⟩
  · rintro _ _ _ _ _ ⟨_, hs, _, _⟩ ⟨ht, hs', hf, hw⟩
    exact ⟨ht, hs'.dense hs.gw, hf.dense, workMonoG_dense hw⟩

theorem recoverSpec_ofG {xi : ExternalCalls} {fd : fundef} {n : Nat} {S : SLoc} {ctx : Ctx n}
    {st : Search n} {level : Nat} {pre : Bool}
    (h : Satisfies xi Program.ge fd (recoverSpecG denseRep S () () ctx st level pre)) :
    Satisfies xi Program.ge fd (recoverSpec S ctx st level pre) :=
by
  refine Satisfies.mono ?_ ?_ h
  · rintro _ _ ⟨ha, hs, h1, h2⟩; exact ⟨ha, hs.toG, h1, h2⟩
  · rintro _ _ _ _ _ ⟨_, hs, _, _⟩ ⟨ht, hs', hf, hw⟩
    exact ⟨ht, hs'.dense hs.gw, hf.dense, workMonoG_dense hw⟩

theorem processnodeSpec_ofG {xi : ExternalCalls} {fd : fundef} {n : Nat} {S : SLoc} {ctx : Ctx n}
    {st : Search n} {level numcells : Nat}
    (h : Satisfies xi Program.ge fd (processnodeSpecG denseRep xi S () () ctx st level numcells)) :
    Satisfies xi Program.ge fd (processnodeSpec xi S ctx st level numcells) :=
by
  refine Satisfies.mono ?_ ?_ h
  · rintro _ _ ⟨ha, hs, hu, h1, h2, h3, hl, hv, hp⟩
    exact ⟨ha, hs.toG, hu, h1, h2, h3, hl.toG, fun z hz => hv z (SLoc.mem_blocksG.1 hz), hp⟩
  · rintro _ _ _ _ _ ⟨_, hs, _⟩ ⟨hv, hs', hw, hf, hm⟩
    exact ⟨hv, hs'.dense hs.gw, hw, hf.dense, workMonoG_dense hm⟩

end Dense

end NautyVerified.Proofs.Search

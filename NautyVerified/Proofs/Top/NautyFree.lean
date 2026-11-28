import NautyVerified.Proofs.Top.NautyFreedyn
import NautyVerified.Proofs.Top.NautyPost
import NautyVerified.Proofs.Top.Fields

/-!
# `nauty()`'s release stage (`tFree`)

For `n >= 320`, `nautil_freedyn()`, `(*dispatch.freedyn)()` and
`nauty_freedyn()` free every `DYNALLSTAT` array and the target-cell list;
`dispatch.cleanup` is `NULL` and `doschreier` is 0. `wp_tFreeG D` is the
stage over `SearchAtG D` (only the blocks of `FreeSetG` change); the dense
`wp_tFree` (`FreeSet`, naugraph.c's `naugraph_freedyn`) is its instance.
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt FreeD Malloced)
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

kernel_rfl type_nautilFreedyn : type_of_fundef (.Internal dense.fn.nautil_freedyn) = tfun [] .Tvoid
kernel_rfl type_naugraphFreedyn : type_of_fundef (.Internal dense.fn.naugraph_freedyn) = tfun [] .Tvoid
kernel_rfl type_nautyFreedyn : type_of_fundef (.Internal dense.fn.nauty_freedyn) = tfun [] .Tvoid

/-- The `DYNALLSTAT` globals the release resets, `alloc_m` and `tcnode0`. -/
def freeGlobals : List block :=
  [Block.nautilWorkperm, Block.nautilWorkpermSz, Block.naugraphWorkset, Block.naugraphWorksetSz,
   Block.naugraphWorkperm, Block.naugraphWorkpermSz, Block.naugraphBucket, Block.naugraphBucketSz,
   Block.naugraphDnwork, Block.naugraphDnworkSz, Block.nautyFirsttc, Block.nautyFirsttcSz,
   Block.nautyCanoncode, Block.nautyCanoncodeSz, Block.nautyFirstcode, Block.nautyFirstcodeSz,
   Block.nautyWorkperm, Block.nautyWorkpermSz, Block.nautyCanonlab, Block.nautyCanonlabSz,
   Block.nautyFirstlab, Block.nautyFirstlabSz, Block.nautyDefltwork, Block.nautyDefltworkSz,
   Block.nautyFixedpts, Block.nautyFixedptsSz, Block.nautyActive, Block.nautyActiveSz,
   Search.Block.allocM, Search.Block.tcnode0]

/-- What the release may change: those globals, the arrays' blocks, the work
blocks and the list. -/
def FreeSet (m : mem) (S : SLoc) (chain : List (block × block)) (cDW : Nat) (bDW : block)
    (z : block) : Prop :=
  z ∈ freeGlobals ∨ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws] ∨
    (0 < cDW ∧ z = bDW) ∨
    IsWork m z ∨ z ∈ flat chain

variable {xi : ExternalCalls}

/-- The body of `if (n >= 320) { … }`. -/
abbrev freeBody : statement :=
  .Ssequence
    (Set.sk (.Scall none (.Evar dense.id.«nautil_freedyn» (tfun [] .Tvoid)) []))
    (.Ssequence
      (Set.sk
        (.Sifthenelse
          (.Ebinop .One
            (.Efield (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
              dense.id.«freedyn» (tptr (tfun [] .Tvoid)))
            (.Ecast (ci 0 tint) (tptr .Tvoid)) tint)
          (Set.sk
            (.Scall none
              (.Ederef
                (.Efield (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                  dense.id.«freedyn» (tptr (tfun [] .Tvoid)))
                (tfun [] .Tvoid))
              []))
          .Sskip))
      (Set.sk (.Scall none (.Evar dense.id.«nauty_freedyn» (tfun [] .Tvoid)) [])))

theorem ne_ptr_null0 {ge : genv} {m : mem} {b : block} (t : type) (hp : Mem.perm m b (zOfInt 0) .Cur .Nonempty) :
    Cfrontend.Cop.sem_binary_operation ge.genv_cenv .One (.Vptr b Ptrofs.zero) (tptr t)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
      (tptr .Tvoid) m = some (Val.of_bool true) := by
  have hvp : Mem.valid_pointer m b (zOfInt 0) = true := (Mem.valid_pointer_nonempty_perm m b _).2 hp
  have h1 : Cfrontend.Cop.sem_binary_operation ge.genv_cenv .One (.Vptr b Ptrofs.zero) (tptr t)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
      (tptr .Tvoid) m = (Val.cmplu_bool (Mem.valid_pointer m) .Cne (.Vptr b Ptrofs.zero)
        (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))).map
        Val.of_bool := rfl
  rw [h1]
  unfold Val.cmplu_bool
  show Option.map _ (if _ && _ && (Mem.valid_pointer m b (Ptrofs.unsigned Ptrofs.zero) || _)
    then _ else _) = _
  rw [show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hvp, Bool.true_or]
  rfl

open NautyVerified.Proofs.Set (sk pv) in
open NautyVerified.Proofs.Refine (tv pi) in
/-- `tFree` after the `n >= 320` release: the `dispatch.cleanup` and Schreier tests. -/
abbrev freeTail : statement :=
  (.Ssequence
      (sk
        (.Sifthenelse
          (.Ebinop .One
            (.Efield
              (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
              dense.id.«cleanup»
              (tptr
                (tfun
                  [(tptr tulong),
                   (tptr (tptr tulong)),
                   (tptr tulong),
                   (tptr (tptr tulong)),
                   (tptr tint),
                   (tptr tint),
                   (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                   (tptr (.Tstruct dense.id.«_1024» noattr)),
                   tint,
                   tint]
                  .Tvoid)))
            (.Ecast (ci 0 tint) (tptr .Tvoid))
            tint)
          (sk
            (.Scall none
              (.Ederef
                (.Efield
                  (.Evar dense.id.«nauty:dispatch» (.Tstruct dense.id.«_1027» noattr))
                  dense.id.«cleanup»
                  (tptr
                    (tfun
                      [(tptr tulong),
                       (tptr (tptr tulong)),
                       (tptr tulong),
                       (tptr (tptr tulong)),
                       (tptr tint),
                       (tptr tint),
                       (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                       (tptr (.Tstruct dense.id.«_1024» noattr)),
                       tint,
                       tint]
                      .Tvoid)))
                (tfun
                  [(tptr tulong),
                   (tptr (tptr tulong)),
                   (tptr tulong),
                   (tptr (tptr tulong)),
                   (tptr tint),
                   (tptr tint),
                   (tptr (.Tstruct dense.id.«optionstruct» noattr)),
                   (tptr (.Tstruct dense.id.«_1024» noattr)),
                   tint,
                   tint]
                  .Tvoid))
              [(pv dense.id.«g_arg»),
               (.Eaddrof (.Evar dense.id.«nauty:g» (tptr tulong)) (tptr (tptr tulong))),
               (pv dense.id.«canong_arg»),
               (.Eaddrof (.Evar dense.id.«nauty:canong» (tptr tulong)) (tptr (tptr tulong))),
               (pi dense.id.«lab»),
               (pi dense.id.«ptn»),
               (.Etempvar dense.id.«options» (tptr (.Tstruct dense.id.«optionstruct» noattr))),
               (.Evar dense.id.«nauty:stats» (tptr (.Tstruct dense.id.«_1024» noattr))),
               (.Evar dense.id.«nauty:m» tint),
               (.Evar dense.id.«nauty:n» tint)]))
          .Sskip))
      (sk
        (.Sifthenelse
          (.Evar dense.id.«nauty:doschreier» tint)
          (.Ssequence
            (sk
              (.Scall none
                (.Evar dense.id.«freeschreier»
                  (tfun
                    [(tptr (tptr (.Tstruct dense.id.«schreierlevel» noattr))),
                     (tptr (tptr (.Tstruct dense.id.«permnodestruct» noattr)))]
                    .Tvoid))
                [(.Eaddrof
                   (.Evar dense.id.«nauty:gp» (tptr (.Tstruct dense.id.«schreierlevel» noattr)))
                   (tptr (tptr (.Tstruct dense.id.«schreierlevel» noattr)))),
                 (.Eaddrof
                   (.Evar dense.id.«nauty:gens» (tptr (.Tstruct dense.id.«permnodestruct» noattr)))
                   (tptr (tptr (.Tstruct dense.id.«permnodestruct» noattr))))]))
            (sk
              (.Sifthenelse
                (.Ebinop .Oge (.Evar dense.id.«nauty:n» tint) (ci 320 tint) tint)
                (sk (.Scall none (.Evar dense.id.«schreier_freedyn» (tfun [] .Tvoid)) []))
                .Sskip)))
          .Sskip)))

theorem tFree_eq : Nauty.tFree = .Ssequence (Set.sk Nauty.freeIf) freeTail := rfl

/-! ### For any dispatch procedures

`wp_tFreeG D`: the release over `SearchAtG D`. `nautil_freedyn` and
`nauty_freedyn` are shared (`nautilFreedyn_satisfiesG`,
`nautyFreedyn_satisfies`), `(*dispatch.freedyn)()` runs through `D`'s
`freedynSpec`, releasing the workspace pair `D.wsP`/`D.wsS`; afterwards only
the blocks of `FreeSetG` have changed (nauty.c's and nautil.c's pairs,
`alloc_m`, `tcnode0`, the arrays, the list, `D`'s written globals, workspace
pair and scratch blocks). The dense `wp_tFree` is its instance at
`Dispatch.dense`. -/

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep DispatchC)

variable {ge : genv} [E : NautyEnv ge] {O : Ops}

/-- nauty.c's nine pairs, with the capacities and blocks the search left. -/
def nautyDsG (S : SLoc) (cDW : Nat) (bDW : block) : List FreeD :=
  [⟨dense.id.«nauty:firsttc», dense.id.«nauty:firsttc_sz», E.nautyFirsttc, E.nautyFirsttcSz,
     tint, 4, S.capTC, S.bTC⟩,
   ⟨dense.id.«nauty:canoncode», dense.id.«nauty:canoncode_sz», E.nautyCanoncode,
     E.nautyCanoncodeSz, tshort, 2, S.capCC, S.bCC⟩,
   ⟨dense.id.«nauty:firstcode», dense.id.«nauty:firstcode_sz», E.nautyFirstcode,
     E.nautyFirstcodeSz, tshort, 2, S.capFC, S.bFC⟩,
   ⟨dense.id.«nauty:workperm», dense.id.«nauty:workperm_sz», E.nautyWorkperm,
     E.nautyWorkpermSz, tint, 4, S.capWP, S.bWP⟩,
   ⟨dense.id.«nauty:canonlab», dense.id.«nauty:canonlab_sz», E.nautyCanonlab,
     E.nautyCanonlabSz, tint, 4, S.capCL, S.bCL⟩,
   ⟨dense.id.«nauty:firstlab», dense.id.«nauty:firstlab_sz», E.nautyFirstlab,
     E.nautyFirstlabSz, tint, 4, S.capFL, S.bFL⟩,
   ⟨dense.id.«nauty:defltwork», dense.id.«nauty:defltwork_sz», E.nautyDefltwork,
     E.nautyDefltworkSz, tulong, 8, cDW, bDW⟩,
   ⟨dense.id.«nauty:fixedpts», dense.id.«nauty:fixedpts_sz», E.nautyFixedpts,
     E.nautyFixedptsSz, tulong, 8, S.capF, S.bF⟩,
   ⟨dense.id.«nauty:active», dense.id.«nauty:active_sz», E.nautyActive, E.nautyActiveSz,
     tulong, 8, S.capA, S.bA⟩]

/-- nauty.c's and nautil.c's `DYNALLSTAT` globals the release resets, `alloc_m` and `tcnode0`. -/
def freeGlobalsG : List block :=
  [E.nautilWorkperm, E.nautilWorkpermSz, E.nautyFirsttc, E.nautyFirsttcSz,
   E.nautyCanoncode, E.nautyCanoncodeSz, E.nautyFirstcode, E.nautyFirstcodeSz,
   E.nautyWorkperm, E.nautyWorkpermSz, E.nautyCanonlab, E.nautyCanonlabSz,
   E.nautyFirstlab, E.nautyFirstlabSz, E.nautyDefltwork, E.nautyDefltworkSz,
   E.nautyFixedpts, E.nautyFixedptsSz, E.nautyActive, E.nautyActiveSz, E.allocM, E.tcnode0]

/-- What the release may change: those globals, the arrays' blocks, `defltwork`'s
block, the scratch blocks in use, the list, and `D`'s written globals and
workspace pair. -/
def FreeSetG (D : DispatchRep ge O) (m : mem) (S : SLoc) (chain : List (block × block))
    (cDW : Nat) (bDW : block) (z : block) : Prop :=
  z ∈ (freeGlobalsG : List block) ∨ z ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC, S.bws] ∨
    (0 < cDW ∧ z = bDW) ∨ IsWorkG D m z ∨ z ∈ flat chain ∨ z ∈ D.wglobs ∨ z = D.wsP ∨ z = D.wsS

theorem nautilOkG {m : mem} {cN : Nat} {bN : block}
    (dN : DynAt m E.nautilWorkperm E.nautilWorkpermSz 4 cN bN) : FreeD.Ok m (nautilDsG cN bN) := by
  refine ⟨fun d hd => ?_, fun d hd => ?_, ?_, fun d hd hc => ?_, by simp [nautilDsG]⟩
  · simp only [nautilDsG, List.mem_singleton] at hd; subst hd
    exact ⟨E.find_nautilWorkpermSz, E.find_nautilWorkperm⟩
  · simp only [nautilDsG, List.mem_singleton] at hd; subst hd; exact dN
  · simp only [FreeD.globals, nautilDsG, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq, List.Pairwise.nil,
      and_true, false_implies, implies_true]
    env_ne
  · simp only [nautilDsG, List.mem_singleton] at hd; subst hd
    simp only [FreeD.globals, nautilDsG, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨(dN.bne hc).1, (dN.bne hc).2⟩

theorem eval_dFieldG {e : env} {le : temp_env} {m : mem} {fld : ident} {fty : type}
    {off : Int} {v : val} (hge : PTree.get dense.id.«nauty:dispatch» e = none)
    (hfld : ∀ b o, Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) fld (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (h0 : 0 ≤ off) (h1 : off < 2 ^ 32)
    (hf : FieldAt m .Mint64 E.dispatch off v) :
    Exec.evalExpr ge e le m
      (.Efield (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr)) fld (tptr fty)) =
      some v := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, E.find_dispatch, Exec.derefLoc, typeof, hfld,
    Mem.loadv, Alloc.Mptr_eq, show access_mode (tptr fty) = .By_value .Mint64 from rfl,
    show access_mode (Tstruct dense.id.«_1027» noattr) = .By_copy from rfl]
  rw [unsigned_add_off Ptrofs.zero h0 (by
    rw [show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl]; omega)]
  rw [show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl, Int.zero_add, hf.load]

section Release

variable {D : DispatchRep ge O} {m : mem} {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n}
  {st : SearchState n (O.Canon n)} {pre nsp : Bool}

/-- The globals of `nautyDsG`: list entries of `S.litG` other than nautil.c's
pair and the workspace, or `defltwork`'s pair. -/
theorem nautyDsG_globals (h : SearchAtG D m S gl cl G st pre nsp) {cDW : Nat} {bDW : block}
    {z : block} (hz : z ∈ FreeD.globals (nautyDsG S cDW bDW)) :
    (z ∈ envSearch ∧ z ≠ E.nautilWorkperm ∧ z ≠ E.nautilWorkpermSz ∧ z ≠ S.bws) ∨
      z = E.nautyDefltwork ∨ z = E.nautyDefltworkSz := by
  have hd := h.lit
  simp only [FreeD.globals, nautyDsG, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    first
    | exact .inr (.inl rfl)
    | exact .inr (.inr rfl)
    | exact .inl ⟨by simp, by sep_ne hd, by sep_ne hd, by sep_ne hd⟩

theorem nautyDsG_free {cDW : Nat} {bDW : block} {z : block}
    (hz : z ∈ FreeD.globals (nautyDsG S cDW bDW)) : z ∈ (freeGlobalsG : List block) := by
  simp only [FreeD.globals, nautyDsG, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [freeGlobalsG]

/-- The blocks of `nautyDsG` in use: the arrays (list entries of `S.litG`) or
`defltwork`'s block. -/
theorem nautyDsG_blks (h : SearchAtG D m S gl cl G st pre nsp) {cDW : Nat} {bDW : block}
    {d : FreeD} (hd' : d ∈ nautyDsG S cDW bDW) (hc : 0 < d.cap) :
    (d.blk ∈ [S.bA, S.bF, S.bWP, S.bFL, S.bCL, S.bFC, S.bCC, S.bTC] ∧ d.blk ∈ S.litG ∧
      d.blk ≠ E.nautilWorkperm ∧ d.blk ≠ E.nautilWorkpermSz ∧ d.blk ≠ S.bws ∧
      d.blk ≠ E.allocM ∧ d.blk ≠ E.tcnode0) ∨ (0 < cDW ∧ d.blk = bDW) := by
  have hd := h.lit
  simp only [nautyDsG, List.mem_cons, List.mem_nil_iff, or_false] at hd'
  rcases hd' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first
    | exact .inr ⟨hc, rfl⟩
    | exact .inl ⟨by simp, by simp [SLoc.litG], by sep_ne hd, by sep_ne hd, by sep_ne hd,
        by sep_ne hd, by sep_ne hd⟩

theorem nautyOkG (hs : SearchAtG D m S gl cl G st pre nsp) {cDW : Nat} {bDW : block}
    (hDW : DynAt m E.nautyDefltwork E.nautyDefltworkSz 8 cDW bDW)
    (hDWs : 0 < cDW → bDW ∉ S.blocksG D gl cl ∧ bDW ≠ E.nautyDefltwork ∧
      bDW ≠ E.nautyDefltworkSz)
    (hgS : ∀ z ∈ S.blocksG D gl cl, z ≠ E.nautyDefltwork ∧ z ≠ E.nautyDefltworkSz) :
    FreeD.Ok m (nautyDsG S cDW bDW) := by
  have hd := hs.lit
  have hD := hs.dyns
  have mB : ∀ z ∈ S.litG, z ∈ S.blocksG D gl cl := fun z hz => (S.litG_sub D gl cl).subset hz
  refine ⟨fun d hd' => ?_, fun d hd' => ?_, ?_, fun d hd' hc => ?_, ?_⟩
  · simp only [nautyDsG, List.mem_cons, List.mem_nil_iff, or_false] at hd'
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨E.find_nautyFirsttcSz, E.find_nautyFirsttc⟩
    · exact ⟨E.find_nautyCanoncodeSz, E.find_nautyCanoncode⟩
    · exact ⟨E.find_nautyFirstcodeSz, E.find_nautyFirstcode⟩
    · exact ⟨E.find_nautyWorkpermSz, E.find_nautyWorkperm⟩
    · exact ⟨E.find_nautyCanonlabSz, E.find_nautyCanonlab⟩
    · exact ⟨E.find_nautyFirstlabSz, E.find_nautyFirstlab⟩
    · exact ⟨E.find_nautyDefltworkSz, E.find_nautyDefltwork⟩
    · exact ⟨E.find_nautyFixedptsSz, E.find_nautyFixedpts⟩
    · exact ⟨E.find_nautyActiveSz, E.find_nautyActive⟩
  · simp only [nautyDsG, List.mem_cons, List.mem_nil_iff, or_false] at hd'
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hD.firsttc
    · exact hD.canoncode
    · exact hD.firstcode
    · exact hD.workperm
    · exact hD.canonlab
    · exact hD.firstlab
    · exact hDW
    · exact hD.fixedpts
    · exact hD.active
  · simp only [FreeD.globals, nautyDsG, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.pairwise_cons, List.mem_cons, List.mem_nil_iff,
      or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    (repeat' constructor) <;> first | env_ne | exact fun _ h => h.elim
  · intro hg
    rcases nautyDsG_blks hs hd' hc with ⟨hl, hlit, -⟩ | ⟨hc', e⟩
    · rcases nautyDsG_globals hs hg with ⟨hg', -⟩ | e | e
      · have hown : d.blk ∈ ([S.bg, S.bl, S.bp, S.bo, S.bst, S.bc, S.bws, S.bA, S.bF, S.bWP, S.bFL,
            S.bCL, S.bFC, S.bCC, S.bTC, S.bUA] : List block) := by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl ⊢
          rcases hl with h | h | h | h | h | h | h | h <;> simp [h]
        exact (List.pairwise_append.1 hd).2.2 _ hown _ hg' rfl
      · exact (hgS _ (mB _ hlit)).1 e
      · exact (hgS _ (mB _ hlit)).2 e
    · rw [e] at hg
      rcases nautyDsG_globals hs hg with ⟨hg', -⟩ | e' | e'
      · exact (hDWs hc').1 (SLoc.mem_blocksG_of D (.inr (.inr (.inr (.inr (.inl hg'))))))
      · exact (hDWs hc').2.1 e'
      · exact (hDWs hc').2.2 e'
  · simp only [nautyDsG, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    all_goals first
      | (intro h1 _ e; exact (hDWs h1).1 (by rw [e]; exact mB _ (by simp [SLoc.litG])))
      | (intro _ h1 e; exact (hDWs h1).1 (by rw [← e]; exact mB _ (by simp [SLoc.litG])))
      | (intro _ _; sep_ne hd)
      | exact ⟨fun _ _ => by sep_ne hd, fun _ h => h.elim⟩

end Release

variable {xi : ExternalCalls}

set_option maxHeartbeats 4000000 in
/-- `n >= 320`'s release, for any dispatch procedures. -/
theorem wp_freeBodyG [T : TopEnv ge] (D : DispatchC ge O) {Q : Post} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} {chain : List (block × block)} {cDW : Nat} {bDW : block}
    (hs : SearchAtG D.toDispatchRep m S gl cl G st pre nsp)
    (hTc : TcChain m S.M E.tcnode0 chain) (hTo : TcOkG D.toDispatchRep m S gl cl chain)
    (hDW : DynAt m E.nautyDefltwork E.nautyDefltworkSz 8 cDW bDW)
    (hpF : Mem.perm m D.freedyn (zOfInt 0) .Cur .Nonempty)
    (hFN : D.freedyn ≠ E.nautilWorkperm ∧ D.freedyn ≠ E.nautilWorkpermSz)
    (hgW : ∀ z, IsWorkG D.toDispatchRep m z → z ≠ E.nautyDefltwork ∧ z ≠ E.nautyDefltworkSz ∧
      z ≠ D.freedyn)
    (hDWs : 0 < cDW → bDW ∉ S.blocksG D.toDispatchRep gl cl ∧ ¬ IsWorkG D.toDispatchRep m bDW ∧
      bDW ∉ flat chain ∧ bDW ≠ E.nautyDefltwork ∧ bDW ≠ E.nautyDefltworkSz)
    (hgS : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, z ≠ E.nautyDefltwork ∧ z ≠ E.nautyDefltworkSz)
    (hgC : ∀ z ∈ flat chain, z ≠ E.nautyDefltwork ∧ z ≠ E.nautyDefltworkSz)
    (hQ : ∀ m', Unch m m' (FreeSetG D.toDispatchRep m S chain cDW bDW) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 (nEnv bI) le m') :
    Wp xi ge dense.fn.nauty freeBody Q (nEnv bI) le m := by
  have hd := hs.lit
  obtain ⟨cN, bN, dN, nN, uN⟩ := hs.work.nautil
  have mB : ∀ z ∈ S.litG, z ∈ S.blocksG D.toDispatchRep gl cl := fun z hz =>
    (S.litG_sub D.toDispatchRep gl cl).subset hz
  have mGl : ∀ z ∈ D.globs, z ∈ S.blocksG D.toDispatchRep gl cl := fun z hz =>
    SLoc.mem_blocksG_of D.toDispatchRep (.inr (.inr (.inr (.inr (.inr hz)))))
  have hPin : E.nautilWorkperm ∈ S.blocksG D.toDispatchRep gl cl := mB _ (by simp [SLoc.litG])
  have hSin : E.nautilWorkpermSz ∈ S.blocksG D.toDispatchRep gl cl := mB _ (by simp [SLoc.litG])
  have hwsS : S.bws ∈ S.blocksG D.toDispatchRep gl cl := mB _ (by simp [SLoc.litG])
  have eB : E.nautilWorkperm ∈ E.blocks ∧ E.nautilWorkpermSz ∈ E.blocks := by
    simp [NautyEnv.blocks]
  have eD : E.nautyDefltwork ∈ E.blocks ∧ E.nautyDefltworkSz ∈ E.blocks := by
    simp [NautyEnv.blocks]
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr E.nautilFreedyn Ptrofs.zero) (targs := []) (tres := .Tvoid)
    (cc := cc_default) (vargs := []) _ _ (Satisfies.grow (nautilFreedyn_satisfiesG cN bN)) rfl ?_ rfl
    (by simp [Genv.find_funct, E.funct_nautilFreedyn]) type_nautilFreedyn ⟨rfl, nautilOkG dN⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get dense.id.«nautil_freedyn» (nEnv bI) = none from rfl, E.find_nautilFreedyn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  rintro t1 v1 m1 ⟨⟨rfl, -, hu1, -⟩, hg1⟩
  simp only [seqPost, Post.after, E0_append, set_opttemp]
  have hu1' : Unch m m1 (fun z => z = E.nautilWorkpermSz ∨ z = E.nautilWorkperm ∨
      (0 < cN ∧ z = bN)) := hu1.mono fun z h => by
    simp only [FreeD.globals, nautilDsG, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.mem_nil_iff, or_false, exists_eq_left] at h
    rcases h with (h | h) | ⟨hc, h⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨hc, h⟩)
  -- what `nautil_freedyn` leaves alone
  have nW1 : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, z ≠ E.nautilWorkpermSz →
      z ≠ E.nautilWorkperm →
      ¬ (z = E.nautilWorkpermSz ∨ z = E.nautilWorkperm ∨ (0 < cN ∧ z = bN)) := by
    rintro z hz h1 h2 (h | h | ⟨hc, rfl⟩)
    · exact h1 h
    · exact h2 h
    · exact nN hc hz
  have oW1 : ∀ z, z ∉ S.blocksG D.toDispatchRep gl cl → ¬ IsWorkG D.toDispatchRep m z →
      ¬ (z = E.nautilWorkpermSz ∨ z = E.nautilWorkperm ∨ (0 < cN ∧ z = bN)) := by
    rintro z hz hw (h | h | ⟨hc, rfl⟩)
    · exact hz (h ▸ hSin)
    · exact hz (h ▸ hPin)
    · exact hw (.inr ⟨cN, hc, dN⟩)
  have gW1 : ∀ z ∈ D.globs,
      ¬ (z = E.nautilWorkpermSz ∨ z = E.nautilWorkperm ∨ (0 < cN ∧ z = bN)) := fun z hz =>
    nW1 z (mGl z hz) (fun e => D.globs_env _ hz (e ▸ eB.2)) (fun e => D.globs_env _ hz (e ▸ eB.1))
  have hw1 := D.work_unch hs.work.disp hu1' (fun z hz => gW1 z (D.wglobs_sub _ hz))
    (fun z hz => by
      rintro (h | h | ⟨hc, rfl⟩)
      · exact hs.work.notin z hz (h ▸ hSin)
      · exact hs.work.notin z hz (h ▸ hPin)
      · exact uN hc hz) hg1
  have hF1 := hs.fixed.dFreedyn.unch hu1' (nW1 _ (mB _ (by simp [SLoc.litG])) (by sep_ne hd)
    (by sep_ne hd))
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_dFieldG rfl T.field_dFreedyn (by decide) (by decide) hF1]
  simp only [Exec.evalExpr, typeof]
  rw [show Cfrontend.Cop.sem_cast (Vint (Lib.Integers.Int.repr (zOfInt 0))) tint (tptr .Tvoid) m1 =
    some (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
    from rfl]
  simp only []
  have hpF1 : Mem.perm m1 D.freedyn (zOfInt 0) .Cur .Nonempty :=
    (Alloc.Keep.unch hu1' (by
      rintro (h | h | ⟨hc, h⟩)
      · exact hFN.2 h
      · exact hFN.1 h
      · exact (hgW _ (.inr ⟨cN, hc, dN⟩)).2.2 h.symm)).perm _ _ hpF
  rw [ne_ptr_null0 _ hpF1]
  simp only []
  rw [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m1 = some true from rfl]
  simp only [ite_true]
  have dD1 := hs.dyns.workspace.keep hu1' (gW1 _ D.wsP_mem) (gW1 _ D.wsS_mem)
    (fun _ => Alloc.Keep.unch hu1' (nW1 _ hwsS (by sep_ne hd) (by sep_ne hd)))
  obtain ⟨fd, hfd, hty, hsat⟩ := D.freedyn_fn xi
  wp_step; wp_step
  refine wp_call (vf := .Vptr D.freedyn Ptrofs.zero) (targs := [])
    (tres := .Tvoid) (cc := cc_default) (vargs := []) fd _
    (Satisfies.grow (hsat S.capD S.bws)) rfl
    (Processnode.eval_dispatch rfl T.field_dFreedyn rfl (by decide) (by decide) hF1) rfl
    hfd hty
    ⟨rfl, hw1.1, dD1, fun _ => ⟨fun h => hs.work.notin _ (hw1.2 _ h) hwsS,
      hs.lit_globs _ (by simp [SLoc.litG])⟩⟩ ?_
  rintro t2 v2 m2 ⟨⟨rfl, hu2, -, -⟩, hg2⟩
  simp only [seqPost, Post.after, E0_append, set_opttemp]
  -- what the dispatch's `freedyn` leaves alone
  have nW2 : ∀ z, z ∉ D.globs → ¬ D.IsWork m z → z ≠ S.bws →
      ¬ (z ∈ D.wglobs ∨ z = D.wsP ∨ z = D.wsS ∨ D.IsWork m1 z ∨ (0 < S.capD ∧ z = S.bws)) := by
    rintro z hg hw hb (h | h | h | h | ⟨-, h⟩)
    · exact hg (D.wglobs_sub _ h)
    · exact hg (h ▸ D.wsP_mem)
    · exact hg (h ▸ D.wsS_mem)
    · exact hw (hw1.2 z h)
    · exact hb h
  have lW2 : ∀ z ∈ S.litG, z ≠ S.bws →
      ¬ (z ∈ D.wglobs ∨ z = D.wsP ∨ z = D.wsS ∨ D.IsWork m1 z ∨ (0 < S.capD ∧ z = S.bws)) :=
    fun z hz hb => nW2 z (hs.lit_globs z hz) (fun h => hs.work.notin z h (mB z hz)) hb
  have oW2 : ∀ z, z ∉ S.blocksG D.toDispatchRep gl cl → ¬ IsWorkG D.toDispatchRep m z →
      ¬ (z ∈ D.wglobs ∨ z = D.wsP ∨ z = D.wsS ∨ D.IsWork m1 z ∨ (0 < S.capD ∧ z = S.bws)) :=
    fun z hz hw => nW2 z (fun h => hz (mGl z h)) (fun h => hw (.inl h)) (fun e => hz (e ▸ hwsS))
  have dW2 : ∀ z, (z = E.nautyDefltwork ∨ z = E.nautyDefltworkSz) →
      ¬ (z = E.nautilWorkpermSz ∨ z = E.nautilWorkperm ∨ (0 < cN ∧ z = bN)) ∧
      ¬ (z ∈ D.wglobs ∨ z = D.wsP ∨ z = D.wsS ∨ D.IsWork m1 z ∨ (0 < S.capD ∧ z = S.bws)) := by
    intro z hz
    have hzS : z ∉ S.blocksG D.toDispatchRep gl cl := fun h => by
      rcases hz with rfl | rfl
      · exact (hgS _ h).1 rfl
      · exact (hgS _ h).2 rfl
    have hzW : ¬ IsWorkG D.toDispatchRep m z := fun h => by
      rcases hz with rfl | rfl
      · exact (hgW _ h).1 rfl
      · exact (hgW _ h).2.1 rfl
    exact ⟨oW1 z hzS hzW, oW2 z hzS hzW⟩
  have hfm : ∀ z ∈ flat chain, z ∉ S.blocksG D.toDispatchRep gl cl ∧ ¬ IsWorkG D.toDispatchRep m z := by
    intro z hz
    simp only [flat, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hz
    obtain ⟨p, hp, h | h⟩ := hz <;> subst h
    · exact ⟨(hTo.apart p hp).1, (hTo.apart p hp).2.2.1⟩
    · exact ⟨(hTo.apart p hp).2.1, (hTo.apart p hp).2.2.2⟩
  have ok0 := nautyOkG hs hDW (fun hc => ⟨(hDWs hc).1, (hDWs hc).2.2.2.1, (hDWs hc).2.2.2.2⟩) hgS
  have gl12 : ∀ z ∈ FreeD.globals (nautyDsG S cDW bDW),
      ¬ (z = E.nautilWorkpermSz ∨ z = E.nautilWorkperm ∨ (0 < cN ∧ z = bN)) ∧
      ¬ (z ∈ D.wglobs ∨ z = D.wsP ∨ z = D.wsS ∨ D.IsWork m1 z ∨ (0 < S.capD ∧ z = S.bws)) := by
    intro z hz
    rcases nautyDsG_globals hs hz with ⟨hl, h1, h2, h3⟩ | e | e
    · have hl' : z ∈ S.litG := by unfold SLoc.litG; exact List.mem_append_right _ hl
      exact ⟨nW1 z (mB z hl') h2 h1, lW2 z hl' h3⟩
    · exact dW2 z (.inl e)
    · exact dW2 z (.inr e)
  have bl12 : ∀ d ∈ nautyDsG S cDW bDW, 0 < d.cap →
      ¬ (d.blk = E.nautilWorkpermSz ∨ d.blk = E.nautilWorkperm ∨ (0 < cN ∧ d.blk = bN)) ∧
      ¬ (d.blk ∈ D.wglobs ∨ d.blk = D.wsP ∨ d.blk = D.wsS ∨ D.IsWork m1 d.blk ∨
        (0 < S.capD ∧ d.blk = S.bws)) := by
    intro d hd' hc
    rcases nautyDsG_blks hs hd' hc with ⟨-, hl, h1, h2, h3, -⟩ | ⟨hc', e⟩
    · exact ⟨nW1 _ (mB _ hl) h2 h1, lW2 _ hl h3⟩
    · rw [e]
      exact ⟨oW1 _ (hDWs hc').1 (hDWs hc').2.1, oW2 _ (hDWs hc').1 (hDWs hc').2.1⟩
  have ok2 := FreeD.Ok.unch' (FreeD.Ok.unch' ok0 hu1' (fun z hz => (gl12 z hz).1)
    (fun d hd' hc => (bl12 d hd' hc).1)) hu2 (fun z hz => (gl12 z hz).2)
    (fun d hd' hc => (bl12 d hd' hc).2)
  have hTl : E.tcnode0 ∈ S.litG := by simp [SLoc.litG]
  have tc12 : ∀ z ∈ tcBlocks E.tcnode0 chain,
      ¬ (z = E.nautilWorkpermSz ∨ z = E.nautilWorkperm ∨ (0 < cN ∧ z = bN)) ∧
      ¬ (z ∈ D.wglobs ∨ z = D.wsP ∨ z = D.wsS ∨ D.IsWork m1 z ∨ (0 < S.capD ∧ z = S.bws)) := by
    intro z hz
    simp only [Search.tcBlocks, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨nW1 _ (mB _ hTl) (by sep_ne hd) (by sep_ne hd), lW2 _ hTl (by sep_ne hd)⟩
    · exact ⟨oW1 z (hfm z hz).1 (hfm z hz).2, oW2 z (hfm z hz).1 (hfm z hz).2⟩
  have hT2 : TcChain m2 S.M E.tcnode0 chain :=
    TcChain.unch hu2 (TcChain.unch hu1' hTc fun z hz => (tc12 z hz).1) fun z hz => (tc12 z hz).2
  have hAl : E.allocM ∈ S.litG := by simp [SLoc.litG]
  have hA2 : Mem.valid_access m2 .Mint32 E.allocM (zOfInt 0) .Writable :=
    hu2.access _ _ _ _ (lW2 _ hAl (by sep_ne hd))
      (hu1'.access _ _ _ _ (nW1 _ (mB _ hAl) (by sep_ne hd) (by sep_ne hd))
        hs.fixed.allocM.writable)
  have gA : E.allocM ∉ FreeD.globals (nautyDsG S cDW bDW) := by
    simp only [FreeD.globals, nautyDsG, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append]
    sep_notin hd
  have gT : E.tcnode0 ∉ FreeD.globals (nautyDsG S cDW bDW) := by
    simp only [FreeD.globals, nautyDsG, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append]
    sep_notin hd
  wp_step; wp_step
  refine wp_call (vf := .Vptr E.nautyFreedyn Ptrofs.zero) (targs := []) (tres := .Tvoid)
    (cc := cc_default) (vargs := []) _ _
    (Satisfies.grow (nautyFreedyn_satisfies S.M chain (nautyDsG S cDW bDW))) rfl ?_ rfl
    (by simp [Genv.find_funct, E.funct_nautyFreedyn]) type_nautyFreedyn
    ⟨rfl, rfl, hT2, hTo.pairwise, ?_, ok2, hA2, gA, gT, ?_⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get dense.id.«nauty_freedyn» (nEnv bI) = none from rfl, E.find_nautyFreedyn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  · intro z hz
    obtain ⟨hzS, -⟩ := hfm z hz
    refine ⟨fun e => hzS (by rw [e]; exact mB _ hAl), fun e => hzS (by rw [e]; exact mB _ hTl),
      fun h => ?_, fun d hd' hc e => ?_⟩
    · rcases nautyDsG_globals hs h with ⟨hl, -⟩ | e | e
      · exact hzS (SLoc.mem_blocksG_of _ (.inr (.inr (.inr (.inr (.inl hl))))))
      · exact (hgC z hz).1 e
      · exact (hgC z hz).2 e
    · rcases nautyDsG_blks hs hd' hc with ⟨-, hl, -⟩ | ⟨hc', e'⟩
      · exact hzS (by rw [e]; exact mB _ hl)
      · exact (hDWs hc').2.2.1 (by rw [← e', ← e]; exact hz)
  · intro d hd' hc
    rcases nautyDsG_blks hs hd' hc with ⟨-, -, -, -, -, h1, h2⟩ | ⟨hc', e⟩
    · exact ⟨h1, h2⟩
    · rw [e]
      exact ⟨fun e' => (hDWs hc').1 (by rw [e']; exact mB _ hAl),
        fun e' => (hDWs hc').1 (by rw [e']; exact mB _ hTl)⟩
  · rintro t3 v3 m3 ⟨⟨rfl, -, -, -, hu3, -⟩, hg3⟩
    simp only [seqPost, Post.after, E0_append, set_opttemp]
    refine hQ m3 (((hu1'.mono fun z h => ?_).trans (hu2.mono fun z h => ?_)).trans
      (hu3.mono fun z h => ?_)) (fun z hz => hg3 _ (hg2 _ (hg1 _ hz)))
    · rcases h with rfl | rfl | ⟨hc, rfl⟩
      · exact .inl (by simp [freeGlobalsG])
      · exact .inl (by simp [freeGlobalsG])
      · exact .inr (.inr (.inr (.inl (.inr ⟨cN, hc, dN⟩))))
    · rcases h with h | rfl | rfl | h | ⟨-, rfl⟩
      · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
      · exact .inr (.inr (.inr (.inl (.inl (hw1.2 _ h)))))
      · exact .inr (.inl (by simp))
    · rcases h with h | rfl | rfl | h | ⟨d, hd', hc, rfl⟩
      · exact .inr (.inr (.inr (.inr (.inl h))))
      · exact .inl (by simp [freeGlobalsG])
      · exact .inl (by simp [freeGlobalsG])
      · exact .inl (nautyDsG_free h)
      · rcases nautyDsG_blks hs hd' hc with ⟨hl, -⟩ | ⟨hc', e⟩
        · refine .inr (.inl ?_)
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl ⊢
          rcases hl with h | h | h | h | h | h | h | h <;> simp [h]
        · exact .inr (.inr (.inl ⟨hc', e⟩))

/-- `dispatch.cleanup` is `NULL` and `doschreier` is 0. -/
theorem wp_freeTailG [T : TopEnv ge] {Q : Post} {le : temp_env} {m : mem}
    (hC : FieldAt m .Mint64 E.dispatch 80 Vnullptr)
    (hS : IntAt m E.doschreier 0) (hQ : Q.normal E0 (nEnv bI) le m) :
    Wp xi ge dense.fn.nauty freeTail Q (nEnv bI) le m := by
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_dFieldG rfl T.field_dCleanup (by decide) (by decide) hC]
  simp only [Exec.evalExpr, typeof]
  rw [show Cfrontend.Cop.sem_cast (Vint (Lib.Integers.Int.repr (zOfInt 0))) tint (tptr .Tvoid) m =
    some (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
    from rfl]
  simp only []
  rw [ne_null_null]
  simp only []
  rw [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step
  apply wp_if_eval
  rw [Search.eval_gint (e := nEnv bI) rfl E.find_doschreier hS]
  simp only [typeof, cop]
  rw [ite_eq_right (by decide)]
  apply wp_skip
  simpa using hQ

/-- `nauty()`'s release stage (`tFree`), for any dispatch procedures. -/
theorem wp_tFreeG [T : TopEnv ge] (D : DispatchC ge O) {Q : Post} {le : temp_env} {m : mem}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {pre nsp : Bool} {chain : List (block × block)} {cDW : Nat} {bDW : block}
    (hs : SearchAtG D.toDispatchRep m S gl cl G st pre nsp)
    (hTc : TcChain m S.M E.tcnode0 chain) (hTo : TcOkG D.toDispatchRep m S gl cl chain)
    (hDW : DynAt m E.nautyDefltwork E.nautyDefltworkSz 8 cDW bDW)
    (hpF : Mem.perm m D.freedyn (zOfInt 0) .Cur .Nonempty)
    (hFN : D.freedyn ≠ E.nautilWorkperm ∧ D.freedyn ≠ E.nautilWorkpermSz)
    (hgW : ∀ z, IsWorkG D.toDispatchRep m z → z ≠ E.nautyDefltwork ∧ z ≠ E.nautyDefltworkSz ∧
      z ≠ D.freedyn)
    (hDWs : 0 < cDW → bDW ∉ S.blocksG D.toDispatchRep gl cl ∧ ¬ IsWorkG D.toDispatchRep m bDW ∧
      bDW ∉ flat chain ∧ bDW ≠ E.nautyDefltwork ∧ bDW ≠ E.nautyDefltworkSz)
    (hgS : ∀ z ∈ S.blocksG D.toDispatchRep gl cl, z ≠ E.nautyDefltwork ∧ z ≠ E.nautyDefltworkSz)
    (hgC : ∀ z ∈ flat chain, z ≠ E.nautyDefltwork ∧ z ≠ E.nautyDefltworkSz)
    (hQ : ∀ m', Unch m m' (FreeSetG D.toDispatchRep m S chain cDW bDW) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 (nEnv bI) le m') :
    Wp xi ge dense.fn.nauty Nauty.tFree Q (nEnv bI) le m := by
  have hd := hs.lit
  have hnl := hs.nlt
  rw [tFree_eq]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, Search.eval_gint (e := nEnv bI) rfl E.find_n hs.fixed.nn]
  simp only [Exec.evalExpr, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 320) = ir 320 from rfl,
    ir_lt (a := n) (b := 320) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  have hfC := hs.fixed.dCleanup
  have hfS := hs.fixed.doschreier
  have nF : ∀ z ∈ [E.dispatch, E.doschreier], ¬ FreeSetG D.toDispatchRep m S chain cDW bDW z := by
    intro z hz hF
    have hzl : z ∈ S.litG := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl <;> simp [SLoc.litG]
    have hzS : z ∈ S.blocksG D.toDispatchRep gl cl := (S.litG_sub D.toDispatchRep gl cl).subset hzl
    have hzg : z ∉ D.globs := hs.lit_globs z hzl
    rcases hF with h | h | ⟨hc, rfl⟩ | h | h | h | rfl | rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl <;> exact absurd h (by simp only [freeGlobalsG]; sep_notin hd)
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl <;> exact absurd h (by sep_notin hd)
    · exact (hDWs hc).1 hzS
    · exact hs.work_not h hzS
    · simp only [flat, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at h
      obtain ⟨p, hp, h | h⟩ := h
      · exact (hTo.apart p hp).1 (h ▸ hzS)
      · exact (hTo.apart p hp).2.1 (h ▸ hzS)
    · exact hzg (D.wglobs_sub _ h)
    · exact hzg D.wsP_mem
    · exact hzg D.wsS_mem
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at nF
  by_cases h320 : n < 320
  · rw [ite_eq_right (by simp; omega)]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    exact wp_freeTailG hfC hfS (hQ m (Unch.refl _ _) fun _ h => h)
  · rw [ite_eq_left (by simp; omega)]
    refine wp_freeBodyG D hs hTc hTo hDW hpF hFN hgW hDWs hgS hgC fun m' hu hg => ?_
    simp only [seqPost, Post.after, E0_append]
    exact wp_freeTailG (hfC.unch hu nF.1) (hfS.unch hu nF.2) (hQ m' hu hg)

end Generic

/-- `nauty()`'s release stage (`tFree`). -/
theorem wp_tFree {Q : Post} {le : temp_env} {m : mem} {S : SLoc} {n : Nat} {ctx : Ctx n}
    {st : Hex.GraphIso.Nauty.Search n} {pre nsp : Bool} {chain : List (block × block)} {cDW : Nat}
    {bDW : block}
    (hs : SearchAt m S ctx st pre nsp) (_hvm : ∀ z ∈ S.blocks, Mem.valid_block m z)
    (hTc : TcChain m S.M Proofs.Search.Block.tcnode0 chain) (hTo : TcOk m S chain)
    (hDW : DynAt m Block.nautyDefltwork Block.nautyDefltworkSz 8 cDW bDW)
    (hpF : Mem.perm m Proofs.Search.Block.naugraphFreedyn (zOfInt 0) .Cur .Nonempty)
    (hgW : ∀ z, IsWork m z → z ≠ Block.nautyDefltwork ∧ z ≠ Block.nautyDefltworkSz ∧
      z ≠ Proofs.Search.Block.naugraphFreedyn)
    (hDWs : 0 < cDW → bDW ∉ S.blocks ∧ ¬ IsWork m bDW ∧ bDW ∉ flat chain ∧
      bDW ≠ Block.nautyDefltwork ∧ bDW ≠ Block.nautyDefltworkSz)
    (hgS : ∀ z ∈ S.blocks, z ≠ Block.nautyDefltwork ∧ z ≠ Block.nautyDefltworkSz)
    (hgC : ∀ z ∈ flat chain, z ≠ Block.nautyDefltwork ∧ z ≠ Block.nautyDefltworkSz)
    (hQ : ∀ m', Unch m m' (FreeSet m S chain cDW bDW) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 (nEnv bI) le m') :
    Wp xi ge dense.fn.nauty Nauty.tFree Q (nEnv bI) le m := by
  have hFG : ∀ z ∈ (freeGlobalsG : List block), z ∈ freeGlobals := by decide
  have hWG : ∀ z ∈ Dispatch.denseWGlobs, z ∈ freeGlobals := by decide
  refine wp_tFreeG NautyVerified.Proofs.Dispatch.dense hs.toG hTc
    ⟨hTo.pairwise, hTo.valid, fun p hp =>
      let ⟨a1, a2, a3, a4⟩ := hTo.apart p hp
      ⟨fun h => a1 (SLoc.mem_blocksG.1 h), fun h => a2 (SLoc.mem_blocksG.1 h),
        fun h => a3 (isWork_dense.1 h), fun h => a4 (isWork_dense.1 h)⟩⟩
    hDW hpF ⟨by decide, by decide⟩ (fun z hz => hgW z (isWork_dense.1 hz))
    (fun hc => let ⟨a, b, c, d, e⟩ := hDWs hc
      ⟨fun h => a (SLoc.mem_blocksG.1 h), fun h => b (isWork_dense.1 h), c, d, e⟩)
    (fun z hz => hgS z (SLoc.mem_blocksG.1 hz)) hgC fun m' hu hg => hQ m' (hu.mono fun z hz => ?_) hg
  rcases hz with h | h | h | h | h | h | rfl | rfl
  · exact .inl (hFG z h)
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl (isWork_dense.1 h))))
  · exact .inr (.inr (.inr (.inr h)))
  · exact .inl (hWG z h)
  · exact .inl (by decide)
  · exact .inl (by decide)

end NautyVerified.Proofs.Top

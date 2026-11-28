import NautyVerified.Proofs.Top.NautyFreedyn
import NautyVerified.Proofs.Top.NautyPost
import NautyVerified.Proofs.Top.Fields

/-!
# `nauty()`'s release stage (`tFree`)

For `n >= 320`, `nautil_freedyn()`, `(*dispatch.freedyn)()` (naugraph.c's
`naugraph_freedyn`) and `nauty_freedyn()` free every `DYNALLSTAT` array and
the target-cell list; `dispatch.cleanup` is `NULL` and `doschreier` is 0.
Afterwards only the blocks of `FreeSet` have changed.
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

/-- nauty.c's nine pairs, with the capacities and blocks the search left. -/
def nautyDs (S : SLoc) (cDW : Nat) (bDW : block) : List FreeD :=
  [⟨dense.id.«nauty:firsttc», dense.id.«nauty:firsttc_sz», Block.nautyFirsttc, Block.nautyFirsttcSz,
     tint, 4, S.capTC, S.bTC⟩,
   ⟨dense.id.«nauty:canoncode», dense.id.«nauty:canoncode_sz», Block.nautyCanoncode,
     Block.nautyCanoncodeSz, tshort, 2, S.capCC, S.bCC⟩,
   ⟨dense.id.«nauty:firstcode», dense.id.«nauty:firstcode_sz», Block.nautyFirstcode,
     Block.nautyFirstcodeSz, tshort, 2, S.capFC, S.bFC⟩,
   ⟨dense.id.«nauty:workperm», dense.id.«nauty:workperm_sz», Block.nautyWorkperm,
     Block.nautyWorkpermSz, tint, 4, S.capWP, S.bWP⟩,
   ⟨dense.id.«nauty:canonlab», dense.id.«nauty:canonlab_sz», Block.nautyCanonlab,
     Block.nautyCanonlabSz, tint, 4, S.capCL, S.bCL⟩,
   ⟨dense.id.«nauty:firstlab», dense.id.«nauty:firstlab_sz», Block.nautyFirstlab,
     Block.nautyFirstlabSz, tint, 4, S.capFL, S.bFL⟩,
   ⟨dense.id.«nauty:defltwork», dense.id.«nauty:defltwork_sz», Block.nautyDefltwork,
     Block.nautyDefltworkSz, tulong, 8, cDW, bDW⟩,
   ⟨dense.id.«nauty:fixedpts», dense.id.«nauty:fixedpts_sz», Block.nautyFixedpts,
     Block.nautyFixedptsSz, tulong, 8, S.capF, S.bF⟩,
   ⟨dense.id.«nauty:active», dense.id.«nauty:active_sz», Block.nautyActive, Block.nautyActiveSz,
     tulong, 8, S.capA, S.bA⟩]

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

theorem freeGlobals_sub {S : SLoc} {z : block} (h : z ∈ freeGlobals) :
    z ∈ S.blocks ∨ z = Block.nautyDefltwork ∨ z = Block.nautyDefltworkSz := by
  simp only [freeGlobals, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp [SLoc.blocks]

/-- A block outside `S.blocks` and not one of `defltwork`'s globals is none of `freeGlobals`. -/
theorem not_freeGlobals {S : SLoc} {z : block} (hz : z ∉ S.blocks) (h1 : z ≠ Block.nautyDefltwork)
    (h2 : z ≠ Block.nautyDefltworkSz) : z ∉ freeGlobals := fun h => by
  rcases freeGlobals_sub (S := S) h with h | h | h
  · exact hz h
  · exact h1 h
  · exact h2 h

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

theorem nautilOk {m : mem} {cN : Nat} {bN : block}
    (dN : DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 cN bN)
    (hap : 0 < cN → bN ∉ freeGlobals) : FreeD.Ok m (nautilDs cN bN) := by
  refine ⟨fun d hd => ?_, fun d hd => ?_, by simp [FreeD.globals, nautilDs]; decide, fun d hd hc => ?_,
    by simp [nautilDs]⟩
  · simp only [nautilDs, List.mem_singleton] at hd; subst hd
    exact ⟨Program.find_nautilWorkpermSz, Program.find_nautilWorkperm⟩
  · simp only [nautilDs, List.mem_singleton] at hd; subst hd; exact dN
  · simp only [nautilDs, List.mem_singleton] at hd; subst hd
    intro h
    simp only [FreeD.globals, nautilDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.mem_nil_iff, or_false] at h
    exact hap hc (by rcases h with h | h <;> simp [freeGlobals, h])

theorem ne_ptr_null0 {m : mem} {b : block} (t : type) (hp : Mem.perm m b (zOfInt 0) .Cur .Nonempty) :
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

theorem naugraphOk {m : mem} {S : SLoc} {cS cW cB cD : Nat} {bS bW bB bD : block}
    (hd : S.blocks.Pairwise (· ≠ ·)) (hbD : bD = S.bws)
    (dS : DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 cS bS)
    (dW : DynAt m Block.naugraphWorkperm Block.naugraphWorkpermSz 4 cW bW)
    (dB : DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 cB bB)
    (dD : DynAt m Block.naugraphDnwork Block.naugraphDnworkSz 8 cD bD)
    (nS : 0 < cS → bS ∉ S.blocks) (nW : 0 < cW → bW ∉ S.blocks) (nB : 0 < cB → bB ∉ S.blocks)
    (pWS : 0 < cW → 0 < cS → bW ≠ bS) (pWB : 0 < cW → 0 < cB → bW ≠ bB)
    (pSB : 0 < cS → 0 < cB → bS ≠ bB) :
    FreeD.Ok m (naugraphDs cS bS cW bW cB bB cD bD) := by
  subst hbD
  have hG : ∀ z ∈ FreeD.globals (naugraphDs cS bS cW bW cB bB cD S.bws), z ∈ S.blocks := by
    intro z hz
    simp only [FreeD.globals, naugraphDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with h|h|h|h|h|h|h|h <;> subst h <;> simp [SLoc.blocks]
  have hwsS : S.bws ∈ S.blocks := by simp [SLoc.blocks]
  refine ⟨fun d hd => ?_, fun d hd => ?_, by simp [FreeD.globals, naugraphDs]; decide,
    fun d hd hc => ?_, ?_⟩
  · simp only [naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨Program.find_naugraphWorksetSz, Program.find_naugraphWorkset⟩
    · exact ⟨Program.find_naugraphWorkpermSz, Program.find_naugraphWorkperm⟩
    · exact ⟨Program.find_naugraphBucketSz, Program.find_naugraphBucket⟩
    · exact ⟨Program.find_naugraphDnworkSz, Program.find_naugraphDnwork⟩
  · simp only [naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact dS
    · exact dW
    · exact dB
    · exact dD
  · simp only [naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact fun h => nS hc (hG _ h)
    · exact fun h => nW hc (hG _ h)
    · exact fun h => nB hc (hG _ h)
    · simp only [FreeD.globals, naugraphDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.cons_append, List.nil_append]
      sep_notin hd
  · simp only [naugraphDs, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    refine ⟨⟨fun h1 h2 => (pWS h2 h1).symm, pSB, fun h1 _ e => nS h1 (e ▸ hwsS)⟩,
      ⟨pWB, fun h1 _ e => nW h1 (e ▸ hwsS)⟩, fun h1 _ e => nB h1 (e ▸ hwsS)⟩

theorem eval_dField {e : env} {le : temp_env} {m : mem} {fld : ident} {fty : type}
    {off : Int} {v : val} (hge : PTree.get dense.id.«nauty:dispatch» e = none)
    (hfld : ∀ b o, Exec.lvalOfField ge (Tstruct dense.id.«_1027» noattr) fld (.Vptr b o) =
      some (b, Ptrofs.add o (Ptrofs.repr (zOfInt off)), .Full))
    (h0 : 0 ≤ off) (h1 : off < 2 ^ 32)
    (hf : FieldAt m .Mint64 Proofs.Search.Block.dispatch off v) :
    Exec.evalExpr ge e le m
      (.Efield (.Evar dense.id.«nauty:dispatch» (Tstruct dense.id.«_1027» noattr)) fld (tptr fty)) =
      some v := by
  simp only [Exec.evalExpr, Exec.lvalOfVar, hge, find_dispatch, Exec.derefLoc, typeof, hfld,
    Mem.loadv, Alloc.Mptr_eq, show access_mode (tptr fty) = .By_value .Mint64 from rfl,
    show access_mode (Tstruct dense.id.«_1027» noattr) = .By_copy from rfl]
  rw [unsigned_add_off Ptrofs.zero h0 (by
    rw [show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl]; omega)]
  rw [show intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 from rfl, Int.zero_add, hf.load]

theorem nautyDs_globals {S : SLoc} {cDW : Nat} {bDW : block} {z : block}
    (hz : z ∈ FreeD.globals (nautyDs S cDW bDW)) : z ∈ freeGlobals := by
  simp only [FreeD.globals, nautyDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [freeGlobals]

theorem nautyOk {m : mem} {S : SLoc} {n : Nat} {cDW : Nat} {bDW : block}
    (hd : S.blocks.Pairwise (· ≠ ·)) (hD : Dyns n m S)
    (hDW : DynAt m Block.nautyDefltwork Block.nautyDefltworkSz 8 cDW bDW)
    (hDWs : 0 < cDW → bDW ∉ S.blocks ∧ bDW ≠ Block.nautyDefltwork ∧ bDW ≠ Block.nautyDefltworkSz)
    (hgS : ∀ z ∈ S.blocks, z ≠ Block.nautyDefltwork ∧ z ≠ Block.nautyDefltworkSz) :
    FreeD.Ok m (nautyDs S cDW bDW) := by
  have gS := fun z (hz : z ∈ S.blocks) => hgS z hz
  refine ⟨fun d hd => ?_, fun d hd => ?_, by
      simp only [FreeD.globals, nautyDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.cons_append, List.nil_append]
      decide,
    fun d hd hc => ?_, ?_⟩
  · simp only [nautyDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨Program.find_nautyFirsttcSz, Program.find_nautyFirsttc⟩
    · exact ⟨Program.find_nautyCanoncodeSz, Program.find_nautyCanoncode⟩
    · exact ⟨Program.find_nautyFirstcodeSz, Program.find_nautyFirstcode⟩
    · exact ⟨Program.find_nautyWorkpermSz, Program.find_nautyWorkperm⟩
    · exact ⟨Program.find_nautyCanonlabSz, Program.find_nautyCanonlab⟩
    · exact ⟨Program.find_nautyFirstlabSz, Program.find_nautyFirstlab⟩
    · exact ⟨Program.find_nautyDefltworkSz, Program.find_nautyDefltwork⟩
    · exact ⟨Program.find_nautyFixedptsSz, Program.find_nautyFixedpts⟩
    · exact ⟨Program.find_nautyActiveSz, Program.find_nautyActive⟩
  · simp only [nautyDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hD.firsttc
    · exact hD.canoncode
    · exact hD.firstcode
    · exact hD.workperm
    · exact hD.canonlab
    · exact hD.firstlab
    · exact hDW
    · exact hD.fixedpts
    · exact hD.active
  · have hsub : ∀ z ∈ FreeD.globals (nautyDs S cDW bDW), z ∈ freeGlobals := by
      intro z hz
      simp only [FreeD.globals, nautyDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [freeGlobals]
    simp only [nautyDs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (intro h
         rcases freeGlobals_sub (S := S) (hsub _ h) with h' | h' | h' <;>
           first | exact (hDWs hc).1 h' | exact (hDWs hc).2.1 h' | exact (hDWs hc).2.2 h')
      | (simp only [FreeD.globals, nautyDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
           List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false, not_or]
         refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
           first | sep_ne hd | exact (gS _ (by simp [SLoc.blocks])).1 |
             exact (gS _ (by simp [SLoc.blocks])).2)
  · simp only [nautyDs, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    all_goals first
      | (intro _ _; sep_ne hd)
      | (intro h1 _ e; exact (hDWs h1).1 (by rw [e]; simp [SLoc.blocks]))
      | (intro _ h1 e; exact (hDWs h1).1 (by rw [← e]; simp [SLoc.blocks]))
      | exact ⟨fun _ _ => by sep_ne hd, fun _ h => h.elim⟩

set_option maxHeartbeats 4000000 in
/-- `n >= 320`'s release. -/
theorem wp_freeBody {Q : Post} {le : temp_env} {m : mem} {S : SLoc} {n : Nat} {ctx : Ctx n}
    {st : Hex.GraphIso.Nauty.Search n} {pre nsp : Bool} {chain : List (block × block)} {cDW : Nat} {bDW : block}
    (hs : SearchAt m S ctx st pre nsp) (hvm : ∀ z ∈ S.blocks, Mem.valid_block m z)
    (hTc : TcChain m S.M Proofs.Search.Block.tcnode0 chain) (hTo : TcOk m S chain)
    (hDW : DynAt m Block.nautyDefltwork Block.nautyDefltworkSz 8 cDW bDW)
    (hpF : Mem.perm m Proofs.Search.Block.naugraphFreedyn (zOfInt 0) .Cur .Nonempty)
    (hgW : ∀ z, IsWork m z → z ≠ Block.nautyDefltwork ∧ z ≠ Block.nautyDefltworkSz ∧
      z ≠ Proofs.Search.Block.naugraphFreedyn)
    (hDWs : 0 < cDW → bDW ∉ S.blocks ∧ ¬ IsWork m bDW ∧ bDW ∉ flat chain ∧
      bDW ≠ Block.nautyDefltwork ∧ bDW ≠ Block.nautyDefltworkSz)
    (hgS : ∀ z ∈ S.blocks, z ≠ Block.nautyDefltwork ∧ z ≠ Block.nautyDefltworkSz)
    (hgC : ∀ z ∈ flat chain, z ≠ Block.nautyDefltwork ∧ z ≠ Block.nautyDefltworkSz)
    (hQ : ∀ m', Unch m m' (FreeSet m S chain cDW bDW) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 (nEnv bI) le m') :
    Wp xi ge dense.fn.nauty freeBody Q (nEnv bI) le m := by
  have hd := hs.distinct
  obtain ⟨cW, bW, cS, bS, cB, bB, cN, bN, dW, dS, dB, dN, nW, nS, nB, nN, pWS, pWB, pSB, pNW,
    pNS, pNB⟩ := hs.work.arr
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.nautilFreedyn Ptrofs.zero) (targs := []) (tres := .Tvoid)
    (cc := cc_default) (vargs := []) _ _ (Satisfies.grow (nautilFreedyn_satisfies cN bN)) rfl ?_ rfl
    (by simp [Genv.find_funct, funct_nautilFreedyn]) type_nautilFreedyn ⟨rfl, nautilOk dN ?_⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get dense.id.«nautil_freedyn» (nEnv bI) = none from rfl, find_nautilFreedyn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  · intro hc
    exact not_freeGlobals (nN hc) (hgW _ (.inr (.inr (.inr ⟨cN, hc, dN⟩)))).1
      (hgW _ (.inr (.inr (.inr ⟨cN, hc, dN⟩)))).2.1
  · rintro t1 v1 m1 ⟨⟨rfl, hD1, hu1, hnb1⟩, hg1⟩
    simp only [seqPost, Post.after, E0_append, set_opttemp]
    have hu1' : Unch m m1 (fun z => z = Block.nautilWorkpermSz ∨ z = Block.nautilWorkperm ∨
        (0 < cN ∧ z = bN)) := hu1.mono fun z h => by
      simp only [FreeD.globals, nautilDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.mem_nil_iff, or_false, exists_eq_left] at h
      rcases h with (h | h) | ⟨hc, h⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨hc, h⟩)
    have nW1 : ∀ z ∈ S.blocks, z ≠ Block.nautilWorkpermSz → z ≠ Block.nautilWorkperm →
        ¬ (z = Block.nautilWorkpermSz ∨ z = Block.nautilWorkperm ∨ (0 < cN ∧ z = bN)) := by
      rintro z hz h1 h2 (h | h | ⟨hc, rfl⟩)
      · exact h1 h
      · exact h2 h
      · exact nN hc hz
    have hF1 := hs.fixed.dFreedyn.unch hu1' (nW1 _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd))
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, eval_dField rfl field_dFreedyn (by decide) (by decide) hF1]
    simp only [Exec.evalExpr, typeof]
    rw [show Cfrontend.Cop.sem_cast (Vint (Lib.Integers.Int.repr (zOfInt 0))) tint (tptr .Tvoid) m1 =
      some (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
      from rfl]
    simp only []
    have hpF1 : Mem.perm m1 Proofs.Search.Block.naugraphFreedyn (zOfInt 0) .Cur .Nonempty :=
      (Alloc.Keep.unch hu1' (by
        rintro (h | h | ⟨hc, h⟩)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact (hgW _ (.inr (.inr (.inr ⟨cN, hc, dN⟩)))).2.2 h.symm)).perm _ _ hpF
    rw [ne_ptr_null0 _ hpF1]
    simp only []
    rw [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m1 = some true from rfl]
    simp only [ite_true]
    have k1 : ∀ z, z ∉ S.blocks → (0 < cN → z ≠ bN) →
        ¬ (z = Block.nautilWorkpermSz ∨ z = Block.nautilWorkperm ∨ (0 < cN ∧ z = bN)) := by
      rintro z hz hn (h | h | ⟨hc, h⟩)
      · exact hz (h ▸ by simp [SLoc.blocks])
      · exact hz (h ▸ by simp [SLoc.blocks])
      · exact hn hc h
    have gS : ∀ z ∈ S.blocks, z ≠ Block.nautilWorkpermSz → z ≠ Block.nautilWorkperm → _ :=
      fun z hz h1 h2 => nW1 z hz h1 h2
    have dS1 := dS.keep hu1' (gS _ (by simp [SLoc.blocks]) (by decide) (by decide))
      (gS _ (by simp [SLoc.blocks]) (by decide) (by decide))
      (fun hc => Alloc.Keep.unch hu1' (k1 _ (nS hc) (fun hcN e => pNS hcN hc e.symm)))
    have dW1 := dW.keep hu1' (gS _ (by simp [SLoc.blocks]) (by decide) (by decide))
      (gS _ (by simp [SLoc.blocks]) (by decide) (by decide))
      (fun hc => Alloc.Keep.unch hu1' (k1 _ (nW hc) (fun hcN e => pNW hcN hc e.symm)))
    have dB1 := dB.keep hu1' (gS _ (by simp [SLoc.blocks]) (by decide) (by decide))
      (gS _ (by simp [SLoc.blocks]) (by decide) (by decide))
      (fun hc => Alloc.Keep.unch hu1' (k1 _ (nB hc) (fun hcN e => pNB hcN hc e.symm)))
    have dD1 := hs.dyns.workspace.keep hu1' (gS _ (by simp [SLoc.blocks]) (by decide) (by decide))
      (gS _ (by simp [SLoc.blocks]) (by decide) (by decide))
      (fun _ => Alloc.Keep.unch hu1' (gS _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd)))
    wp_step; wp_step
    refine wp_call (vf := .Vptr Proofs.Search.Block.naugraphFreedyn Ptrofs.zero) (targs := [])
      (tres := .Tvoid) (cc := cc_default) (vargs := []) _ _
      (Satisfies.grow (naugraphFreedyn_satisfies cS bS cW bW cB bB S.capD S.bws)) rfl
      (Processnode.eval_dispatch rfl field_dFreedyn rfl (by decide) (by decide) hF1) rfl
      (by simp [Genv.find_funct, funct_naugraphFreedyn]) type_naugraphFreedyn
      ⟨rfl, naugraphOk hd rfl dS1 dW1 dB1 dD1 nS nW nB pWS pWB pSB⟩ ?_
    rintro t2 v2 m2 ⟨⟨rfl, hD2, hu2, hnb2⟩, hg2⟩
    simp only [seqPost, Post.after, E0_append, set_opttemp]
    have hG2 : ∀ z ∈ FreeD.globals (naugraphDs cS bS cW bW cB bB S.capD S.bws),
        z ∈ S.blocks ∧ z ∈ freeGlobals := by
      intro z hz
      simp only [FreeD.globals, naugraphDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with h|h|h|h|h|h|h|h <;> subst h <;> simp [SLoc.blocks, freeGlobals]
    -- what the naugraph call changed
    have k2 : ∀ z, (z ∈ S.blocks → z ∉ FreeD.globals (naugraphDs cS bS cW bW cB bB S.capD S.bws) ∧
        z ≠ S.bws) → (z ∉ S.blocks → (0 < cS → z ≠ bS) ∧ (0 < cW → z ≠ bW) ∧ (0 < cB → z ≠ bB)) →
        ¬ (z ∈ FreeD.globals (naugraphDs cS bS cW bW cB bB S.capD S.bws) ∨
          ∃ d ∈ naugraphDs cS bS cW bW cB bB S.capD S.bws, 0 < d.cap ∧ z = d.blk) := by
      intro z h1 h2 h
      by_cases hz : z ∈ S.blocks
      · obtain ⟨g1, g2⟩ := h1 hz
        rcases h with h | ⟨d, hd', hc, rfl⟩
        · exact g1 h
        · simp only [naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd'
          rcases hd' with rfl | rfl | rfl | rfl
          · exact nS hc hz
          · exact nW hc hz
          · exact nB hc hz
          · exact g2 rfl
      · obtain ⟨g1, g2, g3⟩ := h2 hz
        rcases h with h | ⟨d, hd', hc, rfl⟩
        · exact hz (hG2 _ h).1
        · simp only [naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd'
          rcases hd' with rfl | rfl | rfl | rfl
          · exact g1 hc rfl
          · exact g2 hc rfl
          · exact g3 hc rfl
          · exact hz (by simp [SLoc.blocks])
    have hfm : ∀ z ∈ flat chain, z ∉ S.blocks ∧ ¬ IsWork m z := by
      intro z hz
      simp only [flat, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hz
      obtain ⟨p, hp, h | h⟩ := hz <;> subst h
      · exact ⟨(hTo.apart p hp).1, (hTo.apart p hp).2.2.1⟩
      · exact ⟨(hTo.apart p hp).2.1, (hTo.apart p hp).2.2.2⟩
    have hwk : ∀ {c : Nat} {b : block}, 0 < c → (DynAt m Block.naugraphWorkperm
        Block.naugraphWorkpermSz 4 c b ∨ DynAt m Block.naugraphWorkset Block.naugraphWorksetSz 8 c b ∨
        DynAt m Block.naugraphBucket Block.naugraphBucketSz 4 c b ∨
        DynAt m Block.nautilWorkperm Block.nautilWorkpermSz 4 c b) → IsWork m b := by
      intro c b hc h
      rcases h with h | h | h | h
      · exact .inl ⟨c, hc, h⟩
      · exact .inr (.inl ⟨c, hc, h⟩)
      · exact .inr (.inr (.inl ⟨c, hc, h⟩))
      · exact .inr (.inr (.inr ⟨c, hc, h⟩))
    -- a block apart from S, the work blocks and `defltwork`'s globals survives both calls
    have out12 : ∀ z, z ∉ S.blocks → ¬ IsWork m z →
        ¬ (z = Block.nautilWorkpermSz ∨ z = Block.nautilWorkperm ∨ (0 < cN ∧ z = bN)) ∧
        ¬ (z ∈ FreeD.globals (naugraphDs cS bS cW bW cB bB S.capD S.bws) ∨
          ∃ d ∈ naugraphDs cS bS cW bW cB bB S.capD S.bws, 0 < d.cap ∧ z = d.blk) := by
      intro z hz hw
      refine ⟨k1 z hz (fun hc e => hw (e ▸ hwk hc (.inr (.inr (.inr dN))))), k2 z (fun h => absurd h hz)
        (fun _ => ⟨fun hc e => hw (e ▸ hwk hc (.inr (.inl dS))),
          fun hc e => hw (e ▸ hwk hc (.inl dW)), fun hc e => hw (e ▸ hwk hc (.inr (.inr (.inl dB))))⟩)⟩
    -- a block of S other than the work globals and `bws` survives both calls
    have in12 : ∀ z ∈ S.blocks, z ≠ Block.nautilWorkpermSz → z ≠ Block.nautilWorkperm →
        z ∉ FreeD.globals (naugraphDs cS bS cW bW cB bB S.capD S.bws) → z ≠ S.bws →
        ¬ (z = Block.nautilWorkpermSz ∨ z = Block.nautilWorkperm ∨ (0 < cN ∧ z = bN)) ∧
        ¬ (z ∈ FreeD.globals (naugraphDs cS bS cW bW cB bB S.capD S.bws) ∨
          ∃ d ∈ naugraphDs cS bS cW bW cB bB S.capD S.bws, 0 < d.cap ∧ z = d.blk) := by
      intro z hz h1 h2 hg hb
      exact ⟨nW1 z hz h1 h2, k2 z (fun _ => ⟨hg, hb⟩) (fun h => absurd hz h)⟩
    -- the globals `nauty_freedyn` resets survive the first two calls
    have glob12 : ∀ z ∈ FreeD.globals (nautyDs S cDW bDW),
        ¬ (z = Block.nautilWorkpermSz ∨ z = Block.nautilWorkperm ∨ (0 < cN ∧ z = bN)) ∧
        ¬ (z ∈ FreeD.globals (naugraphDs cS bS cW bW cB bB S.capD S.bws) ∨
          ∃ d ∈ naugraphDs cS bS cW bW cB bB S.capD S.bws, 0 < d.cap ∧ z = d.blk) := by
      intro z hz
      simp only [FreeD.globals, nautyDs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hz
      have hDWo : ∀ z, (z = Block.nautyDefltwork ∨ z = Block.nautyDefltworkSz) → z ∉ S.blocks :=
        fun z hz' h => by rcases hz' with rfl | rfl; exact (hgS _ h).1 rfl; exact (hgS _ h).2 rfl
      have hDWw : ∀ z, (z = Block.nautyDefltwork ∨ z = Block.nautyDefltworkSz) → ¬ IsWork m z :=
        fun z hz' h => by
          rcases hz' with rfl | rfl
          · exact (hgW _ h).1 rfl
          · exact (hgW _ h).2.1 rfl
      rcases hz with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
        first
        | exact out12 _ (hDWo _ (by simp)) (hDWw _ (by simp))
        | exact in12 _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd)
            (by simp only [FreeD.globals, naugraphDs, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.cons_append, List.nil_append]; sep_notin hd) (by sep_ne hd)
    -- the blocks `nauty_freedyn` frees survive the first two calls
    have blk12 : ∀ d ∈ nautyDs S cDW bDW, 0 < d.cap →
        ¬ (d.blk = Block.nautilWorkpermSz ∨ d.blk = Block.nautilWorkperm ∨ (0 < cN ∧ d.blk = bN)) ∧
        ¬ (d.blk ∈ FreeD.globals (naugraphDs cS bS cW bW cB bB S.capD S.bws) ∨
          ∃ d' ∈ naugraphDs cS bS cW bW cB bB S.capD S.bws, 0 < d'.cap ∧ d.blk = d'.blk) := by
      intro d hd' hc
      simp only [nautyDs, List.mem_cons, List.mem_nil_iff, or_false] at hd'
      rcases hd' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        first
        | exact out12 _ (hDWs hc).1 (hDWs hc).2.1
        | exact in12 _ (by simp [SLoc.blocks]) (by sep_ne hd) (by sep_ne hd)
            (by simp only [FreeD.globals, naugraphDs, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.cons_append, List.nil_append]; sep_notin hd) (by sep_ne hd)
    have ok0 := nautyOk hd hs.dyns hDW (fun hc => ⟨(hDWs hc).1, (hDWs hc).2.2.2.1, (hDWs hc).2.2.2.2⟩) hgS
    have ok2 := FreeD.Ok.unch' (FreeD.Ok.unch' ok0 hu1' (fun z hz => (glob12 z hz).1)
      (fun d hd' hc => (blk12 d hd' hc).1)) hu2 (fun z hz => (glob12 z hz).2)
      (fun d hd' hc => (blk12 d hd' hc).2)
    have hT2 : TcChain m2 S.M Proofs.Search.Block.tcnode0 chain := by
      have hT1 := TcChain.unch hu1' hTc fun z hz => by
        simp only [Search.tcBlocks, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact (in12 _ (by simp [SLoc.blocks]) (by decide) (by decide) (by
            simp only [FreeD.globals, naugraphDs, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.cons_append, List.nil_append]; sep_notin hd) (by sep_ne hd)).1
        · exact (out12 z (hfm z hz).1 (hfm z hz).2).1
      exact TcChain.unch hu2 hT1 fun z hz => by
        simp only [Search.tcBlocks, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact (in12 _ (by simp [SLoc.blocks]) (by decide) (by decide) (by
            simp only [FreeD.globals, naugraphDs, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.cons_append, List.nil_append]; sep_notin hd) (by sep_ne hd)).2
        · exact (out12 z (hfm z hz).1 (hfm z hz).2).2
    have hA2 : Mem.valid_access m2 .Mint32 Proofs.Search.Block.allocM (zOfInt 0) .Writable := by
      have h := in12 Proofs.Search.Block.allocM (by simp [SLoc.blocks]) (by decide) (by decide) (by
            simp only [FreeD.globals, naugraphDs, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.cons_append, List.nil_append]; sep_notin hd) (by sep_ne hd)
      exact hu2.access _ _ _ _ h.2 (hu1'.access _ _ _ _ h.1 hs.fixed.allocM.writable)
    wp_step; wp_step
    refine wp_call (vf := .Vptr Block.nautyFreedyn Ptrofs.zero) (targs := []) (tres := .Tvoid)
      (cc := cc_default) (vargs := []) _ _
      (Satisfies.grow (nautyFreedyn_satisfies S.M chain (nautyDs S cDW bDW))) rfl ?_ rfl
      (by simp [Genv.find_funct, funct_nautyFreedyn]) type_nautyFreedyn
      ⟨rfl, rfl, hT2, hTo.pairwise, ?_, ok2, hA2, by simp [FreeD.globals, nautyDs]; decide,
        by simp [FreeD.globals, nautyDs]; decide, ?_⟩ ?_
    · simp only [Exec.evalExpr, Exec.lvalOfVar,
        show PTree.get dense.id.«nauty_freedyn» (nEnv bI) = none from rfl, find_nautyFreedyn,
        Exec.derefLoc, Cfrontend.Ctypes.access_mode]
    · intro z hz
      obtain ⟨hzS, -⟩ := hfm z hz
      refine ⟨fun e => hzS (by rw [e]; simp [SLoc.blocks]), fun e => hzS (by rw [e]; simp [SLoc.blocks]),
        fun h => ?_, fun d hd' hc e => ?_⟩
      · rcases freeGlobals_sub (S := S) (nautyDs_globals h) with h' | h' | h'
        · exact hzS h'
        · exact (hgC z hz).1 h'
        · exact (hgC z hz).2 h'
      · simp only [nautyDs, List.mem_cons, List.mem_nil_iff, or_false] at hd'
        rcases hd' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          first
          | (dsimp only at e hc; exact (hDWs hc).2.2.1 (by rw [← e]; exact hz))
          | exact hzS (by rw [e]; simp [SLoc.blocks])
    · intro d hd' hc
      simp only [nautyDs, List.mem_cons, List.mem_nil_iff, or_false] at hd'
      rcases hd' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        first
        | exact ⟨by sep_ne hd, by sep_ne hd⟩
        | exact ⟨fun e => (hDWs hc).1 (by dsimp only at e; rw [e]; simp [SLoc.blocks]),
            fun e => (hDWs hc).1 (by dsimp only at e; rw [e]; simp [SLoc.blocks])⟩
    · rintro t3 v3 m3 ⟨⟨rfl, -, -, -, hu3, -⟩, hg3⟩
      simp only [seqPost, Post.after, E0_append, set_opttemp]
      refine hQ m3 (((hu1'.mono fun z h => ?_).trans (hu2.mono fun z h => ?_)).trans
        (hu3.mono fun z h => ?_)) (fun z hz => hg3 _ (hg2 _ (hg1 _ hz)))
      · rcases h with rfl | rfl | ⟨hc, rfl⟩
        · exact .inl (by simp [freeGlobals])
        · exact .inl (by simp [freeGlobals])
        · exact .inr (.inr (.inr (.inl (hwk hc (.inr (.inr (.inr dN)))))))
      · rcases h with h | ⟨d, hd', hc, rfl⟩
        · exact .inl (hG2 _ h).2
        · simp only [naugraphDs, List.mem_cons, List.mem_nil_iff, or_false] at hd'
          rcases hd' with rfl | rfl | rfl | rfl
          · exact .inr (.inr (.inr (.inl (hwk hc (.inr (.inl dS))))))
          · exact .inr (.inr (.inr (.inl (hwk hc (.inl dW)))))
          · exact .inr (.inr (.inr (.inl (hwk hc (.inr (.inr (.inl dB)))))))
          · exact .inr (.inl (by simp))
      · rcases h with h | rfl | rfl | h | ⟨d, hd', hc, rfl⟩
        · exact .inr (.inr (.inr (.inr h)))
        · exact .inl (by simp [freeGlobals])
        · exact .inl (by simp [freeGlobals])
        · exact .inl (nautyDs_globals h)
        · simp only [nautyDs, List.mem_cons, List.mem_nil_iff, or_false] at hd'
          rcases hd' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            first
            | exact .inr (.inr (.inl ⟨hc, rfl⟩))
            | exact .inr (.inl (by simp))

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

/-- `dispatch.cleanup` is `NULL` and `doschreier` is 0. -/
theorem wp_freeTail {Q : Post} {le : temp_env} {m : mem}
    (hC : FieldAt m .Mint64 Proofs.Search.Block.dispatch 80 Vnullptr)
    (hS : IntAt m Proofs.Search.Block.doschreier 0) (hQ : Q.normal E0 (nEnv bI) le m) :
    Wp xi ge dense.fn.nauty freeTail Q (nEnv bI) le m := by
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_dField rfl field_dCleanup (by decide) (by decide) hC]
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
  rw [Search.eval_gint (e := nEnv bI) rfl find_doschreier hS]
  simp only [typeof, cop]
  rw [ite_eq_right (by decide)]
  apply wp_skip
  simpa using hQ

/-- `nauty()`'s release stage (`tFree`). -/
theorem wp_tFree {Q : Post} {le : temp_env} {m : mem} {S : SLoc} {n : Nat} {ctx : Ctx n}
    {st : Hex.GraphIso.Nauty.Search n} {pre nsp : Bool} {chain : List (block × block)} {cDW : Nat}
    {bDW : block}
    (hs : SearchAt m S ctx st pre nsp) (hvm : ∀ z ∈ S.blocks, Mem.valid_block m z)
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
  have hd := hs.distinct
  have hnl := hs.nlt
  rw [tFree_eq]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, Search.eval_gint (e := nEnv bI) rfl find_n hs.fixed.nn]
  simp only [Exec.evalExpr, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 320) = ir 320 from rfl,
    ir_lt (a := n) (b := 320) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  have hfC := hs.fixed.dCleanup
  have hfS := hs.fixed.doschreier
  have hfm' : ∀ z ∈ flat chain, z ∉ S.blocks := by
    intro z hz
    simp only [flat, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hz
    obtain ⟨p, hp, h | h⟩ := hz <;> subst h
    · exact (hTo.apart p hp).1
    · exact (hTo.apart p hp).2.1
  have nF : ∀ z ∈ [Proofs.Search.Block.dispatch, Proofs.Search.Block.doschreier],
      ¬ FreeSet m S chain cDW bDW z := by
    intro z hz hF
    have hzS : z ∈ S.blocks := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl <;> simp [SLoc.blocks]
    rcases hF with h | h | ⟨hc, rfl⟩ | h | h
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl <;> exact absurd h (by decide)
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz h
      rcases hz with rfl | rfl <;>
        rcases h with h|h|h|h|h|h|h|h|h <;> exact absurd h (by sep_ne hd)
    · exact (hDWs hc).1 hzS
    · exact hs.work_not h hzS
    · exact (hfm' z h) hzS
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at nF
  by_cases h320 : n < 320
  · rw [ite_eq_right (by simp; omega)]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    exact wp_freeTail hfC hfS (hQ m (Unch.refl _ _) fun _ h => h)
  · rw [ite_eq_left (by simp; omega)]
    refine wp_freeBody hs hvm hTc hTo hDW hpF hgW hDWs hgS hgC fun m' hu hg => ?_
    simp only [seqPost, Post.after, E0_append]
    exact wp_freeTail (hfC.unch hu nF.1) (hfS.unch hu nF.2) (hQ m' hu hg)

end NautyVerified.Proofs.Top

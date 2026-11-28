import NautyVerified.Proofs.Top.NautyWork
import NautyVerified.Proofs.Search.Node.FirstCall

/-!
# `nauty()`'s root call (`tRoot`)

`retval = firstpathnode0(lab, ptn, 1, numcells, &tcnode0)`, through a
`firstpathnodeSpec` for the root (level 1, empty `tcnode` chain).
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls}

/-- The root `firstpathnode0` call (`tRoot`). -/
theorem wp_tRoot {n : Nat} {Q : Post} {le : temp_env} {m : mem}
    {NodeOk : Bool → Nat → Nat → Search n → Prop} {Em : Bool → Nat → Nat → Search n → List Int}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {nc : Nat}
    (hRoot : Satisfies xi ge (.Internal dense.fn.«nauty:firstpathnode0»)
      (firstpathnodeSpec xi NodeOk Em S ctx st 1 nc []))
    (h : SearchAt m S ctx st true false) (hTc : TcChain m S.M Block.tcnode0 [])
    (hTo : TcOk m S []) (hcb : AutomCb xi S.bUA) (hn1 : 1 ≤ n) (hncl : nc ≤ n)
    (hok : NodeOk true 1 nc st)
    (hvU : Mem.valid_block m S.bUA) (hpU : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hnc : PTree.get dense.id.«numcells» le = some (.Vint (ir nc)))
    (hQ : ∀ t m', let r := hexNode true ctx 1 nc st
      SearchAt m' S ctx r.2 false (exitValue 1 r.1).2 →
      Emits t (Em true 1 nc st) →
      (∃ chain', TcChain m' S.M Block.tcnode0 chain' ∧ TcOk m' S chain' ∧ 1 ≤ chain'.length ∧
        ∀ p ∈ chain', ¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2) →
      NodeFrame m m' S [] 1 →
      (∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z) →
      Wp xi ge dense.fn.nauty Nauty.tPost (Q.after t) (nEnv bI)
        (PTree.set dense.id.«retval» (.Vint (ir (exitValue 1 r.1).1))
          (PTree.set (idOf 735) (.Vint (ir (exitValue 1 r.1).1)) le)) m') :
    Wp xi ge dense.fn.nauty Nauty.tRoot Q (nEnv bI) le m := by
  simp only [Nauty.tRoot, Set.sk]
  wp_step; wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.firstpathnodeFn Ptrofs.zero)
    (targs := [tptr tint, tptr tint, tint, tint, tptr tcStruct]) (tres := tint)
    (cc := Common.AST.cc_default)
    (vargs := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir ((1 : Nat) : Int)),
      .Vint (ir (nc : Int)), .Vptr (tcParent [] 1) Ptrofs.zero])
    (.Internal dense.fn.«nauty:firstpathnode0») _ hRoot rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_firstpathnodeFn]) rfl
    ⟨rfl, h, hTc, hTo, by simp, hcb, Nat.le_refl _, hn1, hncl, hok, hvU, hpU⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get dense.id.«nauty:firstpathnode0» (nEnv bI) = none from rfl, find_firstpathnodeFn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, hlab, hptn, hnc,
      show PTree.get dense.id.«nauty:tcnode0» (nEnv bI) = none from rfl, find_tcnode0,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode, Refine.tv, Refine.pi, typeof, cop]
    rfl
  · rintro t v m' ⟨hv, hS', hE, hC, hF, hW, -⟩
    subst hv
    simp only [set_opttemp, seqPost, Post.after]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv, append_E0]
    refine hQ t m' hS' hE ?_ hF hW
    obtain ⟨c', h1, h2, h3, -, h5⟩ := hC
    exact ⟨c', h1, h2, h3, fun p hp => (h5 p hp).resolve_left (by simp)⟩

end NautyVerified.Proofs.Top

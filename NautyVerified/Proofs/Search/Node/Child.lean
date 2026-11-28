import NautyVerified.Proofs.Search.Node.Em
import NautyVerified.Proofs.Search.Node.TcOps

/-!
# A node's recursive call on a child

`rtnlevel = othernode0(lab, ptn, level + 1, numcells + 1, tcnode_this);`
`wp_nodeChild` takes `othernode0`'s specification at the child as a
hypothesis and passes its postcondition on; `wp_nodeChildG` is the same over
`SearchAtG D` for `nodeSpecG`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

/-- The recursive call and `rtnlevel = t717`. -/
abbrev childCall : statement :=
  .Ssequence
    (Set.sk (.Scall (some (idOf 717))
      (.Evar dense.id.«nauty:othernode0»
        (tfun [tptr tint, tptr tint, tint, tint, tptr tcStruct] tint))
      [.Etempvar dense.id.«lab» (tptr tint), .Etempvar dense.id.«ptn» (tptr tint),
       .Ebinop .Oadd (Refine.tv dense.id.«level») (ci 1 tint) tint,
       .Ebinop .Oadd (.Evar dense.id.«numcells» tint) (ci 1 tint) tint,
       .Etempvar dense.id.«tcnode_this» (tptr tcStruct)]))
    (.Sset dense.id.«rtnlevel» (Refine.tv (idOf 717)))

theorem wp_nodeChild {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {NodeOk : Bool → Nat → Nat → Search n → Prop} {Em : Bool → Nat → Nat → Search n → List Int}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {level nc : Nat} {chain : List (block × block)}
    (hRec : Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (othernodeSpec xi NodeOk Em S ctx st (level + 1) (nc + 1) chain))
    (h : SearchAt m S ctx st false false) (hTc : TcChain m S.M Block.tcnode0 chain)
    (hTo : TcOk m S chain) (hlen : level ≤ chain.length) (hcb : AutomCb xi S.bUA)
    (hln : level + 1 ≤ n) (hncl : nc + 1 ≤ n) (hok : NodeOk false (level + 1) (nc + 1) st)
    (hvU : Mem.valid_block m S.bUA) (hua : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty)
    {bnc : block} (hen : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc)))
    (hge : PTree.get dense.id.«nauty:othernode0» e = none)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (htcn : PTree.get dense.id.«tcnode_this» le =
      some (.Vptr (tcParent chain (level + 1)) Ptrofs.zero))
    (hQ : ∀ t m',
      SearchAt m' S ctx (hexNode false ctx (level + 1) (nc + 1) st).2 false
        (exitValue (level + 1) (hexNode false ctx (level + 1) (nc + 1) st).1).2 →
      Emits t (Em false (level + 1) (nc + 1) st) →
      (∃ chain', TcChain m' S.M Block.tcnode0 chain' ∧ TcOk m' S chain' ∧
        level + 1 ≤ chain'.length ∧ chain'.take level = chain.take level ∧
        ∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) →
      NodeFrame m m' S chain (level + 1) →
      (∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z) →
      (∀ tg sh, (hexNode false ctx (level + 1) (nc + 1) st).1 = .unwind tg sh → tg < level + 1) →
      Q.normal t e (PTree.set dense.id.«rtnlevel»
        (.Vint (ir (exitValue (level + 1) (hexNode false ctx (level + 1) (nc + 1) st).1).1))
        (PTree.set (idOf 717)
          (.Vint (ir (exitValue (level + 1) (hexNode false ctx (level + 1) (nc + 1) st).1).1)) le))
        m') :
    Wp xi ge f childCall Q e le m := by
  have hnl := h.nlt
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.othernodeFn Ptrofs.zero)
    (targs := [tptr tint, tptr tint, tint, tint, tptr tcStruct]) (tres := tint)
    (cc := Common.AST.cc_default)
    (vargs := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir ((level + 1 : Nat) : Int)),
      .Vint (ir ((nc + 1 : Nat) : Int)), .Vptr (tcParent chain (level + 1)) Ptrofs.zero])
    (.Internal dense.fn.«nauty:othernode0») _ hRec rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_othernodeFn]) rfl
    ⟨rfl, h, hTc, hTo, by omega, hcb, by omega, hln, hncl, hok, hvU, hua⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, hge, find_othernodeFn, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, hen, hlab, hptn, hlev, htcn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hncv, ite_true, Refine.tv, typeof, cop,
      ir_add]
    push_cast
    rfl
  · rintro t v m' ⟨hv, hS', hE, hC, hF, hW, hT⟩
    subst hv
    simp only [set_opttemp]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv, append_E0]
    refine hQ t m' hS' hE ?_ hF hW hT
    obtain ⟨c', h1, h2, h3, h4, h5⟩ := hC
    exact ⟨c', h1, h2, h3, by simpa using h4, h5⟩

section Generic

open NautyVerified.Proofs.Dispatch (Ops DispatchRep)

variable {ge : genv} [E : NautyEnv ge] {O : Ops} {D : DispatchRep ge O}

/-- `wp_nodeChild` over `SearchAtG D`, for `nodeSpecG` and the policy `P`. -/
theorem wp_nodeChildG {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    [P : Generic.Policy (SearchState n (O.Canon n)) n (γ := O.Gr n)]
    {NodeOk : Bool → Nat → Nat → SearchState n (O.Canon n) → Prop}
    {Em : Bool → Nat → Nat → SearchState n (O.Canon n) → List Int}
    {S : SLoc} {gl : D.GLoc} {cl : D.CLoc} {G : O.Gr n} {st : SearchState n (O.Canon n)}
    {level nc : Nat} {chain : List (block × block)}
    (hRec : Satisfies xi ge (.Internal dense.fn.«nauty:othernode0»)
      (nodeSpecG D xi NodeOk Em false S gl cl G st (level + 1) (nc + 1) chain))
    (h : SearchAtG D m S gl cl G st false false) (hTc : TcChain m S.M E.tcnode0 chain)
    (hTo : TcOkG D m S gl cl chain) (hlen : level ≤ chain.length) (hcb : AutomCb xi S.bUA)
    (hln : level + 1 ≤ n) (hncl : nc + 1 ≤ n) (hok : NodeOk false (level + 1) (nc + 1) st)
    (hvU : Mem.valid_block m S.bUA) (hua : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty)
    {bnc : block} (hen : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc)))
    (hge : PTree.get dense.id.«nauty:othernode0» e = none)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (htcn : PTree.get dense.id.«tcnode_this» le =
      some (.Vptr (tcParent chain (level + 1)) Ptrofs.zero))
    (hQ : ∀ t m',
      SearchAtG D m' S gl cl G (hexNodeG false G (level + 1) (nc + 1) st).2 false
        (exitValue (level + 1) (hexNodeG false G (level + 1) (nc + 1) st).1).2 →
      Emits t (Em false (level + 1) (nc + 1) st) →
      (∃ chain', TcChain m' S.M E.tcnode0 chain' ∧ TcOkG D m' S gl cl chain' ∧
        level + 1 ≤ chain'.length ∧ chain'.take level = chain.take level ∧
        ∀ p ∈ chain', p ∈ chain ∨ (¬ Mem.valid_block m p.1 ∧ ¬ Mem.valid_block m p.2)) →
      NodeFrameG D m m' S gl cl chain (level + 1) →
      (∀ z, IsWorkG D m' z → IsWorkG D m z ∨ ¬ Mem.valid_block m z) →
      (∀ tg sh, (hexNodeG false G (level + 1) (nc + 1) st).1 = .unwind tg sh → tg < level + 1) →
      Q.normal t e (PTree.set dense.id.«rtnlevel»
        (.Vint (ir (exitValue (level + 1) (hexNodeG false G (level + 1) (nc + 1) st).1).1))
        (PTree.set (idOf 717)
          (.Vint (ir (exitValue (level + 1) (hexNodeG false G (level + 1) (nc + 1) st).1).1)) le))
        m') :
    Wp xi ge f childCall Q e le m := by
  have hnl := h.nlt
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr E.othernodeFn Ptrofs.zero)
    (targs := [tptr tint, tptr tint, tint, tint, tptr tcStruct]) (tres := tint)
    (cc := Common.AST.cc_default)
    (vargs := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir ((level + 1 : Nat) : Int)),
      .Vint (ir ((nc + 1 : Nat) : Int)), .Vptr (tcParent chain (level + 1)) Ptrofs.zero])
    (.Internal dense.fn.«nauty:othernode0») _ hRec rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, E.funct_othernodeFn]) rfl
    ⟨rfl, h, hTc, hTo, by omega, hcb, by omega, hln, hncl, hok, hvU, hua⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, hge, E.find_othernodeFn, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.lvalOfVar, hen, hlab, hptn, hlev, htcn,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hncv, ite_true, Refine.tv, typeof, cop,
      ir_add]
    push_cast
    rfl
  · rintro t v m' ⟨hv, hS', hE, hC, hF, hW, hT⟩
    subst hv
    simp only [set_opttemp]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, Refine.tv, append_E0]
    refine hQ t m' hS' hE ?_ hF hW hT
    obtain ⟨c', h1, h2, h3, h4, h5⟩ := hC
    exact ⟨c', h1, h2, h3, by simpa using h4, h5⟩

end Generic

end NautyVerified.Proofs.Search

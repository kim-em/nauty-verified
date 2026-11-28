import NautyVerified.Proofs.Search.Node.Choose

/-!
# `othernode0`'s `processnode` call

```
rtnlevel = processnode(lab, ptn, level, numcells);
if (rtnlevel < level) return rtnlevel;
```

`wp_nodeProcess`: with HexGraphIso's `classify` then `leafExit` giving the
exit `r.1`, an internal node (`.done`) continues with the rest of the body, and
every other exit returns its target, which lies below `level`.
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

/-- `t712 = processnode(lab, ptn, level, numcells); rtnlevel = t712;` -/
abbrev procCall : statement :=
  .Ssequence
    (Set.sk (.Scall (some (idOf 712))
      (.Evar dense.id.«nauty:processnode» (tfun [tptr tint, tptr tint, tint, tint] tint))
      [.Etempvar dense.id.«lab» (tptr tint), .Etempvar dense.id.«ptn» (tptr tint),
       Refine.tv dense.id.«level», .Evar dense.id.«numcells» tint]))
    (.Sset dense.id.«rtnlevel» (Refine.tv (idOf 712)))

/-- `if (rtnlevel < level) return rtnlevel;` -/
abbrev earlyRet : statement :=
  .Sifthenelse (.Ebinop .Olt (Refine.tv dense.id.«rtnlevel») (Refine.tv dense.id.«level») tint)
    (Set.sk (.Sreturn (some (Refine.tv dense.id.«rtnlevel»)))) .Sskip

/-- `processnode`'s exit at an off-path node. -/
abbrev procExit {n : Nat} (ctx : Ctx n) (level numcells : Nat) (st : Search n) : Exit × Search n :=
  leafExit (classify ctx level numcells st).1 level (classify ctx level numcells st).2

/-- What `processnode` writes. -/
abbrev procWords {n : Nat} (ctx : Ctx n) (level numcells : Nat) (st : Search n) : List Int :=
  if (procExit ctx level numcells st).2.numgenerators = st.numgenerators + 1 then
    genWords (procExit ctx level numcells st).2.workperm n else []

theorem wp_nodeProcess {n : Nat} {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {S : SLoc} {ctx : Ctx n} {st : Search n} {level nc : Nat} {rest : statement}
    (h : SearchAt m S ctx st false false)
    (hP : Satisfies xi ge (.Internal dense.fn.«nauty:processnode») (processnodeSpec xi S ctx st level nc))
    (hcb : AutomCb xi S.bUA) (hl1 : 1 ≤ level) (hln : level ≤ n) (hncl : nc ≤ n)
    (hlok : LeafOk st) (hval : ∀ z ∈ S.blocks, Mem.valid_block m z)
    (hua : Mem.perm m S.bUA (zOfInt 0) .Cur .Nonempty)
    {bnc : block} (hen : PTree.get dense.id.numcells e = some (bnc, tint))
    (hncv : Mem.load .Mint32 m bnc (zOfInt 0) = some (.Vint (ir nc)))
    (hge : PTree.get dense.id.«nauty:processnode» e = none)
    (hlab : PTree.get dense.id.«lab» le = some (.Vptr S.bl S.lofs))
    (hptn : PTree.get dense.id.«ptn» le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.«level» le = some (.Vint (ir level)))
    (hfret : f.fn_return = tint)
    (hlt : ∀ tg s, (procExit ctx level nc st).1 = .unwind tg s → tg < level)
    (hnf : (procExit ctx level nc st).1 ≠ .fuel)
    (hRet : ∀ t m', (procExit ctx level nc st).1 ≠ .done →
      SearchAt m' S ctx (procExit ctx level nc st).2 false
        (exitValue level (procExit ctx level nc st).1).2 →
      Writes t (procWords ctx level nc st) → SFrame m m' S →
      (∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z) →
      match Mem.free_list m' (blocks_of_env ge e) with
      | some m'' => Q.ret t (.Vint (ir (exitValue level (procExit ctx level nc st).1).1)) m''
      | none => False)
    (hDone : ∀ t le' m', (procExit ctx level nc st).1 = .done →
      SearchAt m' S ctx (procExit ctx level nc st).2 false false →
      Writes t (procWords ctx level nc st) → SFrame m m' S →
      (∀ z, IsWork m' z → IsWork m z ∨ ¬ Mem.valid_block m z) →
      (∀ x, x ≠ idOf 712 → x ≠ dense.id.«rtnlevel» → PTree.get x le' = PTree.get x le) →
      Wp xi ge f rest (Q.after t) e le' m') :
    Wp xi ge f (.Ssequence procCall (.Ssequence (Set.sk earlyRet) rest)) Q e le m := by
  have hnl := h.nlt
  wp_step; wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.processnodeFn Ptrofs.zero) (targs := [tptr tint, tptr tint, tint, tint])
    (tres := tint) (cc := Common.AST.cc_default)
    (vargs := [.Vptr S.bl S.lofs, .Vptr S.bp S.pofs, .Vint (ir level), .Vint (ir nc)])
    (.Internal dense.fn.«nauty:processnode») _ hP rfl ?_ ?_
    (by simp [Common.Globalenvs.Genv.find_funct, funct_processnodeFn]) rfl
    ⟨rfl, h, hcb, hl1, hln, hncl, hlok, hval, hua⟩ ?_
  · simp only [Exec.evalExpr, Exec.lvalOfVar, hge, find_processnodeFn, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode]
  · simp only [Exec.evalExprlist, Exec.evalExpr, hlab, hptn, hlev, typeof, cop, Exec.lvalOfVar, hen,
      Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hncv, ite_true]
  rintro t v m' ⟨hv, hS', hW, hF⟩
  subst hv
  simp only [set_opttemp]
  have hle : ∀ (v : val) x, x ≠ idOf 712 → x ≠ dense.id.«rtnlevel» →
      PTree.get x (PTree.set dense.id.rtnlevel v (PTree.set (idOf 712) v le)) = PTree.get x le :=
    fun v x h1 h2 => by rw [temps_gso _ _ h2, temps_gso _ _ h1]
  have hrl : ∀ v, PTree.get dense.id.«rtnlevel» (PTree.set dense.id.rtnlevel v
      (PTree.set (idOf 712) v le)) = some v := fun v => temps_gss _ _ _
  have hlev' : ∀ v, PTree.get dense.id.level (PTree.set dense.id.rtnlevel v
      (PTree.set (idOf 712) v le)) = some (.Vint (ir level)) :=
    fun v => (hle v dense.id.level (by decide) (by decide)).trans hlev
  have hW' := hW
  have hS'' := hS'
  rcases hx : (leafExit (classify ctx level nc st).1 level (classify ctx level nc st).2).1 with
    _ | ⟨tg, s⟩ | _
  · -- internal node: continue
    simp only [exitValue]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hrl, hlev', Refine.tv, typeof, cop]
    rw [ir_lt (a := (level : Int)) (b := level) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp only [Int.lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
    apply wp_skip
    simp only [seqPost, Post.after, E0_append]
    rw [hx] at hS''
    exact hDone t _ m' hx hS'' hW' hF.1 hF.2 fun x h1 h2 => hle _ x h1 h2
  · -- an unwind below this level: return its target
    have htg := hlt tg s hx
    simp only [exitValue]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hrl, hlev', Refine.tv, typeof, cop]
    rw [ir_lt (a := (tg : Int)) (b := level) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    simp only [show (tg : Int) < level by omega, decide_true, ite_true]
    wp_step; wp_step
    apply wp_return_some_eval
    simp only [Exec.evalExpr, hrl, Refine.tv, typeof, hfret, cop]
    have := hRet t m' (by rw [hx]; simp) hS' hW' hF.1 hF.2
    rw [hx] at this
    simp only [exitValue] at this
    revert this
    rcases Mem.free_list m' (blocks_of_env ge e) with _ | m'' <;> simp [Post.after]
  · exact absurd hx hnf

end NautyVerified.Proofs.Search

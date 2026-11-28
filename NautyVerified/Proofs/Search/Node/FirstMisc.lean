import NautyVerified.Proofs.Search.Node.FirstLocal
import NautyVerified.Proofs.Search.Node.Firstpathnode

/-!
# The kill check and the cheap test of `firstpathnode0`

- `wp_fpnKill`: `t710 = nauty_kill_request; if (t710) return -12;` in the
  execution whose volatile read returns 0: the trace is that one read, which
  emits nothing;
- `wp_fpnCheap`: `if (noncheaplevel >= level) t711 = !cheapautom(…) else t711 = 0;
  if (t711) noncheaplevel = level + 1;` is HexGraphIso's `cheapCheck true`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Refine (tv)
open NautyVerified.Proofs.Set (sk)
open Hex.GraphIso.Nauty

set_option linter.unusedSimpArgs false

variable {xi : ExternalCalls} {n : Nat}


/-- The kill flag's volatile read of 0. -/
abbrev killEv : event := .Event_vload .Mint32 dense.id.«nauty_kill_request» Ptrofs.zero (.EVint Int.zero)

theorem emits_killEv : Emits [killEv] [] :=
  ⟨rfl, rfl, fun c i o ev hm => by
    cases hm with
    | head => rfl
    | tail _ h => cases h⟩

kernel_rfl senv_find_killRequest :
  Senv.find_symbol (Genv.to_senv ge.genv_genv) dense.id.«nauty_kill_request» = some Block.killRequest

kernel_rfl volatile_killRequest :
  Senv.block_is_volatile (Genv.to_senv ge.genv_genv) Block.killRequest = true

/-- `t710 = nauty_kill_request; if (t710) return -12;` reading 0. -/
theorem wp_fpnKill {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    (hge : PTree.get dense.id.«nauty_kill_request» e = none)
    (hQ : Q.normal [killEv] e (PTree.set (idOf 710) (.Vint Int.zero) le) m) :
    Wp xi ge f (.Ssequence
      (sk (.Sbuiltin (some (idOf 710)) (.EF_vload .Mint32)
        [tptr (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr)]
        [.Eaddrof (.Evar dense.id.«nauty_kill_request»
            (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr))
          (tptr (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr))]))
      (.Sifthenelse (.Etempvar (idOf 710) (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr))
        (sk (.Sreturn (some (.Eunop .Oneg (ci 12 tint) tint)))) .Sskip)) Q e le m := by
  wp_step; wp_step; wp_step
  refine wp_builtin (vargs := [.Vptr Block.killRequest Ptrofs.zero]) (t := [killEv])
    (vres := .Vint Int.zero) (m' := m) ?_ ?_ ?_
  · simp only [Exec.evalExprlist, Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, hge,
      find_killRequest, typeof]
    rfl
  · have hv := volatile_load_vol (ge := Genv.to_senv ge.genv_genv) .Mint32 m Block.killRequest
      Ptrofs.zero dense.id.«nauty_kill_request» (.EVint Int.zero) (.Vint Int.zero)
      volatile_killRequest senv_find_killRequest (ev_match_int _)
    exact volatile_load_sem_intro _ _ _ _ _ hv
  simp only [set_opttemp, seqPost, Post.after]
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, typeof]
  rw [show Cfrontend.Cop.bool_val (.Vint Int.zero)
    (Cfrontend.Ctypes.Tint .I32 .Signed NautyVerified.Proofs.vattr) m = some false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  apply wp_skip
  exact hQ

theorem SearchAt.setNoncheap {m m' : mem} {S : SLoc} {ctx : Ctx n} {st : Search n} {pre nsp : Bool}
    (h : SearchAt m S ctx st pre nsp) (hU : Unch m m' (· ∈ [Block.noncheaplevel])) {v : Nat}
    (iNC : IntAt m' Block.noncheaplevel (v : Int)) (hv : v < 2147483648) :
    SearchAt m' S ctx { st with noncheaplevel := v } pre nsp := by
  have sc := h.scalars
  refine h.setScalars hU (fun z hz => by simp at hz; subst hz; decide)
    ⟨sc.gcaFirst.unch hU (by decide), sc.gcaCanon.unch hU (by decide), iNC,
      sc.allsamelevel.unch hU (by decide), sc.eqlevFirst.unch hU (by decide),
      sc.eqlevCanon.unch hU (by decide), sc.compCanon.unch hU (by decide),
      sc.samerows.unch hU (by decide), sc.canonlevel.unch hU (by decide),
      sc.stabvertex.unch hU (by decide), sc.cosetindex.unch hU (by decide),
      sc.needshortprune.unch hU (by decide)⟩
    { h.arrays with } { h.stats with } ?_
  obtain ⟨s1, s2, -, s4⟩ := h.inv.scalars
  exact { h.inv with scalars := ⟨s1, s2, hv, s4⟩ }

/-- `if (noncheaplevel >= level) t711 = !cheapautom(ptn, level, digraph, n); else t711 = 0;
if (t711) noncheaplevel = level + 1;`: HexGraphIso's `cheapCheck true`. -/
theorem wp_fpnCheap {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {S : SLoc}
    {ctx : Ctx n} {st : Search n} {pre nsp : Bool} {level : Nat} (h : SearchAt m S ctx st pre nsp)
    (hE1 : PTree.get dense.id.«nauty:dispatch» e = none)
    (hE2 : PTree.get dense.id.«nauty:digraph» e = none)
    (hE3 : PTree.get dense.id.«nauty:n» e = none)
    (hE4 : PTree.get dense.id.«nauty:noncheaplevel» e = none)
    (hptn : PTree.get dense.id.ptn le = some (.Vptr S.bp S.pofs))
    (hlev : PTree.get dense.id.level le = some (.Vint (ir level))) (h1 : 1 ≤ level) (hn : level ≤ n)
    (hQ : ∀ le' m', SearchAt m' S ctx (cheapCheck true level st) pre nsp →
      Unch m m' (· ∈ [Block.noncheaplevel]) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 711 → x ≠ idOf 712 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp xi ge f (.Ssequence (sk Firstpathnode.cheap)
      (.Sifthenelse (tv (idOf 711))
        (sk (.Sassign (.Evar dense.id.«nauty:noncheaplevel» tint)
          (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint))) .Sskip)) Q e le m := by
  have hnl := h.nlt
  have hI := h.inv
  obtain ⟨-, -, hnc, -⟩ := hI.scalars
  have hcast : ∀ b : Bool, Cfrontend.Cop.sem_cast (Val.of_bool b) tint tbool m =
      some (Val.of_bool b) := fun b => by cases b <;> rfl
  -- the tail, from `t711` holding `b`
  have tail : ∀ (le' : temp_env) (b : Bool), PTree.get (idOf 711) le' = some (Val.of_bool b) →
      PTree.get dense.id.level le' = some (.Vint (ir level)) →
      (∀ x, x ≠ idOf 711 → x ≠ idOf 712 → PTree.get x le' = PTree.get x le) →
      cheapCheck true level st = (if b then { st with noncheaplevel := level + 1 } else st) →
      Wp xi ge f (.Sifthenelse (tv (idOf 711))
        (sk (.Sassign (.Evar dense.id.«nauty:noncheaplevel» tint)
          (.Ebinop .Oadd (tv dense.id.«level») (ci 1 tint) tint))) .Sskip) Q e le' m := by
    intro le' b h711 hlev' hle' hcc
    apply wp_if_eval
    simp only [Exec.evalExpr, tv, h711, typeof]
    cases b
    · rw [show Cfrontend.Cop.bool_val (Val.of_bool false) tint m = some false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      apply wp_skip
      exact hQ le' m (by rw [hcc]; exact h) (Unch.refl _ _) (fun _ h => h) hle'
    · rw [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m = some true from rfl]
      simp only [ite_true]
      wp_step; wp_step
      refine wp_gint hE4 find_noncheaplevel h.scalars.noncheaplevel.writable
        (x := (level : Int) + 1)
        (by simp only [Exec.evalExpr, tv, hlev', typeof, cop]; simp) rfl ?_
      intro m' iNC hu hv
      have hU : Unch m m' (· ∈ [Block.noncheaplevel]) := hu.mono fun z hz => by simp [hz]
      refine hQ le' m' ?_ hU hv hle'
      rw [hcc]
      exact h.setNoncheap hU (by push_cast; exact iNC) (by omega)
  wp_step
  simp only [Firstpathnode.cheap, sk]
  wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, eval_gint hE4 find_noncheaplevel h.scalars.noncheaplevel,
    show Exec.evalExpr ge e le m (tv dense.id.level) = _ from hlev]
  simp only [typeof, cop]
  rw [ir_lt (a := (st.noncheaplevel : Int)) (b := (level : Int)) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩]
  by_cases hge : level ≤ st.noncheaplevel
  · rw [ite_eq_left (by simp; omega)]
    wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr Block.cheapautomFn Ptrofs.zero) (targs := [tptr tint, tint, tint, tint])
      (tres := tint) (cc := Common.AST.cc_default) (.Internal dense.fn.cheapautom) _
      (Cheapautom.cheapautom_satisfies S.bp S.pofs st.ptn level n) ?_ ?_ ?_
      (by simp [Common.Globalenvs.Genv.find_funct, funct_cheapautomFn]) rfl
      ⟨rfl, h.arrays.ptn, hI.ptnSize, fun x hx => by
          rcases hI.ptnVals x hx with hv | hv
          · omega
          · rw [hv]; decide,
        by have := hI.ptnLast; omega, hnl, by omega⟩ ?_
    · rfl
    · simp only [Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar, hE1, find_dispatch, typeof,
        Exec.derefLoc, Cfrontend.Ctypes.access_mode, field_dCheapautom, Mem.loadv, Alloc.Mptr_eq]
      rw [show Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (zOfInt 40))) = zOfInt 40 from rfl,
        h.fixed.dCheapautom.load]
    · simp only [Exec.evalExprlist, Exec.evalExpr, hptn, hlev, tv, Exec.lvalOfVar, hE2, hE3,
        find_digraph, find_n, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
        show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.fixed.digraph.load, h.fixed.nn.load,
        typeof, cop]
    rintro t v m'' ⟨rfl, hmm, rfl⟩
    rw [hmm]
    simp only [set_opttemp, seqPost, Post.after, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss, tv, typeof, cop]
    have e1 : Int.eq (ir 1) Int.zero = false := by decide
    have e0 : Int.eq (ir 0) Int.zero = true := by decide
    have hlev2 : PTree.get dense.id.level (PTree.set (idOf 711) (Val.of_bool
        (!Hex.GraphIso.Nauty.cheapautom st.ptn level n))
        (PTree.set (idOf 712) (.Vint (ir (if Hex.GraphIso.Nauty.cheapautom st.ptn level n = true
          then 1 else 0))) le)) = some (.Vint (ir level)) := by
      rw [temps_gso _ _ (show dense.id.level ≠ idOf 711 by decide),
        temps_gso _ _ (show dense.id.level ≠ idOf 712 by decide)]; exact hlev
    have key := tail _ (!Hex.GraphIso.Nauty.cheapautom st.ptn level n) (temps_gss _ _ _) hlev2
      (fun x h1 h2 => by rw [temps_gso _ _ h1, temps_gso _ _ h2])
      (by unfold cheapCheck; cases Hex.GraphIso.Nauty.cheapautom st.ptn level n <;> simp [hge])
    revert key
    cases hc : Hex.GraphIso.Nauty.cheapautom st.ptn level n <;> intro key <;>
      simp only [ite_true, Bool.false_eq_true, ite_false, e1, e0, Bool.not_false, Bool.not_true] at key ⊢ <;>
      rw [hcast] <;> simpa only [E0_append] using key
  · rw [ite_eq_right (by simp; omega)]
    apply wp_set_eval
    simp only [Exec.evalExpr]
    exact tail _ false (temps_gss _ _ _) (by rw [temps_gso _ _ (by decide)]; exact hlev)
      (fun x h1 _ => temps_gso _ _ h1)
      (by unfold cheapCheck; simp; omega)

end NautyVerified.Proofs.Search

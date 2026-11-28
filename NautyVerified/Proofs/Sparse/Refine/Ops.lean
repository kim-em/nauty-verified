import NautyVerified.Proofs.Sparse.Refine.Pieces
import NautyVerified.Proofs.Refine.Mash
import NautyVerified.Proofs.Set.Bit
import NautyVerified.Proofs.Isautom.Scan

/-!
# `MASH` and the active set in `refine_sg`

`wp_mash`: `longcode = MASH(longcode, a)` computes HexGraphIso's `mash`.
`eval_isAct`, `wp_addAct`, `wp_delAct`: `ISELEMENT(active, a)`,
`ADDELEMENT(active, a)` and `DELELEMENT(active, a)` with nausparse.c's `bit`
table, as membership in, insertion into and erasure from `t.active`, with
the memory afterwards as `Mem`.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk isElement addElementB delElementB addW delW setRep_add setRep_del)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- `longcode = MASH(longcode, a)`. -/
theorem wp_mash {f : function} {Q : Post} {le : temp_env} {m : mem} {a : expr}
    {l i : Nat} (hl : PTree.get id.longcode le = some (.Vlong (lr l))) (hl2 : l < 2 ^ 62)
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir i))) (hty : typeof a = tint)
    (hi : i < 2147483648)
    (hQ : Q.normal E0 empty_env (PTree.set id.longcode
      (.Vlong (lr (Hex.GraphIso.Nauty.mash l i : Nat))) le) m) :
    Wp xi sge f (mash a) Q empty_env le m := by
  apply wp_set_eval
  simp only [Exec.evalExpr, ha, hty]
  simp only [hl, typeof, cop]
  rw [Refine.mash_eq hl2 hi]
  exact hQ

/-- Assigning `longcode` the code of `t'`, which has `t`'s queue length. -/
theorem Tmp.setCode {le : temp_env} (ht : Tmp le L t) (t' : RefineSt n) (hq : t'.queue.size = t.queue.size) :
    Tmp (PTree.set id.longcode (.Vlong (lr t'.longcode)) le) L t' where
  g := by rw [temps_gso _ _ (by decide)]; exact ht.g
  lab := by rw [temps_gso _ _ (by decide)]; exact ht.lab
  ptn := by rw [temps_gso _ _ (by decide)]; exact ht.ptn
  level := by rw [temps_gso _ _ (by decide)]; exact ht.level
  numcells := by rw [temps_gso _ _ (by decide)]; exact ht.numcells
  active := by rw [temps_gso _ _ (by decide)]; exact ht.active
  code := by rw [temps_gso _ _ (by decide)]; exact ht.code
  m := by rw [temps_gso _ _ (by decide)]; exact ht.m
  n := by rw [temps_gso _ _ (by decide)]; exact ht.n
  v := by rw [temps_gso _ _ (by decide)]; exact ht.v
  d := by rw [temps_gso _ _ (by decide)]; exact ht.d
  e := by rw [temps_gso _ _ (by decide)]; exact ht.e
  longcode := temps_gss _ _ _
  nactive := by rw [temps_gso _ _ (by decide), hq]; exact ht.nactive

/-- Assigning `nactive` the queue length of `t'`, which has `t`'s code. -/
theorem Tmp.setNactive {le : temp_env} (ht : Tmp le L t) (t' : RefineSt n) (hc : t'.longcode = t.longcode) :
    Tmp (PTree.set id.nactive (.Vint (ir t'.queue.size)) le) L t' where
  g := by rw [temps_gso _ _ (by decide)]; exact ht.g
  lab := by rw [temps_gso _ _ (by decide)]; exact ht.lab
  ptn := by rw [temps_gso _ _ (by decide)]; exact ht.ptn
  level := by rw [temps_gso _ _ (by decide)]; exact ht.level
  numcells := by rw [temps_gso _ _ (by decide)]; exact ht.numcells
  active := by rw [temps_gso _ _ (by decide)]; exact ht.active
  code := by rw [temps_gso _ _ (by decide)]; exact ht.code
  m := by rw [temps_gso _ _ (by decide)]; exact ht.m
  n := by rw [temps_gso _ _ (by decide)]; exact ht.n
  v := by rw [temps_gso _ _ (by decide)]; exact ht.v
  d := by rw [temps_gso _ _ (by decide)]; exact ht.d
  e := by rw [temps_gso _ _ (by decide)]; exact ht.e
  longcode := by rw [temps_gso _ _ (by decide), hc]; exact ht.longcode
  nactive := temps_gss _ _ _

/-- After `MASH`, the temporaries describe the hashed state. -/
theorem Tmp.hash {le : temp_env} (ht : Tmp le L t) (v : Nat) :
    Tmp (PTree.set id.longcode (.Vlong (lr (Hex.GraphIso.Nauty.mash t.longcode v : Nat))) le) L
      (t.hash v) :=
  ht.setCode (t.hash v) rfl

theorem setWords_mem {ws : Nat → Lib.Integers.int64} {s : Hex.GraphIso.Nauty.VSet n} {M c : Nat}
    (h : SetRep (fun w => bv64 (ws w)) M s) (hc : c < 64 * M) :
    SetwordsMem (fun w => bv64 (ws w)) c = s.mem c := h.2 c hc

/-- `ISELEMENT(active, a)`. -/
theorem eval_isAct {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S) (ht : Tmp le L t)
    {a : expr} {c : Nat} (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c)))
    (hty : typeof a = tint) (hc : c < n) :
    Exec.evalExpr sge empty_env le m (isElement id.active id.«nausparse:bit» a) =
      some (Val.of_bool (t.active.mem c)) := by
  have hnM := hok.nM
  have hnl := hok.nlt
  rw [Set.eval_isElement hm.act (by have := hok.Mlt; omega) ht.active ha hty (by omega) (by omega) hm.bit rfl find_bit,
    setWords_mem hm.actRep (by omega)]

/-- `ADDELEMENT(active, a)`. -/
theorem wp_addAct {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (ht : Tmp le L t) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n)
    (hQ : ∀ m' aw, Mem m' L G { t with active := t.active.insert c } { S with aw } →
      Frame L m m' → Q.normal E0 empty_env le m') :
    Wp xi sge f (addElementB id.active id.«nausparse:bit» a) Q empty_env le m := by
  have hnM := hok.nM
  have hnl := hok.nlt
  refine Set.wp_addElementB hm.act (by have := hok.Mlt; omega) ht.active ha hty (by omega) (by omega) find_bit hm.bit rfl
    fun m' harr hu ho hg => ?_
  have hk : Keep m m' L.ba := Alloc.Keep.of_outside' ho harr.base_nonneg
  exact hQ m' (addW S.aw c) (hm.setAct hok hu _ _ harr (setRep_add hm.actRep hc) rfl rfl rfl)
    (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))

/-- `DELELEMENT(active, a)`. -/
theorem wp_delAct {f : function} {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L)
    (hm : Mem m L G t S) (ht : Tmp le L t) {a : expr} {c : Nat}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < n)
    (hQ : ∀ m' aw, Mem m' L G { t with active := t.active.erase c } { S with aw } →
      Frame L m m' → Q.normal E0 empty_env le m') :
    Wp xi sge f (delElementB id.active id.«nausparse:bit» a) Q empty_env le m := by
  have hnM := hok.nM
  have hnl := hok.nlt
  refine Set.wp_delElementB hm.act (by have := hok.Mlt; omega) ht.active ha hty (by omega) (by omega) find_bit hm.bit rfl
    fun m' harr hu ho hg => ?_
  have hk : Keep m m' L.ba := Alloc.Keep.of_outside' ho harr.base_nonneg
  exact hQ m' (delW S.aw c) (hm.setAct hok hu _ _ harr (setRep_del hm.actRep (by omega)) rfl rfl rfl)
    (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks]))

end NautyVerified.Proofs.Sparse.Refine

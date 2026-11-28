import NautyVerified.Proofs.Sparse.Refine.Count.Frag
import NautyVerified.Proofs.Sparse.Refine.Ops

/-!
# Queue pushes and optional hashes

`wp_enq`: `t = nactive; nactive = t + 1; ACTIVE[t] = x;` appends `x` to the
queue's array `ACTIVE`; with `ADDELEMENT(active, x)` before (`wp_pushA`) or
after (`wp_pushB`) it is HexGraphIso's `push`. `wp_optMash` is the `MASH`
statement present in one of the two passes only. `Keeps S S'`: the scratch a
count split leaves alone (`HITS`, `HITCELL`, both mark arrays).
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk addElementB)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

theorem after_E0 (Q : Post) : Q.after E0 = Q := rfl

/-- The scratch a count split does not write. -/
structure Keeps (S S' : Scr) : Prop where
  w3 : S'.w3 = S.w3
  w4 : S'.w4 = S.w4
  st1 : S'.st1 = S.st1
  mk1 : S'.mk1 = S.mk1
  st2 : S'.st2 = S.st2
  mk2 : S'.mk2 = S.mk2

theorem Keeps.refl (S : Scr) : Keeps S S := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {S₁ S₂ S₃ : Scr} (h₁ : Keeps S₁ S₂) (h₂ : Keeps S₂ S₃) : Keeps S₁ S₃ :=
  ⟨h₂.w3.trans h₁.w3, h₂.w4.trans h₁.w4, h₂.st1.trans h₁.st1, h₂.mk1.trans h₁.mk1,
    h₂.st2.trans h₁.st2, h₂.mk2.trans h₁.mk2⟩

/-- `t = nactive; nactive = t + 1; ACTIVE[t] = x;` -/
abbrev enq (tv0 x : ident) : statement :=
  .Ssequence
    (.Ssequence (sk (.Sset tv0 (tv id.«nactive»)))
      (.Sset id.«nactive» (.Ebinop .Oadd (tv tv0) (ci 1 tint) tint)))
    (.Sassign (gix id.«nausparse:work2» (tv tv0)) (tv x))

/-- `Rep` reads only `CELLSTART`, `ACTIVE` and `HITS`. -/
theorem Rep.scr (hr : Rep L t S) {S' : Scr} (h1 : S'.w1 = S.w1) (h2 : S'.w2 = S.w2)
    (h3 : S'.w3 = S.w3) : Rep L t S' :=
  { starts := by rw [h1]; exact hr.starts
    queue := by rw [h2]; exact hr.queue
    w3size := by rw [h3]; exact hr.w3size
    w3small := by rw [h3]; exact hr.w3small
    ptnSmall := hr.ptnSmall }

/-- The queue after a push, in `ACTIVE`. -/
theorem Rep.push (hr : Rep L t S) (c : Nat) :
    Rep L (t.push c) { S with w2 := upd S.w2 t.queue.size (.Vint (ir c)) } :=
  { hr with
    queue := fun i hi => by
      show upd S.w2 t.queue.size _ i = _
      simp only [RefineSt.push, Array.size_push] at hi
      by_cases he : i = t.queue.size
      · subst he; simp [upd, RefineSt.push]
      · rw [upd_ne _ _ he, hr.queue i (by omega)]
        simp only [RefineSt.push]
        rw [getElem!_pos (t.queue.push c) i (by simp; omega), getElem!_pos t.queue i (by omega),
          Array.getElem_push_lt] }

/-- A queue entry replaced, in `ACTIVE`. -/
theorem Rep.setQ (hr : Rep L t S) {pos : Nat} (hp : pos < t.queue.size) (c : Nat) (a : Hex.GraphIso.Nauty.VSet n) :
    Rep L { t with queue := t.queue.set! pos c, active := a }
      { S with w2 := upd S.w2 pos (.Vint (ir c)) } :=
  { hr with
    queue := fun i hi => by
      show upd S.w2 pos _ i = _
      simp only [Array.size_set!] at hi
      by_cases he : i = pos
      · subst he; simp only [upd, ite_true]; rw [Array.getElem!_set!_self _ _ _ hp]
      · rw [upd_ne _ _ he, hr.queue i hi, Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)] }

theorem wp_enq {Q : Post} {le : temp_env} {m : mem} {tv0 x : ident}
    (htv : tv0 ∉ args ∧ tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive) (hx : x ≠ tv0) (hxn : x ≠ id.nactive)
    (hok : Ok n L) (hm : Mem m L G t S) (ht : Tmp le L t) {c : Nat}
    (hxv : PTree.get x le = some (.Vint (ir c))) (hq : t.queue.size < n)
    (hQ : ∀ m', Mem m' L G t { S with w2 := upd S.w2 t.queue.size (.Vint (ir c)) } → Frame L m m' →
      Q.normal E0 empty_env (PTree.set id.nactive (.Vint (ir (t.queue.size + 1 : Nat)))
        (PTree.set tv0 (.Vint (ir t.queue.size)) le)) m') :
    Wp xi sge F (enq tv0 x) Q empty_env le m := by
  wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, ht.nactive]
  apply wp_set_eval
  simp only [Exec.evalExpr, temps_gss, typeof, cop, ir_add]
  rw [show ((t.queue.size : Int) + 1) = ((t.queue.size + 1 : Nat) : Int) by omega]
  have hne : tv0 ≠ id.nactive := htv.2.2
  refine wp_w2F (c := t.queue.size) (x := c) hok hm (by
      simp only [Exec.evalExpr]; rw [temps_gso _ _ hne, temps_gss]) rfl
    (by have := hok.c2; omega)
    (by simp only [Exec.evalExpr]; rw [temps_gso _ _ hxn, temps_gso _ _ hx]; exact hxv) rfl ?_
  intro m' hm' hf
  exact hQ m' hm' hf

/-- The temporaries an enqueue assigns. -/
theorem enq_tmp {le : temp_env} (ht : Tmp le L t) {tv0 : ident}
    (htv : tv0 ∉ args ∧ tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive) (c : Nat) :
    Tmp (PTree.set id.nactive (.Vint (ir (t.queue.size + 1 : Nat)))
      (PTree.set tv0 (.Vint (ir t.queue.size)) le)) L (t.push c) := by
  have := (ht.set (x := tv0) (.Vint (ir t.queue.size)) htv).setNactive (t.push c) rfl
  simpa [RefineSt.push] using this

theorem enq_temps {le : temp_env} {tv0 : ident} {v1 v2 : val} :
    ∀ y, y ≠ tv0 → y ≠ id.nactive →
      PTree.get y (PTree.set id.nactive v1 (PTree.set tv0 v2 le)) = PTree.get y le :=
  fun y h1 h2 => by rw [temps_gso _ _ h2, temps_gso _ _ h1]

/-- What a push leaves. -/
def Pushed (L : Loc) (G : Hex.SparseGraph n) (t : RefineSt n) (S : Scr) (tv0 : ident) (c : Nat)
    (le0 : temp_env) (m0 : mem) (le : temp_env) (m : mem) (S' : Scr) : Prop :=
  Mem m L G (t.push c) S' ∧ Rep L (t.push c) S' ∧ Tmp le L (t.push c) ∧ Frame L m0 m ∧
    Keeps S S' ∧ S'.w1 = S.w1 ∧
    ∀ y, y ≠ tv0 → y ≠ id.nactive → PTree.get y le = PTree.get y le0

/-- `ADDELEMENT(active, x); ACTIVE[nactive++] = x;` -/
theorem wp_pushA {Q : Post} {le : temp_env} {m : mem} {tv0 x : ident}
    (htv : tv0 ∉ args ∧ tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive) (hx : x ≠ tv0) (hxn : x ≠ id.nactive)
    (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {c : Nat}
    (hxv : PTree.get x le = some (.Vint (ir c))) (hc : c < n) (hq : t.queue.size < n)
    (hQ : ∀ le' m' S', Pushed L G t S tv0 c le m le' m' S' → Q.normal E0 empty_env le' m') :
    Wp xi sge F (.Ssequence (addElementB id.active id.«nausparse:bit» (tv x)) (enq tv0 x))
      Q empty_env le m := by
  apply wp_seq
  refine wp_addAct hok hm ht (show Exec.evalExpr sge empty_env le m (tv x) = _ from hxv) rfl hc ?_
  intro m1 aw hm1 hf1
  simp only [seqPost, after_E0]
  have hm1' : Mem m1 L G { t with active := t.active.insert c } { S with aw } := hm1
  refine wp_enq htv hx hxn hok hm1' (ht.congr rfl rfl) hxv hq ?_
  intro m2 hm2 hf2
  exact hQ _ m2 _ ⟨hm2.congr rfl rfl rfl rfl, Rep.scr (Rep.push hr c) rfl rfl rfl, enq_tmp ht htv c, hf1.trans hf2,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, enq_temps⟩

/-- `ACTIVE[nactive++] = x; ADDELEMENT(active, x);` -/
theorem wp_pushB {Q : Post} {le : temp_env} {m : mem} {tv0 x : ident}
    (htv : tv0 ∉ args ∧ tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive) (hx : x ≠ tv0) (hxn : x ≠ id.nactive)
    (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {c : Nat}
    (hxv : PTree.get x le = some (.Vint (ir c))) (hc : c < n) (hq : t.queue.size < n)
    (hQ : ∀ le' m' S', Pushed L G t S tv0 c le m le' m' S' → Q.normal E0 empty_env le' m') :
    Wp xi sge F (.Ssequence (enq tv0 x) (addElementB id.active id.«nausparse:bit» (tv x)))
      Q empty_env le m := by
  apply wp_seq
  refine wp_enq htv hx hxn hok hm ht hxv hq ?_
  intro m1 hm1 hf1
  simp only [seqPost, after_E0]
  have ht1 := enq_tmp ht htv c
  have hxv' : PTree.get x (PTree.set id.nactive (.Vint (ir (t.queue.size + 1 : Nat)))
      (PTree.set tv0 (.Vint (ir t.queue.size)) le)) = some (.Vint (ir c)) := by
    rw [enq_temps x hx hxn]; exact hxv
  let t' : RefineSt n := { t with queue := t.queue.push c }
  refine wp_addAct (t := t') hok (hm1.congr rfl rfl rfl rfl) (ht1.congr rfl rfl)
    (show Exec.evalExpr sge empty_env _ m1 (tv x) = _ from hxv') rfl hc ?_
  intro m2 aw hm2 hf2
  exact hQ _ m2 _ ⟨hm2.congr rfl rfl rfl rfl, Rep.scr (Rep.push hr c) rfl rfl rfl, ht1, hf1.trans hf2,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, enq_temps⟩

/-- `ADDELEMENT(active, x); ACTIVE[nactive++] = x; rest` -/
theorem wp_pushAR {Q : Post} {le : temp_env} {m : mem} {tv0 x : ident} {rest : statement}
    (htv : tv0 ∉ args ∧ tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive) (hx : x ≠ tv0) (hxn : x ≠ id.nactive)
    (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {c : Nat}
    (hxv : PTree.get x le = some (.Vint (ir c))) (hc : c < n) (hq : t.queue.size < n)
    (hQ : ∀ le' m' S', Pushed L G t S tv0 c le m le' m' S' → Wp xi sge F rest Q empty_env le' m') :
    Wp xi sge F (.Ssequence (addElementB id.active id.«nausparse:bit» (tv x))
      (.Ssequence (enq tv0 x) rest)) Q empty_env le m := by
  apply wp_seq
  refine wp_addAct hok hm ht (show Exec.evalExpr sge empty_env le m (tv x) = _ from hxv) rfl hc ?_
  intro m1 aw hm1 hf1
  simp only [seqPost, after_E0]
  apply wp_seq
  have hm1' : Mem m1 L G { t with active := t.active.insert c } { S with aw } := hm1
  refine wp_enq htv hx hxn hok hm1' (ht.congr rfl rfl) hxv hq ?_
  intro m2 hm2 hf2
  simp only [seqPost, after_E0]
  exact hQ _ m2 _ ⟨hm2.congr rfl rfl rfl rfl, Rep.scr (Rep.push hr c) rfl rfl rfl, enq_tmp ht htv c,
    hf1.trans hf2, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, enq_temps⟩

/-- `ACTIVE[nactive++] = x; ADDELEMENT(active, x); rest` -/
theorem wp_pushBR {Q : Post} {le : temp_env} {m : mem} {tv0 x : ident} {rest : statement}
    (htv : tv0 ∉ args ∧ tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive) (hx : x ≠ tv0) (hxn : x ≠ id.nactive)
    (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t) {c : Nat}
    (hxv : PTree.get x le = some (.Vint (ir c))) (hc : c < n) (hq : t.queue.size < n)
    (hQ : ∀ le' m' S', Pushed L G t S tv0 c le m le' m' S' → Wp xi sge F rest Q empty_env le' m') :
    Wp xi sge F (.Ssequence (enq tv0 x)
      (.Ssequence (addElementB id.active id.«nausparse:bit» (tv x)) rest)) Q empty_env le m := by
  apply wp_seq
  refine wp_enq htv hx hxn hok hm ht hxv hq ?_
  intro m1 hm1 hf1
  simp only [seqPost, after_E0]
  have ht1 := enq_tmp ht htv c
  have hxv' : PTree.get x (PTree.set id.nactive (.Vint (ir (t.queue.size + 1 : Nat)))
      (PTree.set tv0 (.Vint (ir t.queue.size)) le)) = some (.Vint (ir c)) := by
    rw [enq_temps x hx hxn]; exact hxv
  let t' : RefineSt n := { t with queue := t.queue.push c }
  apply wp_seq
  refine wp_addAct (t := t') hok (hm1.congr rfl rfl rfl rfl) (ht1.congr rfl rfl)
    (show Exec.evalExpr sge empty_env _ m1 (tv x) = _ from hxv') rfl hc ?_
  intro m2 aw hm2 hf2
  simp only [seqPost, after_E0]
  exact hQ _ m2 _ ⟨hm2.congr rfl rfl rfl rfl, Rep.scr (Rep.push hr c) rfl rfl rfl, ht1, hf1.trans hf2,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, enq_temps⟩

/-- A hashed state, when `b`. -/
abbrev hashIf (b : Bool) (t : RefineSt n) (i : Nat) : RefineSt n := if b then t.hash i else t

theorem Mem.hashIf {m : mem} (h : Mem m L G t S) (b : Bool) (i : Nat) : Mem m L G (hashIf b t i) S := by
  cases b
  · exact h
  · exact h.congr rfl rfl rfl rfl

theorem Rep.hashIf (h : Rep L t S) (b : Bool) (i : Nat) : Rep L (hashIf b t i) S := by
  cases b
  · exact h
  · exact { h with }

theorem hashIf_code {b : Bool} {i : Nat} (h : t.longcode < 2 ^ 62) : (hashIf b t i).longcode < 2 ^ 62 := by
  cases b
  · exact h
  · show Hex.GraphIso.Nauty.mash _ _ < _
    have := NautyVerified.Proofs.Refine.mash_lt t.longcode i; omega

/-- `MASH(a); rest` when `b`, else `rest`. -/
theorem wp_optMash {Q : Post} {le : temp_env} {m : mem} (b : Bool) {a : expr} {i : Nat}
    {rest : statement} (ht : Tmp le L t) (hc : t.longcode < 2 ^ 62)
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir i))) (hty : typeof a = tint)
    (hi : i < 2147483648)
    (hQ : ∀ le', Tmp le' L (hashIf b t i) → (∀ x, x ≠ id.longcode → PTree.get x le' = PTree.get x le) →
      Wp xi sge F rest Q empty_env le' m) :
    Wp xi sge F (optSeq b (sk (mash a)) rest) Q empty_env le m := by
  cases b
  · exact hQ le ht (fun _ _ => rfl)
  · apply wp_seq
    wp_step; wp_step
    refine wp_mash ht.longcode hc ha hty hi ?_
    exact hQ _ (ht.hash i) (fun x hx => temps_gso _ _ hx)

end NautyVerified.Proofs.Sparse.Refine.Count

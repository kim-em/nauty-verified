import NautyVerified.Statement.Dense
import NautyVerified.Statement.Compiler
import CompCert4Lean.Cfrontend.ClightDeterm
import NautyVerified.Word.Machine

/-!
# From one execution to every behaviour of the binary

The specifications of `main` describe one execution of the pinned Clight
program: the one whose `nv_read`s return the input. This file turns that
into a statement about every behaviour of the compiled binary.

- `norm` sets the result of every syscall event other than `nv_read` to
  `EVint 0`. Under `xi`, `step_norm`: a step with trace `t` is also a step
  with trace `norm t` (only external calls produce events, and `nv_write`
  accepts any result); so two steps from the same state whose traces agree
  after `norm` reach the same state (`step_det`).
- `follow`: an execution consistent with the input stays on the reference
  execution, so every behaviour consistent with the input terminates as the
  reference does (`behaves_unique`).
- `binary_of_execution`: through Phase 3's backward simulation
  (`dense_backward`), every behaviour of the binary consistent with the input
  is that one.
-/

namespace NautyVerified.Statement

open CompCert4Lean CompCert4Lean.Common.Events CompCert4Lean.Common.Behaviors
open CompCert4Lean.Common.Smallstep CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Integers
open Hex.GraphIso

/-- Forget the result of every syscall other than `nv_read`. -/
def normEv : event → event
  | .Event_syscall name args res =>
      if name = nameRead ∧ args = [] then .Event_syscall name args res
      else .Event_syscall name args (.EVint Lib.Integers.Int.zero)
  | e => e

def norm (t : trace) : trace := t.map normEv

theorem norm_nil : norm E0 = E0 := rfl

theorem norm_one_vload (c : Common.AST.memory_chunk) (id : Common.AST.ident) (o : Lib.Integers.ptrofs)
    (ev : eventval) : norm [.Event_vload c id o ev] = [.Event_vload c id o ev] := rfl

theorem norm_one_vstore (c : Common.AST.memory_chunk) (id : Common.AST.ident) (o : Lib.Integers.ptrofs)
    (ev : eventval) : norm [.Event_vstore c id o ev] = [.Event_vstore c id o ev] := rfl

theorem norm_one_annot (s : RString) (args : List eventval) :
    norm [.Event_annot s args] = [.Event_annot s args] := rfl

/-- `xi`'s external functions accept the normalised trace. -/
theorem extSem_norm {name : RString} {sg : Common.AST.signature}
    {ge : Common.Globalenvs.Senv.t} {vargs : List val} {m : Common.Memory.mem} {t : trace}
    {v : val} {m' : Common.Memory.mem} (h : extSem name sg ge vargs m t v m') :
    extSem name sg ge vargs m (norm t) v m' := by
  unfold extSem at h ⊢
  by_cases h1 : name = nameRead ∧ sg = sigRead
  · rw [ite_eq_left h1] at h ⊢
    cases h with
    | intro m ev v hm =>
      have : norm [.Event_syscall nameRead [] ev] = [.Event_syscall nameRead [] ev] := by
        simp [norm, normEv] <;> rfl
      rw [this]; exact .intro _ m ev v hm
  · rw [ite_eq_right h1] at h ⊢
    by_cases h2 : name = nameWrite ∧ sg = sigWrite
    · rw [ite_eq_left h2] at h ⊢
      cases h with
      | intro m x r =>
        have : norm [.Event_syscall nameWrite [.EVlong x] (.EVint r)] =
            [.Event_syscall nameWrite [.EVlong x] (.EVint Lib.Integers.Int.zero)] := by
          simp [norm, normEv] <;> rfl
        rw [this]; exact .intro _ m x _
    · rw [ite_eq_right h2] at h ⊢
      exact h.elim

/-- A step's external call accepts the normalised trace. -/
theorem external_call_norm {ef : Common.AST.external_function} {ge : Common.Globalenvs.Senv.t}
    {vargs : List val} {m : Common.Memory.mem} {t : trace} {v : val} {m' : Common.Memory.mem}
    (h : external_call xi ef ge vargs m t v m') : external_call xi ef ge vargs m (norm t) v m' := by
  have builtin : ∀ name sg, builtin_or_external_sem xi name sg ge vargs m t v m' →
      builtin_or_external_sem xi name sg ge vargs m (norm t) v m' := by
    intro name sg h
    unfold builtin_or_external_sem at h ⊢
    cases hl : Common.Builtins.lookup_builtin_function name sg with
    | some bf =>
      simp only [hl] at h ⊢
      cases h; exact .known_builtin_sem_intro _ _ _ (by assumption)
    | none =>
      simp only [hl] at h ⊢
      exact extSem_norm h
  cases ef with
  | EF_external name sg => exact extSem_norm h
  | EF_builtin name sg => exact builtin name sg h
  | EF_runtime name sg => exact builtin name sg h
  | EF_inline_asm text sg _ => exact h.elim
  | _ =>
    suffices e : norm t = t by rw [e]; exact h
    first
      | (cases h with
          | volatile_load_sem_intro _ _ _ _ _ hl => cases hl <;> rfl)
      | (cases h with
          | volatile_store_sem_intro _ _ _ _ _ _ hs => cases hs <;> rfl)
      | (cases h <;> rfl)

/-- A step with trace `t` is also a step with trace `norm t`. -/
theorem step_norm {ge : genv} {s s' : state} {t : trace} (h : step2 xi ge s t s') :
    step2 xi ge s (norm t) s' := by
  have h0 := h
  cases h with
  | step_builtin f result ef argTypes args k e le m vargs t vres m' hargs hcall =>
    exact .step_builtin f result ef argTypes args k e le m vargs _ vres m' hargs
      (external_call_norm hcall)
  | step_external_function ef argTypes resultType cc vargs k m vres t m' hcall =>
    exact .step_external_function ef argTypes resultType cc vargs k m vres _ m'
      (external_call_norm hcall)
  | _ => exact h0

/-- The pinned Clight program's semantics. -/
abbrev L : semantics := semantics2 xi Source.dense.locals

/-- Two steps from the same state whose traces agree after `norm` reach the same state. -/
theorem step_det {s s₁ s₂ : L.state} {t₁ t₂ : trace} (h₁ : L.step L.globalenv s t₁ s₁)
    (h₂ : L.step L.globalenv s t₂ s₂) (ht : norm t₁ = norm t₂) : s₁ = s₂ :=
  ((semantics2_determinate xi Source.dense.locals).sd_determ s _ s₁ _ s₂ (step_norm h₁)
    (ht ▸ step_norm h₂)).2 rfl

/-! ## Traces -/

theorem reads_cons_syscall (name : RString) (args : List eventval) (res : eventval) (t : List event) :
    reads (.Event_syscall name args res :: t) =
      (if name = nameRead ∧ args = [] then
        [(match res with | .EVlong x => some (Foundation.Numbers.Rocq.Coq.intOfZ
            (Lib.Integers.Int64.signed x)) | _ => none)] else []) ++ reads t := by
  cases args with
  | nil =>
    simp only [reads]
    by_cases h : name = nameRead
    · simp [h] <;> rfl
    · simp [h]
  | cons a args => simp [reads]

theorem reads_appendL : ∀ t₁ t₂ : List event, reads (List.append t₁ t₂) = reads t₁ ++ reads t₂
  | [], _ => rfl
  | .Event_syscall name args res :: t₁, t₂ => by
    show reads (.Event_syscall name args res :: List.append t₁ t₂) = _
    rw [reads_cons_syscall, reads_cons_syscall, reads_appendL t₁ t₂, List.append_assoc]
  | .Event_vload _ _ _ _ :: t₁, t₂ => by
    show reads (_ :: List.append t₁ t₂) = _; simp only [reads]; exact reads_appendL t₁ t₂
  | .Event_vstore _ _ _ _ :: t₁, t₂ => by
    show reads (_ :: List.append t₁ t₂) = _; simp only [reads]; exact reads_appendL t₁ t₂
  | .Event_annot _ _ :: t₁, t₂ => by
    show reads (_ :: List.append t₁ t₂) = _; simp only [reads]; exact reads_appendL t₁ t₂

theorem reads_append (t₁ t₂ : trace) : reads (Eapp t₁ t₂) = reads t₁ ++ reads t₂ :=
  reads_appendL t₁ t₂

theorem reads_norm : ∀ t : List event, reads (norm t) = reads t
  | [] => rfl
  | .Event_syscall name args res :: t => by
    show reads (normEv (.Event_syscall name args res) :: List.map normEv t) = _
    simp only [normEv]
    by_cases h : name = nameRead ∧ args = []
    · rw [ite_eq_left h, reads_cons_syscall, reads_cons_syscall]
      exact congrArg _ (reads_norm t)
    · rw [ite_eq_right h, reads_cons_syscall, reads_cons_syscall, ite_eq_right h, ite_eq_right h]
      exact reads_norm t
  | .Event_vload _ _ _ _ :: t => by
    show reads (_ :: List.map normEv t) = _; simp only [normEv, reads]; exact reads_norm t
  | .Event_vstore _ _ _ _ :: t => by
    show reads (_ :: List.map normEv t) = _; simp only [normEv, reads]; exact reads_norm t
  | .Event_annot _ _ :: t => by
    show reads (_ :: List.map normEv t) = _; simp only [normEv, reads]; exact reads_norm t

theorem writes_norm : ∀ t : List event, writes (norm t) = writes t
  | [] => rfl
  | .Event_syscall name args res :: t => by
    show writes (normEv (.Event_syscall name args res) :: List.map normEv t) = _
    have ih : writes (List.map normEv t) = writes t := writes_norm t
    simp only [normEv]
    split <;> rcases args with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> (try cases a) <;> simp only [writes, ih]
  | .Event_vload _ _ _ _ :: t => by
    show writes (_ :: List.map normEv t) = _; simp only [normEv, writes]; exact writes_norm t
  | .Event_vstore _ _ _ _ :: t => by
    show writes (_ :: List.map normEv t) = _; simp only [normEv, writes]; exact writes_norm t
  | .Event_annot _ _ :: t => by
    show writes (_ :: List.map normEv t) = _; simp only [normEv, writes]; exact writes_norm t

theorem reads_normT (t : trace) : reads (norm t) = reads t := reads_norm t

theorem writes_normT (t : trace) : writes (norm t) = writes t := writes_norm t

theorem norm_append (t₁ t₂ : trace) : norm (Eapp t₁ t₂) = Eapp (norm t₁) (norm t₂) := List.map_append

theorem VloadsZero.left {t₁ t₂ : trace} (h : VloadsZero (Eapp t₁ t₂)) : VloadsZero t₁ :=
  fun c id o ev hm => h c id o ev (List.mem_append_left (as := (t₁ : List event)) t₂ hm)

theorem VloadsZero.right {t₁ t₂ : trace} (h : VloadsZero (Eapp t₁ t₂)) : VloadsZero t₂ :=
  fun c id o ev hm => h c id o ev (List.mem_append_right (bs := (t₂ : List event)) t₁ hm)

theorem L_determinate : determinate L := semantics2_determinate xi Source.dense.locals

theorem intOfZ_signed_inj {x y : Lib.Integers.int64}
    (h : Foundation.Numbers.Rocq.Coq.intOfZ (Lib.Integers.Int64.signed x) =
      Foundation.Numbers.Rocq.Coq.intOfZ (Lib.Integers.Int64.signed y)) : x = y := by
  rw [NautyVerified.Word.intOfZ_Int64_signed, NautyVerified.Word.intOfZ_Int64_signed] at h
  exact NautyVerified.Word.bv64_inj.1 (BitVec.toInt_inj.1 h)

/-- Two first steps from the same state, with the read results of the first
trace a prefix of the second's (which are all integers) and volatile loads of
zero: their traces agree after `norm`, so they reach the same state. -/
theorem first_match {s s₁ s₂ : L.state} {t₁ u₁ : trace} {t₂ u₂ : trace}
    (h₁ : L.step L.globalenv s t₁ s₁) (h₂ : L.step L.globalenv s u₁ s₂)
    (hr : reads (Eapp t₁ t₂) <+: reads (Eapp u₁ u₂)) (hnone : none ∉ reads (Eapp u₁ u₂))
    (hv₁ : VloadsZero t₁) (hv₂ : VloadsZero u₁) : norm t₁ = norm u₁ ∧ s₁ = s₂ := by
  have hm := (L_determinate.sd_determ s t₁ s₁ u₁ s₂ h₁ h₂).1
  rw [reads_append, reads_append] at hr
  rw [reads_append] at hnone
  have hn : norm t₁ = norm u₁ := by
    cases hm with
    | match_traces_E0 => rfl
    | match_traces_syscall id args r1 r2 _ _ _ =>
      by_cases hk : id = nameRead ∧ args = []
      · obtain ⟨rfl, rfl⟩ := hk
        simp only [reads, ite_true, List.singleton_append] at hr hnone
        have hh := (List.cons_prefix_cons.1 hr).1
        cases r2 with
        | EVlong x2 =>
          cases r1 with
          | EVlong x1 =>
            simp only [Option.some.injEq] at hh
            rw [intOfZ_signed_inj hh]
          | _ => simp at hh
        | _ => simp at hnone
      · simp [norm, normEv, hk] <;> rfl
    | match_traces_vload chunk id ofs r1 r2 _ _ _ =>
      have e1 := hv₁ chunk id ofs r1 (List.Mem.head _)
      have e2 := hv₂ chunk id ofs r2 (List.Mem.head _)
      subst e1 e2; rfl
    | match_traces_vstore => rfl
    | match_traces_annot => rfl
  exact ⟨hn, step_det h₁ h₂ hn⟩

abbrev LStar := star L.step L.globalenv

theorem eapp_assoc (a b c : trace) : Eapp (Eapp a b) c = Eapp a (Eapp b c) := List.append_assoc a b c

/-- An execution whose reads are a prefix of the reference execution's, with
volatile loads of zero, stays on the reference execution. -/
theorem follow {s s' : L.state} {t : trace} (h : LStar s t s') :
    ∀ {t₀ : trace} {sF : L.state} {r : Lib.Integers.int}, LStar s t₀ sF → L.final_state sF r →
      reads t <+: reads t₀ → none ∉ reads t₀ → VloadsZero t → VloadsZero t₀ →
      ∃ t₀a t₀b, t₀ = Eapp t₀a t₀b ∧ norm t = norm t₀a ∧ LStar s' t₀b sF := by
  induction h with
  | star_refl s => intro t₀ sF r href _ _ _ _ _; exact ⟨E0, t₀, rfl, rfl, href⟩
  | star_step s1 t1 s2 t2 s3 t hstep hstar htrace ih =>
    intro t₀ sF r href hfin hr hnone hv hv₀
    cases href with
    | star_refl =>
      exact absurd hstep (L_determinate.sd_final_nostep _ r hfin t1 s2)
    | star_step _ u1 r2 u2 _ _ hstep' hstar' htrace' =>
      subst htrace htrace'
      obtain ⟨hn, rfl⟩ := first_match hstep hstep' hr hnone hv.left hv₀.left
      have hreads : reads t1 = reads u1 := by rw [← reads_normT t1, hn, reads_normT]
      rw [reads_append, reads_append, hreads] at hr
      rw [reads_append] at hnone
      obtain ⟨u2a, u2b, rfl, hn2, hst⟩ := ih hstar' hfin ((List.prefix_append_right_inj _).1 hr)
        (fun hm => hnone (List.mem_append_right _ hm)) hv.right hv₀.right
      refine ⟨Eapp u1 u2a, u2b, (eapp_assoc _ _ _).symm, ?_, hst⟩
      rw [norm_append, norm_append, hn, hn2]

/-- A state on the way to a final state does not diverge silently. -/
theorem not_silent {s sF : L.state} {t : trace} {r : Lib.Integers.int} (h : LStar s t sF)
    (hfin : L.final_state sF r) (hs : forever_silent L.step L.globalenv s) : False := by
  induction h with
  | star_refl s =>
    refine forever_silent_casesOn (motive := fun x => x = s → False) ?_ hs rfl
    intro x s2 hstep _ hx
    subst hx
    exact L_determinate.sd_final_nostep _ r hfin _ _ hstep
  | star_step s1 u1 r2 u2 s3 _ hstep hstar _ ih =>
    refine forever_silent_casesOn (motive := fun x => x = s1 → False) ?_ hs rfl
    intro x s2 hstep2 hrest hx
    subst hx
    have hm := (L_determinate.sd_determ _ _ _ _ _ hstep2 hstep).1
    have hu : u1 = E0 := by cases hm; rfl
    subst hu
    have := (L_determinate.sd_determ _ _ _ _ _ hstep2 hstep).2 rfl
    subst this
    exact ih hfin hrest

theorem length_norm (t : trace) : (norm t).length = t.length := List.length_map _

theorem length_eapp (a b : trace) : (Eapp a b).length = a.length + b.length :=
  List.length_append

theorem range_map_eappinf (T : traceinf) :
    ∀ (t : trace) (k : Nat), (List.range (t.length + k)).map (Eappinf t T) =
      Eapp t ((List.range k).map T)
  | [], k => by simp [Eappinf, Eapp]
  | e :: t, k => by
    rw [show (e :: t : trace).length + k = (t.length + k) + 1 by simp; omega, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    show _ :: _ = e :: Eapp t _
    congr 1
    rw [← range_map_eappinf T t k]
    rfl

/-- A reactive execution has finite prefixes of every length, reading the
behaviour's first events. -/
theorem reacts_prefix : ∀ (k : Nat) {s : L.state} {T : traceinf},
    forever_reactive L.step L.globalenv s T →
    ∃ t s', LStar s t s' ∧ k ≤ t.length ∧ (List.range t.length).map T = t
  | 0, s, T, _ => ⟨E0, s, star.star_refl _, Nat.le_refl _, rfl⟩
  | k + 1, s, T, h => by
    refine forever_reactive_casesOn (motive := fun s T =>
      ∃ t s', LStar s t s' ∧ k + 1 ≤ t.length ∧ (List.range t.length).map T = t) ?_ h
    intro s1 s2 t1 T' hst hne hrest
    obtain ⟨t2, s3, hst2, hk, hpre⟩ := reacts_prefix k hrest
    refine ⟨Eapp t1 t2, s3, star_trans' hst hst2, ?_, ?_⟩
    · have : t1.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
      rw [length_eapp]; omega
    · rw [length_eapp, range_map_eappinf, hpre]
where
  star_trans' {a b c : L.state} {t u : trace} (h₁ : LStar a t b) (h₂ : LStar b u c) :
      LStar a (Eapp t u) c := by
    induction h₁ with
    | star_refl => exact h₂
    | star_step s1 t1 s2 t2 s3 t hstep _ htr ih =>
      exact star.star_step s1 t1 s2 (Eapp t2 u) c _ hstep (ih h₂) (by rw [htr, eapp_assoc])

/-- Every behaviour of the pinned Clight program consistent with the input is
the reference execution's termination, with the same writes. -/
theorem behaves_unique {s₀ sF : L.state} {t₀ : trace} {r₀ : Lib.Integers.int} {ins : List Int}
    (hinit : L.initial_state s₀) (hstar : LStar s₀ t₀ sF) (hfin : L.final_state sF r₀)
    (hreads : reads t₀ = ins.map some) (hv₀ : VloadsZero t₀)
    {beh : program_behavior} (hbeh : program_behaves L beh) (hcons : Consistent ins beh) :
    ∃ t, beh = .Terminates t r₀ ∧ writes t = writes t₀ := by
  have hnone : none ∉ reads t₀ := by rw [hreads]; simp
  have pre : ∀ {t : trace}, reads t <+: ins.map some → reads t <+: reads t₀ := fun h =>
    hreads ▸ h
  cases hbeh with
  | program_goes_initially_wrong hno => exact absurd hinit (hno s₀)
  | program_runs s _ hinit' hbehaves =>
    have hs : s = s₀ := L_determinate.sd_initial_determ _ _ hinit' hinit
    subst hs
    cases hbehaves with
    | state_terminates t s' r hst hfinal =>
      obtain ⟨hr, hv⟩ := hcons
      obtain ⟨a, b, ht0, hn, hrest⟩ := follow hst hstar hfin (pre hr) hnone hv hv₀
      cases hrest with
      | star_refl =>
        have hr' : r = r₀ := L_determinate.sd_final_determ _ _ _ hfinal hfin
        subst hr'
        refine ⟨t, rfl, ?_⟩
        have : t₀ = a := by rw [ht0]; exact List.append_nil a
        rw [this, ← writes_normT t, hn, writes_normT]
      | star_step _ _ _ _ _ _ hstep _ _ =>
        exact absurd hstep (L_determinate.sd_final_nostep _ r hfinal _ _)
    | state_diverges t s' hst hforever =>
      obtain ⟨hr, hv⟩ := hcons
      obtain ⟨a, b, _, _, hrest⟩ := follow hst hstar hfin (pre hr) hnone hv hv₀
      exact (not_silent hrest hfin hforever).elim
    | state_reacts T hforever =>
      obtain ⟨t, s', hst, hk, hpre⟩ := reacts_prefix (t₀.length + 1) hforever
      obtain ⟨hr, hv⟩ := hcons t.length
      rw [hpre] at hr hv
      obtain ⟨a, b, ht0, hn, _⟩ := follow hst hstar hfin (pre hr) hnone hv hv₀
      have h1 : t.length = a.length := by
        rw [← length_norm t, hn, length_norm]
      have h2 : t₀.length = a.length + b.length := by rw [ht0]; exact length_eapp a b
      omega
    | state_goes_wrong t s' hst hnostep hnofinal =>
      obtain ⟨hr, hv⟩ := hcons
      obtain ⟨a, b, _, _, hrest⟩ := follow hst hstar hfin (pre hr) hnone hv hv₀
      cases hrest with
      | star_refl => exact (hnofinal r₀ hfin).elim
      | star_step _ _ _ _ _ _ hstep _ _ => exact (hnostep _ _ hstep).elim

theorem prefix_reads {t u : trace} {l : List (Option Int)} (h : reads (Eapp t u) <+: l) :
    reads t <+: l := by
  rw [reads_append] at h; exact (List.prefix_append _ _).trans h

/-- A behaviour consistent with the input that starts with `t` makes `Goes_wrong t`
consistent too. -/
theorem consistent_prefix {ins : List Int} {t : trace} {beh : program_behavior}
    (h : Consistent ins (behavior_app t beh)) : Consistent ins (.Goes_wrong t) := by
  cases beh with
  | Terminates t1 r => exact ⟨prefix_reads h.1, h.2.left⟩
  | Diverges t1 => exact ⟨prefix_reads h.1, h.2.left⟩
  | Goes_wrong t1 => exact ⟨prefix_reads h.1, h.2.left⟩
  | Reacts T =>
    have hk := h t.length
    have e : (List.range t.length).map (Eappinf t T) = t := by
      have := range_map_eappinf T t 0
      simp only [Nat.add_zero, List.range_zero, List.map_nil] at this
      exact this.trans (List.append_nil (as := (t : List event)))
    rw [e] at hk
    exact hk

/-- One execution of the pinned Clight program that reads the input and
writes `expected G` determines every behaviour of the binary consistent with
the input. -/
theorem binary_of_execution {n k : Nat} (G : Colored n k) {ins : List Int} {tp : X86.Asm.program}
    (hc : Compiled tp)
    (hex : ∃ s₀ sF t₀, L.initial_state s₀ ∧ LStar s₀ t₀ sF ∧
      L.final_state sF (Lib.Integers.Int.repr .Z0) ∧ reads t₀ = ins.map some ∧ VloadsZero t₀ ∧
      writes t₀ = expected G) :
    ∀ beh, program_behaves (X86.Asm.semantics Build.config xi tp) beh → Consistent ins beh →
      ∃ t, beh = .Terminates t (Lib.Integers.Int.repr .Z0) ∧ writes t = expected G := by
  intro beh hbeh hcons
  obtain ⟨s₀, sF, t₀, hinit, hstar, hfin, hreads, hv₀, hw⟩ := hex
  obtain ⟨beh₁, hbeh₁, himp⟩ :=
    backward_simulation_behavior_improves _ _ (dense_backward tp hc xi) beh hbeh
  rcases himp with rfl | ⟨t, rfl, beh', rfl⟩
  · obtain ⟨t, rfl, hwt⟩ := behaves_unique hinit hstar hfin hreads hv₀ hbeh₁ hcons
    exact ⟨t, rfl, hwt.trans hw⟩
  · obtain ⟨_, h, _⟩ := behaves_unique hinit hstar hfin hreads hv₀ hbeh₁ (consistent_prefix hcons)
    cases h

end NautyVerified.Statement

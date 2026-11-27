import NautyVerified.Exec.Expr

/-!
# A program logic for Clight, defined by the semantics

Triples are statements about CompCert4Lean's Clight transition relation
(`step` with `function_entry2`, the semantics of SimplLocals output), so the
logic needs no separate soundness theorem: each rule is proved from the step
relation.

The logic is total and existential: `Triple f P s Q` says that from every state
satisfying `P`, *some* execution of `s` finishes (normally, by `break`, by
`continue`, or by `return`) in a state satisfying `Q`, emitting a trace that `Q`
also sees. Existence suffices for the end-to-end theorem because Clight is
deterministic once external calls are (`Determinism.lean`), so the execution
found is the only one.

The design follows CLean's `CCLib.Hoare` (Certora), adapted to
CompCert4Lean's semantics and extended with traces, which nauty needs: the
automorphism callback writes output from inside the search.
-/

namespace NautyVerified.Logic

open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Cfrontend.Ctypes CompCert4Lean.Cfrontend.Cop CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open CompCert4Lean.Flocq.IEEE754.Binary (BinaryNormalizeCertificate)

instance : Append trace := inferInstanceAs (Append (List event))

@[simp] theorem E0_append (t : trace) : E0 ++ t = t := List.nil_append t
@[simp] theorem append_E0 (t : trace) : t ++ E0 = t := List.append_nil t
theorem trace_append_assoc (a b c : trace) : a ++ b ++ c = a ++ (b ++ c) := List.append_assoc a b c

variable [binary64_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable (xi : ExternalCalls) (ge : genv)

/-- One Clight step of SimplLocals output. -/
abbrev Step (s : state) (t : trace) (s' : state) : Prop :=
  step xi ge (function_entry2 ge) s t s'

/-- Finitely many steps, with the trace they emit. -/
inductive Steps : state → trace → state → Prop where
  | refl (s : state) : Steps s E0 s
  | step {s1 s2 s3 : state} {t1 t2 : trace} :
      Step xi ge s1 t1 s2 → Steps s2 t2 s3 → Steps s1 (t1 ++ t2) s3

variable {xi ge}

namespace Steps

theorem trans {s1 s2 s3 : state} {t1 t2 : trace} (h1 : Steps xi ge s1 t1 s2)
    (h2 : Steps xi ge s2 t2 s3) : Steps xi ge s1 (t1 ++ t2) s3 := by
  induction h1 with
  | refl => simpa using h2
  | step h _ ih => rw [trace_append_assoc]; exact Steps.step h (ih h2)

theorem one {s1 s2 : state} {t : trace} (h : Step xi ge s1 t s2) : Steps xi ge s1 t s2 := by
  simpa using Steps.step h (Steps.refl s2)

/-- A silent step followed by more steps. -/
theorem silent {s1 s2 s3 : state} {t : trace} (h : Step xi ge s1 E0 s2)
    (h2 : Steps xi ge s2 t s3) : Steps xi ge s1 t s3 := by
  simpa using Steps.step h h2

/-- `Steps` is CompCert's `star`. -/
theorem toStar {s1 s2 : state} {t : trace} (h : Steps xi ge s1 t s2) :
    Common.Smallstep.star (fun ge => CompCert4Lean.Cfrontend.Clight.step xi ge (function_entry2 ge)) ge s1 t s2 := by
  induction h with
  | refl s => exact .star_refl s
  | step h _ ih => exact .star_step _ _ _ _ _ _ h ih rfl

end Steps

/-! ## Assertions, outcomes, triples -/

/-- An assertion on a function's local environment, temporaries and memory. -/
abbrev Assn := env → temp_env → mem → Prop

/-- What a statement's postcondition constrains, for each way it can finish.
Every component also receives the trace emitted. -/
structure Post where
  normal : trace → Assn
  brk : trace → Assn := fun _ _ _ _ => False
  cont : trace → Assn := fun _ _ _ _ => False
  /-- After `return`: the returned value and the memory once locals are freed. -/
  ret : trace → val → mem → Prop := fun _ _ _ => False

/-- `s`, run in function `f` from any continuation `k`, finishes as `Q` allows. -/
def Triple (f : function) (P : Assn) (s : statement) (Q : Post) : Prop :=
  ∀ (k : cont) (e : env) (le : temp_env) (m : mem), P e le m →
    (∃ t le' m', Steps xi ge (.State f s k e le m) t (.State f .Sskip k e le' m') ∧
        Q.normal t e le' m') ∨
    (∃ t le' m', Steps xi ge (.State f s k e le m) t (.State f .Sbreak k e le' m') ∧
        Q.brk t e le' m') ∨
    (∃ t le' m', Steps xi ge (.State f s k e le m) t (.State f .Scontinue k e le' m') ∧
        Q.cont t e le' m') ∨
    (∃ t v m', Steps xi ge (.State f s k e le m) t (.Returnstate v (call_cont k) m') ∧
        Q.ret t v m')

variable (xi ge) in
/-- The triple, with the semantics made explicit. -/
abbrev TripleIn := @Triple binary64_certificate binary32_certificate xi ge

/-! ## Structural rules -/

theorem triple_conseq {f : function} {P P' : Assn} {s : statement} {Q Q' : Post}
    (hP : ∀ e le m, P' e le m → P e le m)
    (hn : ∀ t e le m, Q.normal t e le m → Q'.normal t e le m)
    (hb : ∀ t e le m, Q.brk t e le m → Q'.brk t e le m)
    (hc : ∀ t e le m, Q.cont t e le m → Q'.cont t e le m)
    (hr : ∀ t v m, Q.ret t v m → Q'.ret t v m)
    (h : Triple (xi := xi) (ge := ge) f P s Q) : Triple (xi := xi) (ge := ge) f P' s Q' := by
  intro k e le m hp
  rcases h k e le m (hP _ _ _ hp) with ⟨t, le', m', hs, hq⟩ | ⟨t, le', m', hs, hq⟩ |
      ⟨t, le', m', hs, hq⟩ | ⟨t, v, m', hs, hq⟩
  · exact .inl ⟨t, le', m', hs, hn _ _ _ _ hq⟩
  · exact .inr (.inl ⟨t, le', m', hs, hb _ _ _ _ hq⟩)
  · exact .inr (.inr (.inl ⟨t, le', m', hs, hc _ _ _ _ hq⟩))
  · exact .inr (.inr (.inr ⟨t, v, m', hs, hr _ _ _ hq⟩))

theorem triple_pre {f : function} {P P' : Assn} {s : statement} {Q : Post}
    (hP : ∀ e le m, P' e le m → P e le m) (h : Triple (xi := xi) (ge := ge) f P s Q) :
    Triple (xi := xi) (ge := ge) f P' s Q :=
  triple_conseq hP (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ _ _ h => h) h

/-- Existential preconditions. -/
theorem triple_exists {α : Sort _} {f : function} {P : α → Assn} {s : statement} {Q : Post}
    (h : ∀ a, Triple (xi := xi) (ge := ge) f (P a) s Q) :
    Triple (xi := xi) (ge := ge) f (fun e le m => ∃ a, P a e le m) s Q := by
  intro k e le m ⟨a, hp⟩
  exact h a k e le m hp

theorem triple_skip {f : function} {P : Assn} :
    Triple (xi := xi) (ge := ge) f P .Sskip { normal := fun t e le m => t = E0 ∧ P e le m } := by
  intro k e le m hp
  exact .inl ⟨E0, le, m, .refl _, rfl, hp⟩

theorem triple_break {f : function} {P : Assn} :
    Triple (xi := xi) (ge := ge) f P .Sbreak
      { normal := fun _ _ _ _ => False, brk := fun t e le m => t = E0 ∧ P e le m } := by
  intro k e le m hp
  exact .inr (.inl ⟨E0, le, m, .refl _, rfl, hp⟩)

theorem triple_continue {f : function} {P : Assn} :
    Triple (xi := xi) (ge := ge) f P .Scontinue
      { normal := fun _ _ _ _ => False, cont := fun t e le m => t = E0 ∧ P e le m } := by
  intro k e le m hp
  exact .inr (.inr (.inl ⟨E0, le, m, .refl _, rfl, hp⟩))

/-- Prefix a trace: what `Q` allows after `t₀` has already been emitted. -/
def Post.after (t₀ : trace) (Q : Post) : Post where
  normal t := Q.normal (t₀ ++ t)
  brk t := Q.brk (t₀ ++ t)
  cont t := Q.cont (t₀ ++ t)
  ret t := Q.ret (t₀ ++ t)

/-- Sequencing. The second statement's precondition is the first's normal
postcondition with the trace so far; the other exits of the first pass through. -/
theorem triple_seq {f : function} {P : Assn} {s1 s2 : statement} {R : trace → Assn} {Q : Post}
    (h1 : Triple (xi := xi) (ge := ge) f P s1
      { normal := R, brk := Q.brk, cont := Q.cont, ret := Q.ret })
    (h2 : ∀ t₁, Triple (xi := xi) (ge := ge) f (R t₁) s2 (Q.after t₁)) :
    Triple (xi := xi) (ge := ge) f P (.Ssequence s1 s2) Q := by
  intro k e le m hp
  have hseq : Step xi ge (.State f (.Ssequence s1 s2) k e le m) E0
      (.State f s1 (.Kseq s2 k) e le m) := .step_seq _ _ _ _ _ _ _
  rcases h1 (.Kseq s2 k) e le m hp with ⟨t, le', m', hs, hq⟩ | ⟨t, le', m', hs, hq⟩ |
      ⟨t, le', m', hs, hq⟩ | ⟨t, v, m', hs, hq⟩
  · -- normal: continue with s2
    have hskip : Step xi ge (.State f .Sskip (.Kseq s2 k) e le' m') E0 (.State f s2 k e le' m') :=
      .step_skip_seq _ _ _ _ _ _
    rcases h2 t k e le' m' hq with ⟨t2, le2, m2, hs2, hq2⟩ | ⟨t2, le2, m2, hs2, hq2⟩ |
        ⟨t2, le2, m2, hs2, hq2⟩ | ⟨t2, v, m2, hs2, hq2⟩
    · exact .inl ⟨t ++ t2, le2, m2, Steps.silent hseq (hs.trans (Steps.silent hskip hs2)), hq2⟩
    · exact .inr (.inl ⟨t ++ t2, le2, m2,
        Steps.silent hseq (hs.trans (Steps.silent hskip hs2)), hq2⟩)
    · exact .inr (.inr (.inl ⟨t ++ t2, le2, m2,
        Steps.silent hseq (hs.trans (Steps.silent hskip hs2)), hq2⟩))
    · exact .inr (.inr (.inr ⟨t ++ t2, v, m2,
        Steps.silent hseq (hs.trans (Steps.silent hskip hs2)), hq2⟩))
  · -- break out of s1: propagates past s2
    have hb : Step xi ge (.State f .Sbreak (.Kseq s2 k) e le' m') E0 (.State f .Sbreak k e le' m') :=
      .step_break_seq _ _ _ _ _ _
    exact .inr (.inl ⟨t, le', m', Steps.silent hseq (by simpa using hs.trans (Steps.one hb)), hq⟩)
  · have hc : Step xi ge (.State f .Scontinue (.Kseq s2 k) e le' m') E0
        (.State f .Scontinue k e le' m') := .step_continue_seq _ _ _ _ _ _
    exact .inr (.inr (.inl ⟨t, le', m',
      Steps.silent hseq (by simpa using hs.trans (Steps.one hc)), hq⟩))
  · exact .inr (.inr (.inr ⟨t, v, m', Steps.silent hseq (by simpa [call_cont] using hs), hq⟩))

/-! ## Assignment to temporaries -/

theorem triple_set {f : function} {P : Assn} {id : ident} {a : expr} {Q : Post}
    (h : ∀ e le m, P e le m → ∃ v, Exec.evalExpr ge e le m a = some v ∧
      Q.normal E0 e (PTree.set id v le) m) :
    Triple (xi := xi) (ge := ge) f P (.Sset id a) Q := by
  intro k e le m hp
  obtain ⟨v, hv, hq⟩ := h e le m hp
  exact .inl ⟨E0, _, m, Steps.one (.step_set _ _ _ _ _ _ _ _ (Exec.evalExpr_sound hv)), hq⟩

/-! ## Assignment through memory -/

theorem triple_assign {f : function} {P : Assn} {a1 a2 : expr} {Q : Post}
    (h : ∀ e le m, P e le m → ∃ loc ofs bf v2 v m',
      Exec.evalLvalue ge e le m a1 = some (loc, ofs, bf) ∧
      Exec.evalExpr ge e le m a2 = some v2 ∧
      sem_cast v2 (typeof a2) (typeof a1) m = some v ∧
      Exec.assignLoc ge.genv_cenv (typeof a1) m loc ofs v bf = some m' ∧
      Q.normal E0 e le m') :
    Triple (xi := xi) (ge := ge) f P (.Sassign a1 a2) Q := by
  intro k e le m hp
  obtain ⟨loc, ofs, bf, v2, v, m', hl, hr, hc, ha, hq⟩ := h e le m hp
  exact .inl ⟨E0, le, m', Steps.one (.step_assign _ _ _ _ _ _ _ _ _ _ _ _ _
    (Exec.evalLvalue_sound hl) (Exec.evalExpr_sound hr) hc (Exec.assignLoc_sound ha)), hq⟩

/-! ## Conditionals -/

theorem triple_if {f : function} {P : Assn} {a : expr} {s1 s2 : statement} {Q : Post}
    (hc : ∀ e le m, P e le m → ∃ v b, Exec.evalExpr ge e le m a = some v ∧
      bool_val v (typeof a) m = some b)
    (h1 : Triple (xi := xi) (ge := ge) f (fun e le m => P e le m ∧ ∃ v,
      Exec.evalExpr ge e le m a = some v ∧ bool_val v (typeof a) m = some true) s1 Q)
    (h2 : Triple (xi := xi) (ge := ge) f (fun e le m => P e le m ∧ ∃ v,
      Exec.evalExpr ge e le m a = some v ∧ bool_val v (typeof a) m = some false) s2 Q) :
    Triple (xi := xi) (ge := ge) f P (.Sifthenelse a s1 s2) Q := by
  intro k e le m hp
  obtain ⟨v, b, hv, hb⟩ := hc e le m hp
  have hstep : Step xi ge (.State f (.Sifthenelse a s1 s2) k e le m) E0
      (.State f (if b then s1 else s2) k e le m) :=
    .step_ifthenelse _ _ _ _ _ _ _ _ _ _ (Exec.evalExpr_sound hv) hb
  cases b with
  | true =>
    rcases h1 k e le m ⟨hp, v, hv, hb⟩ with ⟨t, le', m', hs, hq⟩ | ⟨t, le', m', hs, hq⟩ |
        ⟨t, le', m', hs, hq⟩ | ⟨t, v', m', hs, hq⟩
    · exact .inl ⟨t, le', m', Steps.silent hstep hs, hq⟩
    · exact .inr (.inl ⟨t, le', m', Steps.silent hstep hs, hq⟩)
    · exact .inr (.inr (.inl ⟨t, le', m', Steps.silent hstep hs, hq⟩))
    · exact .inr (.inr (.inr ⟨t, v', m', Steps.silent hstep hs, hq⟩))
  | false =>
    rcases h2 k e le m ⟨hp, v, hv, hb⟩ with ⟨t, le', m', hs, hq⟩ | ⟨t, le', m', hs, hq⟩ |
        ⟨t, le', m', hs, hq⟩ | ⟨t, v', m', hs, hq⟩
    · exact .inl ⟨t, le', m', Steps.silent hstep hs, hq⟩
    · exact .inr (.inl ⟨t, le', m', Steps.silent hstep hs, hq⟩)
    · exact .inr (.inr (.inl ⟨t, le', m', Steps.silent hstep hs, hq⟩))
    · exact .inr (.inr (.inr ⟨t, v', m', Steps.silent hstep hs, hq⟩))

/-! ## Return -/

theorem triple_return_some {f : function} {P : Assn} {a : expr} {Q : Post}
    (h : ∀ e le m, P e le m → ∃ v v' m', Exec.evalExpr ge e le m a = some v ∧
      sem_cast v (typeof a) f.fn_return m = some v' ∧
      Mem.free_list m (blocks_of_env ge e) = some m' ∧ Q.ret E0 v' m') :
    Triple (xi := xi) (ge := ge) f P (.Sreturn (some a)) Q := by
  intro k e le m hp
  obtain ⟨v, v', m', hv, hc, hf, hq⟩ := h e le m hp
  exact .inr (.inr (.inr ⟨E0, v', m',
    Steps.one (.step_return_1 _ _ _ _ _ _ _ _ _ (Exec.evalExpr_sound hv) hc hf), hq⟩))

theorem triple_return_none {f : function} {P : Assn} {Q : Post}
    (h : ∀ e le m, P e le m → ∃ m', Mem.free_list m (blocks_of_env ge e) = some m' ∧
      Q.ret E0 .Vundef m') :
    Triple (xi := xi) (ge := ge) f P (.Sreturn none) Q := by
  intro k e le m hp
  obtain ⟨m', hf, hq⟩ := h e le m hp
  exact .inr (.inr (.inr ⟨E0, .Vundef, m', Steps.one (.step_return_0 _ _ _ _ _ _ hf), hq⟩))

/-! ## Loops

`Sloop body iter` runs `body`, then `iter`, then repeats; `break` in either
leaves the loop normally, `continue` in `body` skips to `iter`. The invariant
`I n t` is indexed by a variant `n`, which must decrease on every iteration,
and by the trace `t` emitted since the loop began; `J n t` holds between
`body` and `iter`. -/

theorem triple_loop {f : function} {body iter : statement} {I J : Nat → trace → Assn}
    {Q : Post}
    (hbody : ∀ n t, Triple (xi := xi) (ge := ge) f (I n t) body
      { normal := fun t' => J n (t ++ t'), cont := fun t' => J n (t ++ t'),
        brk := fun t' => Q.normal (t ++ t'), ret := fun t' => Q.ret (t ++ t') })
    (hiter : ∀ n t, Triple (xi := xi) (ge := ge) f (J n t) iter
      { normal := fun t' e le m => ∃ n' < n, I n' (t ++ t') e le m,
        brk := fun t' => Q.normal (t ++ t'), ret := fun t' => Q.ret (t ++ t') }) :
    ∀ n, Triple (xi := xi) (ge := ge) f (I n E0) (.Sloop body iter) Q := by
  -- Generalise the trace so far, then induct on the variant.
  suffices H : ∀ n t, ∀ k e le m, I n t e le m →
      (∃ t' le' m', Steps xi ge (.State f (.Sloop body iter) k e le m) t'
          (.State f .Sskip k e le' m') ∧ Q.normal (t ++ t') e le' m') ∨
      (∃ t' v m', Steps xi ge (.State f (.Sloop body iter) k e le m) t'
          (.Returnstate v (call_cont k) m') ∧ Q.ret (t ++ t') v m') by
    intro n k e le m hp
    rcases H n E0 k e le m hp with ⟨t', le', m', hs, hq⟩ | ⟨t', v, m', hs, hq⟩
    · exact .inl ⟨t', le', m', hs, by simpa using hq⟩
    · exact .inr (.inr (.inr ⟨t', v, m', hs, by simpa using hq⟩))
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro t k e le m hp
  have hloop : Step xi ge (.State f (.Sloop body iter) k e le m) E0
      (.State f body (.Kloop1 body iter k) e le m) := .step_loop _ _ _ _ _ _ _
  -- After the body, either run `iter` or leave.
  have afterIter : ∀ t₁ le₁ m₁, J n (t ++ t₁) e le₁ m₁ →
      (∃ t' le' m', Steps xi ge (.State f iter (.Kloop2 body iter k) e le₁ m₁) t'
          (.State f .Sskip k e le' m') ∧ Q.normal (t ++ t₁ ++ t') e le' m') ∨
      (∃ t' v m', Steps xi ge (.State f iter (.Kloop2 body iter k) e le₁ m₁) t'
          (.Returnstate v (call_cont k) m') ∧ Q.ret (t ++ t₁ ++ t') v m') := by
    intro t₁ le₁ m₁ hj
    rcases hiter n (t ++ t₁) (.Kloop2 body iter k) e le₁ m₁ hj with
        ⟨t₂, le₂, m₂, hs, n', hn', hi⟩ | ⟨t₂, le₂, m₂, hs, hq⟩ | ⟨t₂, le₂, m₂, hs, hq⟩ |
        ⟨t₂, v, m₂, hs, hq⟩
    · -- next iteration
      have hback : Step xi ge (.State f .Sskip (.Kloop2 body iter k) e le₂ m₂) E0
          (.State f (.Sloop body iter) k e le₂ m₂) := .step_skip_loop2 _ _ _ _ _ _ _
      rcases ih n' hn' (t ++ t₁ ++ t₂) k e le₂ m₂ hi with ⟨t₃, le₃, m₃, hs3, hq3⟩ |
          ⟨t₃, v, m₃, hs3, hq3⟩
      · exact .inl ⟨t₂ ++ t₃, le₃, m₃, hs.trans (Steps.silent hback hs3),
          by simpa [trace_append_assoc] using hq3⟩
      · exact .inr ⟨t₂ ++ t₃, v, m₃, hs.trans (Steps.silent hback hs3),
          by simpa [trace_append_assoc] using hq3⟩
    · have hout : Step xi ge (.State f .Sbreak (.Kloop2 body iter k) e le₂ m₂) E0
          (.State f .Sskip k e le₂ m₂) := .step_break_loop2 _ _ _ _ _ _ _
      exact .inl ⟨t₂, le₂, m₂, by simpa using hs.trans (Steps.one hout), hq⟩
    · exact absurd hq id
    · exact .inr ⟨t₂, v, m₂, by simpa [call_cont] using hs, hq⟩
  rcases hbody n t (.Kloop1 body iter k) e le m hp with ⟨t₁, le₁, m₁, hs, hj⟩ |
      ⟨t₁, le₁, m₁, hs, hq⟩ | ⟨t₁, le₁, m₁, hs, hj⟩ | ⟨t₁, v, m₁, hs, hq⟩
  · have hnext : Step xi ge (.State f .Sskip (.Kloop1 body iter k) e le₁ m₁) E0
        (.State f iter (.Kloop2 body iter k) e le₁ m₁) :=
      .step_skip_or_continue_loop1 _ _ _ _ _ _ _ _ (.inl rfl)
    rcases afterIter t₁ le₁ m₁ hj with ⟨t', le', m', hs', hq⟩ | ⟨t', v, m', hs', hq⟩
    · exact .inl ⟨t₁ ++ t', le', m', Steps.silent hloop (hs.trans (Steps.silent hnext hs')),
        by simpa [trace_append_assoc] using hq⟩
    · exact .inr ⟨t₁ ++ t', v, m', Steps.silent hloop (hs.trans (Steps.silent hnext hs')),
        by simpa [trace_append_assoc] using hq⟩
  · have hout : Step xi ge (.State f .Sbreak (.Kloop1 body iter k) e le₁ m₁) E0
        (.State f .Sskip k e le₁ m₁) := .step_break_loop1 _ _ _ _ _ _ _
    exact .inl ⟨t₁, le₁, m₁, Steps.silent hloop (by simpa using hs.trans (Steps.one hout)), hq⟩
  · have hnext : Step xi ge (.State f .Scontinue (.Kloop1 body iter k) e le₁ m₁) E0
        (.State f iter (.Kloop2 body iter k) e le₁ m₁) :=
      .step_skip_or_continue_loop1 _ _ _ _ _ _ _ _ (.inr rfl)
    rcases afterIter t₁ le₁ m₁ hj with ⟨t', le', m', hs', hq⟩ | ⟨t', v, m', hs', hq⟩
    · exact .inl ⟨t₁ ++ t', le', m', Steps.silent hloop (hs.trans (Steps.silent hnext hs')),
        by simpa [trace_append_assoc] using hq⟩
    · exact .inr ⟨t₁ ++ t', v, m', Steps.silent hloop (hs.trans (Steps.silent hnext hs')),
        by simpa [trace_append_assoc] using hq⟩
  · exact .inr ⟨t₁, v, m₁, Steps.silent hloop (by simpa [call_cont] using hs), hq⟩

end NautyVerified.Logic

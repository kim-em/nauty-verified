import NautyVerified.Logic.Call

/-!
# Weakest preconditions

`Wp f s Q e le m`: `s`, run in function `f` from local environment `e`,
temporaries `le` and memory `m` (and any continuation), finishes as `Q`
allows. A triple is `Wp` at every state satisfying its precondition
(`triple_iff_wp`).

The rules below are stated backwards (`wp_seq` asks for `Wp` of the first
statement with the second's `Wp` as its postcondition), so proving `Wp` of a
concrete body needs no intermediate assertions: applying the rule for each
statement and evaluating its expressions with `simp` executes the body
symbolically from the given state.
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

variable [binary64_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {ge : genv}

variable (xi ge) in
/-- The weakest precondition of `s` for `Q`, in function `f`. -/
def Wp (f : function) (s : statement) (Q : Post) : Assn := fun e le m =>
  Triple (xi := xi) (ge := ge) f (fun e' le' m' => e' = e ∧ le' = le ∧ m' = m) s Q

theorem triple_iff_wp {f : function} {P : Assn} {s : statement} {Q : Post} :
    Triple (xi := xi) (ge := ge) f P s Q ↔ ∀ e le m, P e le m → Wp xi ge f s Q e le m := by
  constructor
  · intro h e le m hp k e' le' m' ⟨he, hle, hm⟩
    subst he hle hm
    exact h k e' le' m' hp
  · intro h k e le m hp
    exact h e le m hp k e le m ⟨rfl, rfl, rfl⟩

theorem wp_of_triple {f : function} {P : Assn} {s : statement} {Q : Post}
    (h : Triple (xi := xi) (ge := ge) f P s Q) {e le m} (hp : P e le m) :
    Wp xi ge f s Q e le m :=
  triple_iff_wp.1 h e le m hp

theorem wp_conseq {f : function} {s : statement} {Q Q' : Post}
    (hn : ∀ t e le m, Q.normal t e le m → Q'.normal t e le m)
    (hb : ∀ t e le m, Q.brk t e le m → Q'.brk t e le m)
    (hc : ∀ t e le m, Q.cont t e le m → Q'.cont t e le m)
    (hr : ∀ t v m, Q.ret t v m → Q'.ret t v m) {e le m}
    (h : Wp xi ge f s Q e le m) : Wp xi ge f s Q' e le m :=
  triple_conseq (fun _ _ _ h => h) hn hb hc hr h

theorem wp_skip {f : function} {Q : Post} {e le m} (h : Q.normal E0 e le m) :
    Wp xi ge f .Sskip Q e le m := by
  intro k e' le' m' ⟨he, hle, hm⟩
  subst he hle hm
  exact .inl ⟨E0, le', m', .refl _, h⟩

theorem wp_break {f : function} {Q : Post} {e le m} (h : Q.brk E0 e le m) :
    Wp xi ge f .Sbreak Q e le m := by
  intro k e' le' m' ⟨he, hle, hm⟩
  subst he hle hm
  exact .inr (.inl ⟨E0, le', m', .refl _, h⟩)

theorem wp_continue {f : function} {Q : Post} {e le m} (h : Q.cont E0 e le m) :
    Wp xi ge f .Scontinue Q e le m := by
  intro k e' le' m' ⟨he, hle, hm⟩
  subst he hle hm
  exact .inr (.inr (.inl ⟨E0, le', m', .refl _, h⟩))

variable (xi ge) in
/-- The postcondition of the first statement of a sequence: run the second. -/
def seqPost (f : function) (s2 : statement) (Q : Post) : Post where
  normal t e le m := Wp xi ge f s2 (Q.after t) e le m
  brk := Q.brk
  cont := Q.cont
  ret := Q.ret

theorem wp_seq {f : function} {s1 s2 : statement} {Q : Post} {e le m}
    (h : Wp xi ge f s1 (seqPost xi ge f s2 Q) e le m) :
    Wp xi ge f (.Ssequence s1 s2) Q e le m := by
  refine triple_seq (R := fun t e' le' m' => Wp xi ge f s2 (Q.after t) e' le' m') h ?_
  intro t₁
  exact triple_iff_wp.2 fun _ _ _ h => h

theorem wp_set {f : function} {id : ident} {a : expr} {Q : Post} {e le m} {v : val}
    (hv : Exec.evalExpr ge e le m a = some v) (h : Q.normal E0 e (PTree.set id v le) m) :
    Wp xi ge f (.Sset id a) Q e le m :=
  triple_set fun _ _ _ ⟨he, hle, hm⟩ => by subst he hle hm; exact ⟨v, hv, h⟩

theorem wp_assign {f : function} {a1 a2 : expr} {Q : Post} {e le m}
    {loc : block} {ofs : ptrofs} {bf : bitfield} {v2 v : val} {m' : mem}
    (hl : Exec.evalLvalue ge e le m a1 = some (loc, ofs, bf))
    (hr : Exec.evalExpr ge e le m a2 = some v2)
    (hc : sem_cast v2 (typeof a2) (typeof a1) m = some v)
    (ha : Exec.assignLoc ge.genv_cenv (typeof a1) m loc ofs v bf = some m')
    (h : Q.normal E0 e le m') :
    Wp xi ge f (.Sassign a1 a2) Q e le m :=
  triple_assign fun _ _ _ ⟨he, hle, hm⟩ => by
    subst he hle hm; exact ⟨loc, ofs, bf, v2, v, m', hl, hr, hc, ha, h⟩

/-- A conditional whose test evaluates to `b`. -/
theorem wp_if {f : function} {a : expr} {s1 s2 : statement} {Q : Post} {e le m}
    {v : val} {b : Bool} (hv : Exec.evalExpr ge e le m a = some v)
    (hb : bool_val v (typeof a) m = some b)
    (h : Wp xi ge f (if b then s1 else s2) Q e le m) :
    Wp xi ge f (.Sifthenelse a s1 s2) Q e le m := by
  intro k e' le' m' ⟨he, hle, hm⟩
  subst he hle hm
  have hstep : Step xi ge (.State f (.Sifthenelse a s1 s2) k e' le' m') E0
      (.State f (if b then s1 else s2) k e' le' m') :=
    .step_ifthenelse _ _ _ _ _ _ _ _ _ _ (Exec.evalExpr_sound hv) hb
  rcases h k e' le' m' ⟨rfl, rfl, rfl⟩ with ⟨t, le₂, m₂, hs, hq⟩ | ⟨t, le₂, m₂, hs, hq⟩ |
      ⟨t, le₂, m₂, hs, hq⟩ | ⟨t, v', m₂, hs, hq⟩
  · exact .inl ⟨t, le₂, m₂, Steps.silent hstep hs, hq⟩
  · exact .inr (.inl ⟨t, le₂, m₂, Steps.silent hstep hs, hq⟩)
  · exact .inr (.inr (.inl ⟨t, le₂, m₂, Steps.silent hstep hs, hq⟩))
  · exact .inr (.inr (.inr ⟨t, v', m₂, Steps.silent hstep hs, hq⟩))

theorem wp_return_some {f : function} {a : expr} {Q : Post} {e le m} {v v' : val} {m' : mem}
    (hv : Exec.evalExpr ge e le m a = some v) (hc : sem_cast v (typeof a) f.fn_return m = some v')
    (hf : Mem.free_list m (blocks_of_env ge e) = some m') (h : Q.ret E0 v' m') :
    Wp xi ge f (.Sreturn (some a)) Q e le m :=
  triple_return_some fun _ _ _ ⟨he, hle, hm⟩ => by subst he hle hm; exact ⟨v, v', m', hv, hc, hf, h⟩

theorem wp_return_none {f : function} {Q : Post} {e le m} {m' : mem}
    (hf : Mem.free_list m (blocks_of_env ge e) = some m') (h : Q.ret E0 .Vundef m') :
    Wp xi ge f (.Sreturn none) Q e le m :=
  triple_return_none fun _ _ _ ⟨he, hle, hm⟩ => by subst he hle hm; exact ⟨m', hf, h⟩

theorem wp_call {f : function} {optid : Option ident} {a : expr} {al : List expr} {Q : Post}
    {e le m} (fd : fundef) (S : FunSpec) (hS : Satisfies xi ge fd S)
    {targs : List type} {tres : type} {cc : calling_convention} {vf : val} {vargs : List val}
    (hcl : classify_fun (typeof a) = .fun_case_f targs tres cc)
    (hvf : Exec.evalExpr ge e le m a = some vf)
    (hargs : Exec.evalExprlist ge e le m al targs = some vargs)
    (hfind : Genv.find_funct ge.genv_genv vf = some fd)
    (hty : type_of_fundef fd = .Tfunction targs tres cc)
    (hpre : S.pre vargs m)
    (h : ∀ t v m', S.post vargs m t v m' → Q.normal t e (set_opttemp optid v le) m') :
    Wp xi ge f (.Scall optid a al) Q e le m :=
  triple_call fd S hS fun _ _ _ ⟨he, hle, hm⟩ => by
    subst he hle hm; exact ⟨targs, tres, cc, vf, vargs, hcl, hvf, hargs, hfind, hty, hpre, h⟩

theorem wp_builtin {f : function} {optid : Option ident} {ef : external_function}
    {targs : List type} {al : List expr} {Q : Post} {e le m} {vargs : List val} {t : trace}
    {vres : val} {m' : mem}
    (hargs : Exec.evalExprlist ge e le m al targs = some vargs)
    (hcall : external_call xi ef (Genv.to_senv ge.genv_genv) vargs m t vres m')
    (h : Q.normal t e (set_opttemp optid vres le) m') :
    Wp xi ge f (.Sbuiltin optid ef targs al) Q e le m :=
  triple_builtin fun _ _ _ ⟨he, hle, hm⟩ => by subst he hle hm; exact ⟨vargs, t, vres, m', hargs, hcall, h⟩

/-- Loops, by an invariant `I n t` with variant `n` and trace so far `t`. -/
theorem wp_loop {f : function} {body iter : statement} {I J : Nat → trace → Assn} {Q : Post}
    (hbody : ∀ n t e le m, I n t e le m → Wp xi ge f body
      { normal := fun t' => J n (t ++ t'), cont := fun t' => J n (t ++ t'),
        brk := fun t' => Q.normal (t ++ t'), ret := fun t' => Q.ret (t ++ t') } e le m)
    (hiter : ∀ n t e le m, J n t e le m → Wp xi ge f iter
      { normal := fun t' e le m => ∃ n' < n, I n' (t ++ t') e le m,
        brk := fun t' => Q.normal (t ++ t'), ret := fun t' => Q.ret (t ++ t') } e le m)
    {n e le m} (hi : I n E0 e le m) :
    Wp xi ge f (.Sloop body iter) Q e le m :=
  wp_of_triple (triple_loop (fun n t => triple_iff_wp.2 (hbody n t))
    (fun n t => triple_iff_wp.2 (hiter n t)) n) hi

/-- A statement finishing normally leaves the local environment as it was. -/
theorem wp_env {f : function} {s : statement} {Q : Post} {e le m}
    (h : Wp xi ge f s Q e le m) :
    Wp xi ge f s { Q with normal := fun t e' le' m' => e' = e ∧ Q.normal t e' le' m' } e le m := by
  intro k e' le' m' ⟨he, hle, hm⟩
  subst he hle hm
  rcases h k e' le' m' ⟨rfl, rfl, rfl⟩ with ⟨t, le₂, m₂, hs, hq⟩ | hb | hc | hr
  · exact .inl ⟨t, le₂, m₂, hs, rfl, hq⟩
  · exact .inr (.inl hb)
  · exact .inr (.inr (.inl hc))
  · exact .inr (.inr (.inr hr))

/-! ## Computational forms

The same rules with the evaluation in the premise, as a `match` on the
evaluator's result: after `simp` computes the evaluation, the premise is the
weakest precondition of what follows. -/

theorem wp_set_eval {f : function} {id : ident} {a : expr} {Q : Post} {e le m}
    (h : match Exec.evalExpr ge e le m a with
      | some v => Q.normal E0 e (PTree.set id v le) m
      | none => False) :
    Wp xi ge f (.Sset id a) Q e le m := by
  split at h
  · exact wp_set ‹_› h
  · exact h.elim

theorem wp_if_eval {f : function} {a : expr} {s1 s2 : statement} {Q : Post} {e le m}
    (h : match Exec.evalExpr ge e le m a with
      | some v =>
          match bool_val v (typeof a) m with
          | some b => Wp xi ge f (if b then s1 else s2) Q e le m
          | none => False
      | none => False) :
    Wp xi ge f (.Sifthenelse a s1 s2) Q e le m := by
  split at h
  · split at h
    · exact wp_if ‹_› ‹_› h
    · exact h.elim
  · exact h.elim

theorem wp_return_some_eval {f : function} {a : expr} {Q : Post} {e le m}
    (h : match Exec.evalExpr ge e le m a with
      | some v =>
          match sem_cast v (typeof a) f.fn_return m with
          | some v' =>
              match Mem.free_list m (blocks_of_env ge e) with
              | some m' => Q.ret E0 v' m'
              | none => False
          | none => False
      | none => False) :
    Wp xi ge f (.Sreturn (some a)) Q e le m := by
  split at h
  · split at h
    · split at h
      · exact wp_return_some ‹_› ‹_› ‹_› h
      · exact h.elim
    · exact h.elim
  · exact h.elim

theorem wp_assign_eval {f : function} {a1 a2 : expr} {Q : Post} {e le m}
    (h : match Exec.evalLvalue ge e le m a1, Exec.evalExpr ge e le m a2 with
      | some (loc, ofs, bf), some v2 =>
          match sem_cast v2 (typeof a2) (typeof a1) m with
          | some v =>
              match Exec.assignLoc ge.genv_cenv (typeof a1) m loc ofs v bf with
              | some m' => Q.normal E0 e le m'
              | none => False
          | none => False
      | _, _ => False) :
    Wp xi ge f (.Sassign a1 a2) Q e le m := by
  split at h
  · split at h
    · split at h
      · exact wp_assign ‹_› ‹_› ‹_› ‹_› h
      · exact h.elim
    · exact h.elim
  · exact h.elim

end NautyVerified.Logic

namespace NautyVerified.Logic

/-- Apply the weakest-precondition rule for the head statement and normalise
the postconditions it introduces. Conditionals are evaluated but not split. -/
macro "wp_step" : tactic => `(tactic| first
  | (apply wp_seq; try simp only [seqPost, Post.after])
  | (apply wp_skip; try simp only [seqPost, Post.after, E0_append, append_E0])
  | (apply wp_set_eval; try simp only [Exec.evalExpr])
  | (apply wp_if_eval; try simp only [Exec.evalExpr])
  | (apply wp_return_some_eval; try simp only [Exec.evalExpr])
  | (apply wp_assign_eval; try simp only [Exec.evalExpr, Exec.evalLvalue]))

end NautyVerified.Logic

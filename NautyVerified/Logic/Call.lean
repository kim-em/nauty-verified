import NautyVerified.Logic.Triple

/-!
# Function specifications and calls

A `FunSpec` relates a call's arguments and memory to its trace, result and
final memory. `Satisfies fd S`: every call of `fd` satisfying the precondition
returns, as `S.post` describes. The call rule (`triple_call`) uses a callee's
`Satisfies`; `satisfies_internal` proves `Satisfies` for a function from a
triple about its body, and `satisfies_external` for an external function from
its semantics.

Recursive functions are proved by induction on a measure in the precondition,
using `Satisfies` of smaller instances inside the body's proof.
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

/-- A function specification. -/
structure FunSpec where
  pre : List val → mem → Prop
  post : List val → mem → trace → val → mem → Prop

variable (xi ge) in
/-- Every call of `fd` that satisfies `S.pre` returns as `S.post` says. -/
def Satisfies (fd : fundef) (S : FunSpec) : Prop :=
  ∀ args m, S.pre args m → ∀ k, is_call_cont k →
    ∃ t v m', Steps xi ge (.Callstate fd args k m) t (.Returnstate v k m') ∧ S.post args m t v m'

theorem Satisfies.mono {fd : fundef} {S S' : FunSpec}
    (hpre : ∀ args m, S'.pre args m → S.pre args m)
    (hpost : ∀ args m t v m', S'.pre args m → S.post args m t v m' → S'.post args m t v m')
    (h : Satisfies xi ge fd S) : Satisfies xi ge fd S' := by
  intro args m hp k hk
  obtain ⟨t, v, m', hs, hq⟩ := h args m (hpre _ _ hp) k hk
  exact ⟨t, v, m', hs, hpost _ _ _ _ _ hp hq⟩

/-- A call `optid = a(al)` to a function satisfying `S`. -/
theorem triple_call {f : function} {P : Assn} {optid : Option ident} {a : expr}
    {al : List expr} {Q : Post} (fd : fundef) (S : FunSpec) (hS : Satisfies xi ge fd S)
    (h : ∀ e le m, P e le m → ∃ targs tres cc vf vargs,
      classify_fun (typeof a) = .fun_case_f targs tres cc ∧
      Exec.evalExpr ge e le m a = some vf ∧
      Exec.evalExprlist ge e le m al targs = some vargs ∧
      Genv.find_funct ge.genv_genv vf = some fd ∧
      type_of_fundef fd = .Tfunction targs tres cc ∧
      S.pre vargs m ∧
      ∀ t v m', S.post vargs m t v m' → Q.normal t e (set_opttemp optid v le) m') :
    Triple (xi := xi) (ge := ge) f P (.Scall optid a al) Q := by
  intro k e le m hp
  obtain ⟨targs, tres, cc, vf, vargs, hcl, hvf, hargs, hfind, hty, hpre, hpost⟩ := h e le m hp
  have hcall : Step xi ge (.State f (.Scall optid a al) k e le m) E0
      (.Callstate fd vargs (.Kcall optid f e le k) m) :=
    .step_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcl (Exec.evalExpr_sound hvf)
      (Exec.evalExprlist_sound hargs) hfind hty
  obtain ⟨t, v, m', hs, hq⟩ := hS vargs m hpre (.Kcall optid f e le k) trivial
  have hret : Step xi ge (.Returnstate v (.Kcall optid f e le k) m') E0
      (.State f .Sskip k e (set_opttemp optid v le) m') := .step_returnstate _ _ _ _ _ _ _
  exact .inl ⟨t, _, m', Steps.silent hcall (by simpa using hs.trans (Steps.one hret)),
    hpost t v m' hq⟩

/-- A builtin or inlined external call `optid = ef(al)`. -/
theorem triple_builtin {f : function} {P : Assn} {optid : Option ident}
    {ef : external_function} {targs : List type} {al : List expr} {Q : Post}
    (h : ∀ e le m, P e le m → ∃ vargs t vres m',
      Exec.evalExprlist ge e le m al targs = some vargs ∧
      external_call xi ef (Genv.to_senv ge.genv_genv) vargs m t vres m' ∧
      Q.normal t e (set_opttemp optid vres le) m') :
    Triple (xi := xi) (ge := ge) f P (.Sbuiltin optid ef targs al) Q := by
  intro k e le m hp
  obtain ⟨vargs, t, vres, m', hargs, hcall, hq⟩ := h e le m hp
  exact .inl ⟨t, _, m', by
    simpa using Steps.one (.step_builtin _ _ _ _ _ _ _ _ _ _ _ _ _
      (Exec.evalExprlist_sound hargs) hcall), hq⟩

/-- An external function satisfies any specification its semantics implies. -/
theorem satisfies_external {ef : external_function} {targs : List type} {tres : type}
    {cc : calling_convention} {S : FunSpec}
    (h : ∀ args m, S.pre args m → ∃ t v m',
      external_call xi ef (Genv.to_senv ge.genv_genv) args m t v m' ∧ S.post args m t v m') :
    Satisfies xi ge (.External ef targs tres cc) S := by
  intro args m hp k _
  obtain ⟨t, v, m', hcall, hq⟩ := h args m hp
  exact ⟨t, v, m', by
    simpa using Steps.one (.step_external_function _ _ _ _ _ _ _ _ _ _ hcall), hq⟩

/-- An internal function satisfies `S` if, after entry, its body ends in a
`return` (or falls off its end) as `S.post` says. `Entry args m₀` describes the
state just after entry. -/
theorem satisfies_internal {f : function} {S : FunSpec} {Entry : List val → mem → Assn}
    (hentry : ∀ args m, S.pre args m → ∃ e le m₁,
      function_entry2 ge f args m e le m₁ ∧ Entry args m e le m₁)
    (hbody : ∀ args m₀, S.pre args m₀ → Triple (xi := xi) (ge := ge) f (Entry args m₀) f.fn_body
      { normal := fun t e _ m => ∃ m', Mem.free_list m (blocks_of_env ge e) = some m' ∧
          S.post args m₀ t .Vundef m',
        ret := fun t v m' => S.post args m₀ t v m' }) :
    Satisfies xi ge (.Internal f) S := by
  intro args m hp k hk
  obtain ⟨e, le, m₁, hfe, hen⟩ := hentry args m hp
  have hin : Step xi ge (.Callstate (.Internal f) args k m) E0 (.State f f.fn_body k e le m₁) :=
    .step_internal_function _ _ _ _ _ _ _ hfe
  have hcc : call_cont k = k := by
    cases k <;> simp_all [is_call_cont, call_cont]
  rcases hbody args m hp k e le m₁ hen with ⟨t, le', m', hs, m'', hfree, hq⟩ |
      ⟨t, le', m', hs, hq⟩ | ⟨t, le', m', hs, hq⟩ | ⟨t, v, m', hs, hq⟩
  · have hend : Step xi ge (.State f .Sskip k e le' m') E0 (.Returnstate .Vundef k m'') :=
      .step_skip_call _ _ _ _ _ _ hk hfree
    exact ⟨t, .Vundef, m'', Steps.silent hin (by simpa using hs.trans (Steps.one hend)), hq⟩
  · exact absurd hq id
  · exact absurd hq id
  · rw [hcc] at hs
    exact ⟨t, v, m', Steps.silent hin hs, hq⟩

end NautyVerified.Logic

import NautyVerified.Statement.Compose
import NautyVerified.Proofs.Top.Nauty

/-!
# The end-to-end theorem for dense nauty, from `main_ok`

`densenauty_binary_correct_of` proves `densenauty_binary_correct`'s statement
(`Statement/Final.lean`).

- `init_mem_some`: the linked program has an initial memory. CompCert's
  `init_mem_exists` asks for every global's initialiser to be aligned and to
  take addresses of known symbols only; `initOk` checks both and the kernel
  evaluates it on the program (`initOk_prog`).
- `exec_of_main`: a specification `main` satisfies from the initial memory
  gives an execution of the program from its initial state to a return from
  `main`, whose trace, result and final memory satisfy the postcondition.
- `densenauty_binary_correct_of`: `main_ok`'s `mainSpec` gives the execution
  `binary_of_execution` needs.
-/

namespace NautyVerified.Statement

open CompCert4Lean CompCert4Lean.Common.Events CompCert4Lean.Common.Behaviors
open CompCert4Lean.Common.Smallstep CompCert4Lean.Common.Values CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Proofs
open Hex.GraphIso Hex.GraphIso.Nauty

/-! ## The initial memory exists -/

/-- `init_data_list_aligned p l`, decided. -/
def alignedB : Z → List init_data → Bool
  | _, [] => true
  | p, i :: rest => decide (intOfZ (Genv.init_data_alignment i) ∣ intOfZ p) &&
      alignedB (ZArith.BinInt.Z.add p (init_data_size i)) rest

theorem aligned_of : ∀ (p : Z) (l : List init_data), alignedB p l = true →
    Genv.init_data_list_aligned p l
  | _, [], _ => trivial
  | p, i :: rest, h => by
    simp only [alignedB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨c, hc⟩, h2⟩ := h
    refine ⟨⟨zOfInt c, ?_⟩, aligned_of _ rest h2⟩
    apply intOfZ_injective
    show intOfZ p = intOfZ (zOfInt (intOfZ (Genv.init_data_alignment i) * intOfZ (zOfInt c)))
    rw [intOfZ_zOfInt, intOfZ_zOfInt, hc]

/-- Every `Init_addrof` in `l` names a symbol of `ge`. -/
def addrsB {F V : Type} (ge : Genv.t F V) (l : List init_data) : Bool :=
  l.all fun d => match d with
    | .Init_addrof i _ => (Genv.find_symbol ge i).isSome
    | _ => true

theorem addrs_of {F V : Type} {ge : Genv.t F V} {l : List init_data} (h : addrsB ge l = true) :
    ∀ i o, Init_addrof i o ∈ l → ∃ b, Genv.find_symbol ge i = some b := by
  intro i o hm
  have := List.all_eq_true.1 h _ hm
  simp only at this
  exact Option.isSome_iff_exists.1 this

/-- The hypothesis of `init_mem_exists`, decided. -/
def initOk {F V : Type} (p : program F V) : Bool :=
  p.prog_defs.all fun d => match d.2 with
    | .Gvar v => alignedB ZArith.BinInt.Z.Z0 v.gvar_init && addrsB (Genv.globalenv p) v.gvar_init
    | .Gfun _ => true

theorem init_mem_of {F V : Type} {p : program F V} (h : initOk p = true) :
    ∃ m, Genv.init_mem p = some m := by
  refine Genv.init_mem_exists F V p fun id v hm => ?_
  have := List.all_eq_true.1 h _ hm
  simp only [Bool.and_eq_true] at this
  exact ⟨aligned_of _ _ this.1, addrs_of this.2⟩

kernel_rfl initOk_prog : initOk Init.prog = true

/-- The linked program has an initial memory. -/
theorem init_mem_some : ∃ m, Genv.init_mem Init.prog = some m := init_mem_of initOk_prog

/-! ## An execution from a specification of `main` -/

kernel_rfl prog_main_eq : Source.dense.locals.prog_main = Source.dense.id.main

theorem type_main :
    type_of_fundef (.Internal Source.dense.fn.main : fundef) =
      .Tfunction [] Cfrontend.Ctypes.type_int32s cc_default := rfl

theorem star_of_steps {s s' : state} {t : trace} (h : Steps xi Program.ge s t s') : LStar s t s' := by
  induction h with
  | refl s => exact .star_refl s
  | step hs _ ih => exact .star_step _ _ _ _ _ _ hs ih rfl

/-- The initial state of the linked program: a call of `main` in the initial memory. -/
theorem initial_main {m₀ : mem} (hm : Genv.init_mem Init.prog = some m₀) :
    L.initial_state (.Callstate (.Internal Source.dense.fn.main) [] .Kstop m₀) := by
  refine .intro Harness.Block.main _ m₀ hm ?_ ?_ type_main
  · rw [prog_main_eq, ← Init.ge_eq]; exact Harness.find_main
  · rw [← Init.ge_eq]; exact Harness.funct_main

/-- A specification that `main` satisfies from the initial memory describes an
execution of the program from its initial state to `main`'s return. -/
theorem exec_of_main {S : FunSpec}
    (h : Satisfies xi Program.ge (.Internal Source.dense.fn.main) S)
    (hpre : ∀ m, Genv.init_mem Init.prog = some m → S.pre [] m) :
    ∃ m₀ t v m', L.initial_state (.Callstate (.Internal Source.dense.fn.main) [] .Kstop m₀) ∧
      LStar (.Callstate (.Internal Source.dense.fn.main) [] .Kstop m₀) t (.Returnstate v .Kstop m') ∧
      S.post [] m₀ t v m' := by
  obtain ⟨m₀, hm⟩ := init_mem_some
  obtain ⟨t, v, m', hs, hq⟩ := h [] m₀ (hpre m₀ hm) .Kstop trivial
  exact ⟨m₀, t, v, m', initial_main hm, star_of_steps hs, hq⟩

/-! ## The end-to-end theorem -/

/-- `densenauty_binary_correct`. -/
theorem densenauty_binary_correct_of {n k : Nat} (G : Colored n k) (hn : 0 < n) (hmax : n ≤ maxN)
    (hk : k ≤ maxN) {ins : List Int} (hins : Encodes G ins) {tp : X86.Asm.program} (hc : Compiled tp) :
    ∀ beh, program_behaves (X86.Asm.semantics Build.config xi tp) beh → Consistent ins beh →
      ∃ t, beh = .Terminates t (Lib.Integers.Int.repr .Z0) ∧ writes t = expected G := by
  refine binary_of_execution G hc ?_
  obtain ⟨m₀, t, v, m', hinit, hstar, hv, hr, hw, hz⟩ :=
    exec_of_main (Top.main_ok G ins hins hn hmax hk) fun _ hm => ⟨rfl, hm⟩
  subst hv
  exact ⟨_, _, t, hinit, hstar, .intro _ m', hr, hz, hw⟩

end NautyVerified.Statement

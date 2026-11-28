import NautyVerified.Proofs.Harness.Spec

/-!
# `nv_read` and `nv_write`

`readSpec x`: `nv_read()` can return the `long` `x`, recording the read event.
`writeSpec x`: `nv_write(x)` records the write event. `Reads t l` is the read
analogue of `Search.Writes`, and `reads_eq`/`writes_eq` compute the
statement's `reads`/`writes` of such traces.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (Writes)

kernel_rfl funct_nvRead : Genv.find_funct_ptr ge.genv_genv Block.nvRead =
  some (.External (.EF_external Statement.nameRead Statement.sigRead) [] tlong cc_default)
kernel_rfl funct_nvWrite : Genv.find_funct_ptr ge.genv_genv Block.nvWrite =
  some (.External (.EF_external Statement.nameWrite Statement.sigWrite) [tlong] .Tvoid cc_default)

/-- The read event returning `x`. -/
abbrev readEv (x : Lib.Integers.int64) : event := .Event_syscall Statement.nameRead [] (.EVlong x)

/-- `Int64.signed (lr a) = a` in range. -/
theorem signed_lr {a : Int} (h1 : -2 ^ 63 ≤ a) (h2 : a < 2 ^ 63) :
    intOfZ (Lib.Integers.Int64.signed (lr a)) = a := by
  rw [intOfZ_Int64_signed, bv64_repr, intOfZ_zOfInt, BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le <;> omega

/-- A one-event trace. -/
def tr1 (ev : event) : trace := [ev]

/-- `t` is `nv_read` events returning `l`. -/
inductive Reads : trace → List Int → Prop
  | nil : Reads [] []
  | cons (x : Lib.Integers.int64) {t : trace} {l : List Int} :
      Reads t l → Reads (readEv x :: t) (intOfZ (Lib.Integers.Int64.signed x) :: l)

theorem Reads.append {t₁ t₂ : trace} {l₁ l₂ : List Int} (h₁ : Reads t₁ l₁) (h₂ : Reads t₂ l₂) :
    Reads (t₁ ++ t₂) (l₁ ++ l₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons x _ ih => exact .cons x ih

theorem Reads.one (x : Lib.Integers.int64) :
    Reads (tr1 (readEv x)) [intOfZ (Lib.Integers.Int64.signed x)] := .cons x .nil

theorem nameRead_ne_nameWrite : Statement.nameRead ≠ Statement.nameWrite := by decide +kernel

theorem reads_read (x : Lib.Integers.int64) (u : trace) :
    Statement.reads (readEv x :: u) = some (intOfZ (Lib.Integers.Int64.signed x)) :: Statement.reads u := by
  show (if Statement.nameRead = Statement.nameRead then
    some (intOfZ (Lib.Integers.Int64.signed x)) :: Statement.reads u else Statement.reads u) = _
  rw [ite_eq_left rfl]

theorem writes_read (x : Lib.Integers.int64) (u : trace) :
    Statement.writes (readEv x :: u) = Statement.writes u := rfl

theorem reads_write (x : Lib.Integers.int64) (r : eventval) (u : trace) :
    Statement.reads (.Event_syscall Statement.nameWrite [.EVlong x] r :: u) = Statement.reads u := rfl

theorem writes_write (x : Lib.Integers.int64) (r : eventval) (u : trace) :
    Statement.writes (.Event_syscall Statement.nameWrite [.EVlong x] r :: u) =
      intOfZ (Lib.Integers.Int64.signed x) :: Statement.writes u := by
  show (if Statement.nameWrite = Statement.nameWrite then
    intOfZ (Lib.Integers.Int64.signed x) :: Statement.writes u else Statement.writes u) = _
  rw [ite_eq_left rfl]

theorem Reads.reads {t : trace} {l : List Int} (h : Reads t l) (s : trace) :
    Statement.reads (t ++ s) = l.map some ++ Statement.reads s := by
  induction h with
  | nil => rfl
  | @cons x t' l' _ ih =>
    show Statement.reads (readEv x :: (t' ++ s)) = _
    rw [reads_read, ih]; rfl

theorem Reads.writes {t : trace} {l : List Int} (h : Reads t l) (s : trace) :
    Statement.writes (t ++ s) = Statement.writes s := by
  induction h with
  | nil => rfl
  | @cons x t' l' _ ih =>
    show Statement.writes (readEv x :: (t' ++ s)) = _
    rw [writes_read]; exact ih

theorem Writes.reads {t : trace} {l : List Int} (h : Writes t l) (s : trace) :
    Statement.reads (t ++ s) = Statement.reads s := by
  induction h with
  | nil => rfl
  | @cons x r t' l' _ ih =>
    show Statement.reads (.Event_syscall Statement.nameWrite [.EVlong x] (.EVint r) :: (t' ++ s)) = _
    rw [reads_write]; exact ih

theorem Writes.writes {t : trace} {l : List Int} (h : Writes t l) (s : trace) :
    Statement.writes (t ++ s) = l ++ Statement.writes s := by
  induction h with
  | nil => rfl
  | @cons x r t' l' _ ih =>
    show Statement.writes (.Event_syscall Statement.nameWrite [.EVlong x] (.EVint r) :: (t' ++ s)) = _
    rw [writes_write, ih]; rfl

/-- `nv_read()` returning `x`. -/
def readSpec (x : Lib.Integers.int64) : FunSpec where
  pre args _ := args = []
  post _ m t v m' := t = tr1 (readEv x) ∧ v = .Vlong x ∧ m' = m

/-- `nv_write(x)`. -/
def writeSpec (x : Lib.Integers.int64) : FunSpec where
  pre args _ := args = [.Vlong x]
  post _ m t _ m' := Writes t [intOfZ (Lib.Integers.Int64.signed x)] ∧ m' = m

theorem read_satisfies (x : Lib.Integers.int64) :
    Satisfies Statement.xi ge
      (.External (.EF_external Statement.nameRead Statement.sigRead) [] tlong cc_default)
      (readSpec x) :=
  satisfies_external fun args m hargs => by
    subst hargs
    refine ⟨tr1 (readEv x), .Vlong x, m, ?_, rfl, rfl, rfl⟩
    show Statement.extSem _ _ _ _ _ _ _ _
    simp only [Statement.extSem, and_self, ite_true]
    exact .intro _ m (.EVlong x) (.Vlong x) (.ev_match_long x)

theorem write_satisfies {ge : genv} (x : Lib.Integers.int64) :
    Satisfies Statement.xi ge
      (.External (.EF_external Statement.nameWrite Statement.sigWrite) [tlong] .Tvoid cc_default)
      (writeSpec x) :=
  satisfies_external fun args m hargs => by
    subst hargs
    refine ⟨_, .Vundef, m, ?_, .cons x Lib.Integers.Int.zero .nil, rfl⟩
    show Statement.extSem _ _ _ _ _ _ _ _
    simp only [Statement.extSem, and_self, ite_true]
    rw [ite_eq_right (by intro h; exact nameRead_ne_nameWrite h.1.symm)]
    exact .intro _ m x _

end NautyVerified.Proofs.Harness

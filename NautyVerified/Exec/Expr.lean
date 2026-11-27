import CompCert4Lean.Cfrontend.Clight

/-!
# Executable evaluation of Clight expressions

CompCert4Lean's Clight evaluates expressions by the relations `eval_expr` and
`eval_lvalue`. Clight expressions are deterministic and free of side effects,
so they are also computed by plain structural recursion: `evalExpr` and
`evalLvalue` below, with soundness theorems (`evalExpr_sound`,
`evalLvalue_sound`) saying that whatever they compute the relations allow.

These functions are what the program logic and the interpreter use: on a
concrete Clight expression `simp` unfolds them to the memory operations the
expression performs.

Bit-field accesses are not implemented (the functions return `none`); nauty
uses none.
-/

namespace NautyVerified.Exec

open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Cfrontend.Ctypes CompCert4Lean.Cfrontend.Cop CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open CompCert4Lean.Flocq.IEEE754.Binary (BinaryNormalizeCertificate)

/-- Executable `deref_loc`, for whole (non-bit-field) locations. -/
def derefLoc (ty : type) (m : mem) (b : block) (ofs : ptrofs) : bitfield → Option val
  | .Full =>
      match access_mode ty with
      | .By_value chunk => Mem.loadv chunk m (.Vptr b ofs)
      | .By_reference => some (.Vptr b ofs)
      | .By_copy => some (.Vptr b ofs)
      | .By_nothing => none
  | .Bits .. => none

/-- `a` divides `b`, checked with the witness `b / a`. -/
def dividesBy (a b : Z) : Prop := b = ZArith.BinInt.Z.mul a (ZArith.BinInt.Z.div b a)

instance (a b : Z) : Decidable (dividesBy a b) := inferInstanceAs (Decidable (_ = _))

theorem divide_of_dividesBy {a b : Z} (h : dividesBy a b) : ZArith.BinInt.Z.divide a b :=
  ⟨_, h⟩

/-- The side conditions of `assign_loc_copy`, in decidable form. -/
def copyOk (ce : composite_env) (ty : type) (b : block) (ofs : ptrofs) (b' : block)
    (ofs' : ptrofs) : Prop :=
  dividesBy (alignof_blockcopy ce ty) (Ptrofs.unsigned ofs') ∧
  dividesBy (alignof_blockcopy ce ty) (Ptrofs.unsigned ofs) ∧
  (b' ≠ b ∨ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs ∨
    ZArith.BinInt.Z.le (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs') (sizeof ce ty))
      (Ptrofs.unsigned ofs) ∨
    ZArith.BinInt.Z.le (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) (sizeof ce ty))
      (Ptrofs.unsigned ofs'))

instance (a b : Z) : Decidable (ZArith.BinInt.Z.le a b) :=
  inferInstanceAs (Decidable (intOfZ a ≤ intOfZ b))

instance (ce : composite_env) (ty : type) (b : block) (ofs : ptrofs) (b' : block)
    (ofs' : ptrofs) : Decidable (copyOk ce ty b ofs b' ofs') := by
  unfold copyOk; infer_instance

/-- Executable `assign_loc`, for whole locations: scalar stores and structure copies. -/
def assignLoc (ce : composite_env) (ty : type) (m : mem) (b : block) (ofs : ptrofs) (v : val) :
    bitfield → Option mem
  | .Full =>
      match access_mode ty with
      | .By_value chunk => Mem.storev chunk m (.Vptr b ofs) v
      | .By_copy =>
          match v with
          | .Vptr b' ofs' =>
              if copyOk ce ty b ofs b' ofs' then
                match Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) with
                | some bytes => Mem.storebytes m b (Ptrofs.unsigned ofs) bytes
                | none => none
              else none
          | _ => none
      | _ => none
  | .Bits .. => none

variable [binary64_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

/-- The location of a variable: local if bound with this type, otherwise a global. -/
def lvalOfVar (ge : genv) (e : env) (id : ident) (ty : type) :
    Option (block × ptrofs × bitfield) :=
  match PTree.get id e with
  | some (l, ty') => if ty' = ty then some (l, Ptrofs.zero, .Full) else none
  | none =>
      match Genv.find_symbol ge.genv_genv id with
      | some l => some (l, Ptrofs.zero, .Full)
      | none => none

/-- The location of member `i` of the struct or union at `v` of type `ta`. -/
def lvalOfField (ge : genv) (ta : type) (i : ident) (v : val) :
    Option (block × ptrofs × bitfield) :=
  match v with
  | .Vptr l ofs =>
      match ta with
      | .Tstruct id _ =>
          match PTree.get id ge.genv_cenv with
          | some co =>
              match field_offset ge.genv_cenv i co.co_members with
              | .OK (delta, bf) => some (l, Ptrofs.add ofs (Ptrofs.repr delta), bf)
              | .Error _ => none
          | none => none
      | .Tunion id _ =>
          match PTree.get id ge.genv_cenv with
          | some co =>
              match union_field_offset ge.genv_cenv i co.co_members with
              | .OK (delta, bf) => some (l, Ptrofs.add ofs (Ptrofs.repr delta), bf)
              | .Error _ => none
          | none => none
      | _ => none
  | _ => none

mutual
  /-- Executable `eval_expr`. -/
  def evalExpr (ge : genv) (e : env) (le : temp_env) (m : mem) : expr → Option val
    | .Econst_int i _ => some (.Vint i)
    | .Econst_float f _ => some (.Vfloat f)
    | .Econst_single f _ => some (.Vsingle f)
    | .Econst_long i _ => some (.Vlong i)
    | .Etempvar id _ => PTree.get id le
    | .Esizeof ty1 _ => some (Vptrofs (Ptrofs.repr (sizeof ge.genv_cenv ty1)))
    | .Ealignof ty1 _ => some (Vptrofs (Ptrofs.repr (alignof ge.genv_cenv ty1)))
    | .Eaddrof a _ =>
        match evalLvalue ge e le m a with
        | some (loc, ofs, .Full) => some (.Vptr loc ofs)
        | _ => none
    | .Eunop op a _ =>
        match evalExpr ge e le m a with
        | some v1 => sem_unary_operation op v1 (typeof a) m
        | none => none
    | .Ebinop op a1 a2 _ =>
        match evalExpr ge e le m a1, evalExpr ge e le m a2 with
        | some v1, some v2 => sem_binary_operation ge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m
        | _, _ => none
    | .Ecast a ty =>
        match evalExpr ge e le m a with
        | some v1 => sem_cast v1 (typeof a) ty m
        | none => none
    | .Evar id ty =>
        match lvalOfVar ge e id ty with
        | some (loc, ofs, bf) => derefLoc ty m loc ofs bf
        | none => none
    | .Ederef a ty =>
        match evalExpr ge e le m a with
        | some (.Vptr l ofs) => derefLoc ty m l ofs .Full
        | _ => none
    | .Efield a i ty =>
        match evalExpr ge e le m a with
        | some v =>
            match lvalOfField ge (typeof a) i v with
            | some (loc, ofs, bf) => derefLoc ty m loc ofs bf
            | none => none
        | none => none

  /-- Executable `eval_lvalue`. -/
  def evalLvalue (ge : genv) (e : env) (le : temp_env) (m : mem) :
      expr → Option (block × ptrofs × bitfield)
    | .Evar id ty => lvalOfVar ge e id ty
    | .Ederef a _ =>
        match evalExpr ge e le m a with
        | some (.Vptr l ofs) => some (l, ofs, .Full)
        | _ => none
    | .Efield a i _ =>
        match evalExpr ge e le m a with
        | some v => lvalOfField ge (typeof a) i v
        | none => none
    | _ => none
end

/-- Executable `eval_exprlist`: evaluate and cast each argument. -/
def evalExprlist (ge : genv) (e : env) (le : temp_env) (m : mem) :
    List expr → List type → Option (List val)
  | [], [] => some []
  | a :: as, ty :: tys =>
      match evalExpr ge e le m a with
      | some v1 =>
          match sem_cast v1 (typeof a) ty m with
          | some v2 =>
              match evalExprlist ge e le m as tys with
              | some vs => some (v2 :: vs)
              | none => none
          | none => none
      | none => none
  | _, _ => none

/-! ## Soundness -/

omit binary64_certificate binary32_certificate in
theorem derefLoc_sound {ty : type} {m : mem} {b : block} {ofs : ptrofs} {bf : bitfield}
    {v : val} (h : derefLoc ty m b ofs bf = some v) : deref_loc ty m b ofs bf v := by
  cases bf with
  | Full =>
    simp only [derefLoc] at h
    split at h
    · exact .deref_loc_value _ _ ‹_› h
    · cases h; exact .deref_loc_reference ‹_›
    · cases h; exact .deref_loc_copy ‹_›
    · cases h
  | Bits => simp [derefLoc] at h

omit binary64_certificate binary32_certificate in
theorem assignLoc_sound {ce : composite_env} {ty : type} {m : mem} {b : block} {ofs : ptrofs}
    {bf : bitfield} {v : val} {m' : mem} (h : assignLoc ce ty m b ofs v bf = some m') :
    assign_loc ce ty m b ofs bf v m' := by
  cases bf with
  | Full =>
    simp only [assignLoc] at h
    split at h
    · exact .assign_loc_value _ _ _ ‹_› h
    · rename_i hmode
      split at h
      · rename_i b' ofs'
        split at h
        · rename_i hok
          obtain ⟨h1, h2, h3⟩ := hok
          split at h
          · rename_i bytes hload
            exact .assign_loc_copy _ _ _ _ hmode (fun _ => divide_of_dividesBy h1)
              (fun _ => divide_of_dividesBy h2) h3 hload h
          · cases h
        · cases h
      · cases h
    · cases h
  | Bits => simp [assignLoc] at h

theorem lvalOfVar_sound {ge : genv} {e : env} {le : temp_env} {m : mem} {id : ident}
    {ty : type} {loc : block} {ofs : ptrofs} {bf : bitfield}
    (h : lvalOfVar ge e id ty = some (loc, ofs, bf)) :
    eval_lvalue ge e le m (.Evar id ty) loc ofs bf := by
  unfold lvalOfVar at h
  split at h
  · rename_i l ty' hget
    split at h
    · cases h
      subst_vars
      exact .eval_Evar_local _ _ _ hget
    · cases h
  · rename_i hnone
    split at h
    · cases h
      exact .eval_Evar_global _ _ _ hnone ‹_›
    · cases h

theorem lvalOfField_sound {ge : genv} {e : env} {le : temp_env} {m : mem} {a : expr}
    {i : ident} {ty : type} {v : val} {loc : block} {ofs : ptrofs} {bf : bitfield}
    (ha : eval_expr ge e le m a v) (h : lvalOfField ge (typeof a) i v = some (loc, ofs, bf)) :
    eval_lvalue ge e le m (.Efield a i ty) loc ofs bf := by
  unfold lvalOfField at h
  split at h
  · rename_i l o
    split at h
    · rename_i sid att hty
      split at h
      · rename_i co hco
        split at h
        · rename_i delta bf' hoff
          cases h
          exact .eval_Efield_struct _ _ _ _ _ _ _ _ _ _ ha hty hco hoff
        · cases h
      · cases h
    · rename_i uid att hty
      split at h
      · rename_i co hco
        split at h
        · rename_i delta bf' hoff
          cases h
          exact .eval_Efield_union _ _ _ _ _ _ _ _ _ _ ha hty hco hoff
        · cases h
      · cases h
    · cases h
  · cases h

mutual
  theorem evalExpr_sound {ge : genv} {e : env} {le : temp_env} {m : mem} :
      ∀ {a : expr} {v : val}, evalExpr ge e le m a = some v → eval_expr ge e le m a v
    | .Econst_int i ty, v, h => by cases h; exact .const_int i ty
    | .Econst_float f ty, v, h => by cases h; exact .const_float f ty
    | .Econst_single f ty, v, h => by cases h; exact .const_single f ty
    | .Econst_long i ty, v, h => by cases h; exact .const_long i ty
    | .Etempvar id ty, v, h => .eval_Etempvar id ty v h
    | .Esizeof ty1 ty, v, h => by cases h; exact .sizeof_type ty1 ty
    | .Ealignof ty1 ty, v, h => by cases h; exact .alignof_type ty1 ty
    | .Eaddrof a ty, v, h => by
        simp only [evalExpr] at h
        split at h
        · rename_i loc ofs hl
          cases h
          exact .eval_Eaddrof a ty loc ofs (evalLvalue_sound hl)
        · cases h
    | .Eunop op a ty, v, h => by
        simp only [evalExpr] at h
        split at h
        · rename_i v1 ha
          exact .unary op a ty v1 v (evalExpr_sound ha) h
        · cases h
    | .Ebinop op a1 a2 ty, v, h => by
        simp only [evalExpr] at h
        split at h
        · rename_i v1 v2 h1 h2
          exact .binary op a1 a2 ty v1 v2 v (evalExpr_sound h1) (evalExpr_sound h2) h
        · cases h
    | .Ecast a ty, v, h => by
        simp only [evalExpr] at h
        split at h
        · rename_i v1 ha
          exact .cast a ty v1 v (evalExpr_sound ha) h
        · cases h
    | .Evar id ty, v, h => by
        simp only [evalExpr] at h
        split at h
        · rename_i loc ofs bf hl
          exact .eval_Elvalue _ loc ofs bf v (lvalOfVar_sound hl) (derefLoc_sound h)
        · cases h
    | .Ederef a ty, v, h => by
        simp only [evalExpr] at h
        split at h
        · rename_i l ofs ha
          exact .eval_Elvalue _ l ofs .Full v (.eval_Ederef a ty l ofs (evalExpr_sound ha))
            (derefLoc_sound h)
        · cases h
    | .Efield a i ty, v, h => by
        simp only [evalExpr] at h
        split at h
        · rename_i va ha
          split at h
          · rename_i loc ofs bf hl
            exact .eval_Elvalue _ loc ofs bf v (lvalOfField_sound (evalExpr_sound ha) hl)
              (derefLoc_sound h)
          · cases h
        · cases h

  theorem evalLvalue_sound {ge : genv} {e : env} {le : temp_env} {m : mem} :
      ∀ {a : expr} {loc : block} {ofs : ptrofs} {bf : bitfield},
        evalLvalue ge e le m a = some (loc, ofs, bf) → eval_lvalue ge e le m a loc ofs bf
    | .Evar id ty, loc, ofs, bf, h => lvalOfVar_sound h
    | .Ederef a ty, loc, ofs, bf, h => by
        simp only [evalLvalue] at h
        split at h
        · rename_i ha
          cases h
          exact .eval_Ederef _ _ _ _ (evalExpr_sound ha)
        · cases h
    | .Efield a i ty, loc, ofs, bf, h => by
        simp only [evalLvalue] at h
        split at h
        · rename_i va ha
          exact lvalOfField_sound (evalExpr_sound ha) h
        · cases h
    | .Econst_int .., _, _, _, h | .Econst_float .., _, _, _, h
    | .Econst_single .., _, _, _, h | .Econst_long .., _, _, _, h
    | .Etempvar .., _, _, _, h | .Eaddrof .., _, _, _, h | .Eunop .., _, _, _, h
    | .Ebinop .., _, _, _, h | .Ecast .., _, _, _, h | .Esizeof .., _, _, _, h
    | .Ealignof .., _, _, _, h => by simp [evalLvalue] at h
end

theorem evalExprlist_sound {ge : genv} {e : env} {le : temp_env} {m : mem} :
    ∀ {as : List expr} {tys : List type} {vs : List val},
      evalExprlist ge e le m as tys = some vs → eval_exprlist ge e le m as tys vs
  | [], [], vs, h => by cases h; exact .nil
  | a :: as, ty :: tys, vs, h => by
      simp only [evalExprlist] at h
      split at h
      · rename_i v1 ha
        split at h
        · rename_i v2 hc
          split at h
          · rename_i vs' hr
            cases h
            exact .cons _ _ _ _ _ _ _ (evalExpr_sound ha) hc (evalExprlist_sound hr)
          · cases h
        · cases h
      · cases h
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [evalExprlist] at h

end NautyVerified.Exec

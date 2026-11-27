import NautyVerified.Exec.Expr

/-!
# A Clight interpreter

`doStep` executes one transition of CompCert4Lean's Clight `step` with
`function_entry2` (the semantics of SimplLocals output), and `runProgram` runs a
whole program from its initial state. The harness's external functions act on
a `World`: `nv_read` takes the next input value, `nv_write` appends to the
output, and volatile loads (nauty's `nauty_kill_request`) read zero.

This is a testing tool: running the linked program on the fixtures and
comparing with the native binary checks the exported program and the
semantics before anything is proved about them. Nothing in the proofs depends
on it.
-/

namespace NautyVerified.Exec

open CompCert4Lean
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST CompCert4Lean.Common.Values CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.Memdata
open CompCert4Lean.Cfrontend.Ctypes CompCert4Lean.Cfrontend.Cop CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open CompCert4Lean.Flocq.IEEE754.Binary (BinaryNormalizeCertificate)

variable [binary64_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

/-- The harness's input and output. -/
structure World where
  input : List Int
  output : Array Int := #[]

def bytesOf : Foundation.RocqString.Rocq.Coq.Strings.String.string → List UInt8
  | .EmptyString => []
  | .String c rest => c :: bytesOf rest

def nameIs (name : Foundation.RocqString.Rocq.Coq.Strings.String.string) (s : String) : Bool :=
  bytesOf name == s.toUTF8.toList

/-- The `ptrofs` that `Vptrofs` would have produced (64-bit). -/
def ptrofsOfVal : val → Option ptrofs
  | .Vlong n => some (Ptrofs.of_int64 n)
  | _ => none

/-- One external call, or `none` if the interpreter does not implement it. -/
def externalCall (ge : genv) (w : World) (ef : external_function) (vargs : List val)
    (m : mem) : Option (World × val × mem) :=
  match ef, vargs with
  | .EF_external name _, [] =>
      if nameIs name "nv_read" then
        match w.input with
        | x :: rest => some ({ w with input := rest }, .Vlong (Int64.repr (zOfInt x)), m)
        | [] => none
      else none
  | .EF_external name _, [.Vlong x] =>
      if nameIs name "nv_write" then
        some ({ w with output := w.output.push (intOfZ (Int64.signed x)) }, .Vundef, m)
      else none
  | .EF_vload chunk, [.Vptr b ofs] =>
      if Genv.block_is_volatile ge.genv_genv b then
        some (w, Val.load_result chunk (.Vint Int.zero), m)
      else (Mem.load chunk m b (Ptrofs.unsigned ofs)).map fun v => (w, v, m)
  | .EF_malloc, [v] =>
      match ptrofsOfVal v with
      | some sz =>
          let (m', b) := Mem.alloc m (ZArith.BinInt.Z.opp (size_chunk Mptr)) (Ptrofs.unsigned sz)
          (Mem.store Mptr m' b (ZArith.BinInt.Z.opp (size_chunk Mptr)) (Vptrofs sz)).map fun m'' =>
            (w, .Vptr b Ptrofs.zero, m'')
      | none => none
  | .EF_free, [.Vptr b lo] =>
      match Mem.load Mptr m b (ZArith.BinInt.Z.sub (Ptrofs.unsigned lo) (size_chunk Mptr)) with
      | some vsz =>
          match ptrofsOfVal vsz with
          | some sz =>
              (Mem.free m b (ZArith.BinInt.Z.sub (Ptrofs.unsigned lo) (size_chunk Mptr))
                (ZArith.BinInt.Z.add (Ptrofs.unsigned lo) (Ptrofs.unsigned sz))).map fun m' => (w, .Vundef, m')
          | none => none
      | none => none
  | .EF_free, [.Vlong n] => if Int64.eq n Int64.zero then some (w, .Vundef, m) else none
  | .EF_debug .., _ => some (w, .Vundef, m)
  | _, _ => none

/-- Executable `function_entry2`, without its distinctness side conditions. -/
def functionEntry2 (ge : genv) (f : function) (vargs : List val) (m : mem) :
    Option (env × temp_env × mem) :=
  let (e, m') := f.fn_vars.foldl (fun (e, m) (id, ty) =>
    let (m1, b1) := Mem.alloc m .Z0 (sizeof ge.genv_cenv ty)
    (PTree.set id (b1, ty) e, m1)) (empty_env, m)
  match bind_parameter_temps f.fn_params vargs (create_undef_temps f.fn_temps) with
  | some le => some (e, le, m')
  | none => none

/-- One transition, or `none` if stuck (for this interpreter). -/
def doStep (ge : genv) (w : World) : state → Option (World × state)
  | .State f (.Sassign a1 a2) k e le m =>
      match evalLvalue ge e le m a1, evalExpr ge e le m a2 with
      | some (loc, ofs, bf), some v2 =>
          match sem_cast v2 (typeof a2) (typeof a1) m with
          | some v =>
              (assignLoc ge.genv_cenv (typeof a1) m loc ofs v bf).map fun m' => (w, .State f .Sskip k e le m')
          | none => none
      | _, _ => none
  | .State f (.Sset id a) k e le m =>
      (evalExpr ge e le m a).map fun v => (w, .State f .Sskip k e (PTree.set id v le) m)
  | .State f (.Scall optid a al) k e le m =>
      match classify_fun (typeof a) with
      | .fun_case_f tyargs tyres cconv =>
          match evalExpr ge e le m a with
          | some vf =>
              match evalExprlist ge e le m al tyargs with
              | some vargs =>
                  match Genv.find_funct ge.genv_genv vf with
                  | some fd =>
                      if type_of_fundef fd = .Tfunction tyargs tyres cconv
                      then some (w, .Callstate fd vargs (.Kcall optid f e le k) m)
                      else none
                  | none => none
              | none => none
          | none => none
      | _ => none
  | .State f (.Sbuiltin optid ef tyargs al) k e le m =>
      match evalExprlist ge e le m al tyargs with
      | some vargs =>
          (externalCall ge w ef vargs m).map fun (w', vres, m') =>
            (w', .State f .Sskip k e (set_opttemp optid vres le) m')
      | none => none
  | .State f (.Ssequence s1 s2) k e le m => some (w, .State f s1 (.Kseq s2 k) e le m)
  | .State f (.Sifthenelse a s1 s2) k e le m =>
      match evalExpr ge e le m a with
      | some v1 =>
          (bool_val v1 (typeof a) m).map fun b => (w, .State f (if b then s1 else s2) k e le m)
      | none => none
  | .State f (.Sloop s1 s2) k e le m => some (w, .State f s1 (.Kloop1 s1 s2 k) e le m)
  | .State _ (.Sreturn none) k e _ m =>
      (Mem.free_list m (blocks_of_env ge e)).map fun m' => (w, .Returnstate .Vundef (call_cont k) m')
  | .State f (.Sreturn (some a)) k e le m =>
      match evalExpr ge e le m a with
      | some v =>
          match sem_cast v (typeof a) f.fn_return m with
          | some v' =>
              (Mem.free_list m (blocks_of_env ge e)).map fun m' =>
                (w, .Returnstate v' (call_cont k) m')
          | none => none
      | none => none
  | .State f (.Sswitch a sl) k e le m =>
      match evalExpr ge e le m a with
      | some v =>
          (sem_switch_arg v (typeof a)).map fun n =>
            (w, .State f (seq_of_labeled_statement (select_switch n sl)) (.Kswitch k) e le m)
      | none => none
  | .State f (.Slabel _ s) k e le m => some (w, .State f s k e le m)
  | .State f (.Sgoto lbl) k e le m =>
      (find_label lbl f.fn_body (call_cont k)).map fun (s', k') => (w, .State f s' k' e le m)
  | .State f .Sskip k e le m =>
      match k with
      | .Kseq s k' => some (w, .State f s k' e le m)
      | .Kloop1 s1 s2 k' => some (w, .State f s2 (.Kloop2 s1 s2 k') e le m)
      | .Kloop2 s1 s2 k' => some (w, .State f (.Sloop s1 s2) k' e le m)
      | .Kswitch k' => some (w, .State f .Sskip k' e le m)
      | .Kstop | .Kcall .. =>
          (Mem.free_list m (blocks_of_env ge e)).map fun m' => (w, .Returnstate .Vundef k m')
  | .State f .Sbreak k e le m =>
      match k with
      | .Kseq _ k' => some (w, .State f .Sbreak k' e le m)
      | .Kloop1 _ _ k' | .Kloop2 _ _ k' | .Kswitch k' => some (w, .State f .Sskip k' e le m)
      | _ => none
  | .State f .Scontinue k e le m =>
      match k with
      | .Kseq _ k' => some (w, .State f .Scontinue k' e le m)
      | .Kloop1 s1 s2 k' => some (w, .State f s2 (.Kloop2 s1 s2 k') e le m)
      | .Kswitch k' => some (w, .State f .Scontinue k' e le m)
      | _ => none
  | .Callstate (.Internal f) vargs k m =>
      (functionEntry2 ge f vargs m).map fun (e, le, m1) => (w, .State f f.fn_body k e le m1)
  | .Callstate (.External ef _ _ _) vargs k m =>
      (externalCall ge w ef vargs m).map fun (w', vres, m') => (w', .Returnstate vres k m')
  | .Returnstate v (.Kcall optid f e le k) m =>
      some (w, .State f .Sskip k e (set_opttemp optid v le) m)
  | .Returnstate _ _ _ => none

/-- How a run ended. -/
inductive RunResult where
  | done (exitCode : Int) (output : Array Int) (steps : Nat)
  | stuck (where_ : String) (output : Array Int) (steps : Nat)
  | outOfFuel (output : Array Int)

def describeVal : Option val → String
  | none => "none" | some .Vundef => "undef" | some (.Vint _) => "int" | some (.Vlong _) => "long"
  | some (.Vptr _ _) => "ptr" | some _ => "float"

def describe (ge : genv) : state → String
  | .State _ s _ e le m =>
      match s with
      | .Sassign a1 a2 =>
          let lv := evalLvalue ge e le m a1
          let rv := evalExpr ge e le m a2
          let mode := match access_mode (typeof a1) with
            | .By_value _ => "by_value" | .By_copy => "by_copy" | .By_reference => "by_ref" | .By_nothing => "nothing"
          let cast := match rv with
            | some v => describeVal (sem_cast v (typeof a2) (typeof a1) m) | none => "-"
          let isv := match typeof a1 with
            | .Tint _ _ a | .Tlong _ a | .Tpointer _ a => toString a.attr_volatile | _ => "?"
          s!"assign: lvalue {lv.isSome} rvalue {describeVal rv} cast {cast} mode {mode} volatile {isv}" | .Sset .. => "set" | .Scall .. => "call"
      | .Sbuiltin .. => "builtin" | .Sreturn .. => "return" | .Sifthenelse .. => "if"
      | _ => "statement"
  | .Callstate (.Internal _) _ _ _ => "internal call"
  | .Callstate (.External ef _ _ _) _ _ _ =>
      match ef with
      | .EF_external name _ => s!"external {String.fromUTF8! (ByteArray.mk (bytesOf name).toArray)}"
      | _ => "external"
  | .Returnstate .. => "return state"

/-- Run at most `fuel` steps. -/
def run (ge : genv) : Nat → Nat → World → state → RunResult
  | 0, _, w, _ => .outOfFuel w.output
  | fuel + 1, n, w, s =>
      match s with
      | .Returnstate (.Vint r) .Kstop _ => .done (intOfZ (Int.signed r)) w.output n
      | _ =>
          match doStep ge w s with
          | some (w', s') => run ge fuel (n + 1) w' s'
          | none => .stuck (describe ge s) w.output n

/-- Run a program's `main` on the given input. -/
def runProgram (p : program) (input : List Int) (fuel : Nat) : Option RunResult :=
  let ge := globalenv p
  match Genv.init_mem (program_of_program p) with
  | none => none
  | some m0 =>
      match Genv.find_symbol ge.genv_genv p.prog_main with
      | none => none
      | some b =>
          (Genv.find_funct_ptr ge.genv_genv b).map fun f =>
            run ge fuel 0 { input } (.Callstate f [] .Kstop m0)

end NautyVerified.Exec

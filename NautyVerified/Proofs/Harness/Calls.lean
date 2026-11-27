import NautyVerified.Proofs.Harness.Options
import NautyVerified.Proofs.Alloc.Zero

/-!
# The harness's calls

`wp_rd`: `t = nv_read()` returning any chosen `long`. `wp_wr`: `nv_write(e)`
for an `int` or `long` expression. `wp_za`: `t = nauty_zalloc(e)`, giving a
fresh zero-filled block. All in `main`'s environment `e`, which holds only the
local `stats`.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (Writes)
open NautyVerified.Proofs.Alloc (Fresh zallocSpec zalloc_satisfies zb)

/-- `nv_read()` in an environment without a local of that name. -/
theorem wp_rd {Q : Post} {e : env} {le : temp_env} {m : mem} (t : ident) (x : Lib.Integers.int64)
    (he : PTree.get dense.id.nv_read e = none)
    (hQ : Q.normal (tr1 (readEv x)) e (PTree.set t (.Vlong x) le) m) :
    Wp Statement.xi ge dense.fn.main (rd t) Q e le m := by
  refine wp_call (vf := .Vptr Block.nvRead Ptrofs.zero) (targs := []) (tres := tlong)
    (cc := cc_default) _ (readSpec x) (read_satisfies x) rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar, he, find_nvRead, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode])
    rfl (by simp [Genv.find_funct, funct_nvRead]) rfl rfl ?_
  rintro t' v m' ⟨rfl, rfl, rfl⟩
  exact hQ

/-- `nv_write(a)` for a `long` value. -/
theorem wp_wr {Q : Post} {e : env} {le : temp_env} {m : mem} {a : expr} {x : Lib.Integers.int64}
    (he : PTree.get dense.id.nv_write e = none)
    (ha : Exec.evalExprlist ge e le m [a] [tlong] = some [.Vlong x])
    (hQ : ∀ t, Writes t [intOfZ (Lib.Integers.Int64.signed x)] → Q.normal t e le m) :
    Wp Statement.xi ge dense.fn.main (wr a) Q e le m := by
  refine wp_call (vf := .Vptr Block.nvWrite Ptrofs.zero) (targs := [tlong]) (tres := .Tvoid)
    (cc := cc_default) _ (writeSpec x) (write_satisfies x) rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar, he, find_nvWrite, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode])
    ha (by simp [Genv.find_funct, funct_nvWrite]) rfl rfl ?_
  rintro t' v m' ⟨hw, rfl⟩
  exact hQ t' hw

/-- `t = nauty_zalloc(a)`. -/
theorem wp_za {Q : Post} {e : env} {le : temp_env} {m : mem} {a : expr} (t : ident) {sz : Nat}
    (he : PTree.get dense.id.nauty_zalloc e = none)
    (ha : Exec.evalExprlist ge e le m [a] [tulong] = some [.Vlong (lr sz)]) (hsz : sz < 2 ^ 62)
    (hQ : ∀ b m', Fresh m m' b sz →
      Mem.loadbytes m' b (zOfInt 0) (zOfInt sz) = some (List.replicate sz zb) →
      Q.normal E0 e (PTree.set t (.Vptr b Ptrofs.zero) le) m') :
    Wp Statement.xi ge dense.fn.main (za t a) Q e le m := by
  refine wp_call (vf := .Vptr Block.zalloc Ptrofs.zero) (targs := [tulong]) (tres := tptr .Tvoid)
    (cc := cc_default) _ (zallocSpec sz) (zalloc_satisfies sz) rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar, he, find_zalloc, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode])
    ha (by simp [Genv.find_funct, Program.funct_zalloc]) rfl ⟨rfl, hsz⟩ ?_
  rintro t' v m' ⟨rfl, b, rfl, hfr, hz⟩
  exact hQ b m' hfr hz

/-- `Logic.wp_store`, also reporting that every valid block stays valid. -/
theorem wp_storeV {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bo : block}
    {ofs : ptrofs} {o : Array Nat} {n : Nat}
    (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n)
    (hn : n < 2147483648) (p : ident) (hp : PTree.get p le = some (.Vptr bo ofs))
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (x : Int) (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (upd (ints o) c (.Vint (ir x))) n →
      Unch m m' (· = bo) → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) → Q.normal E0 e le m') :
    Wp Statement.xi ge f (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar p (tptr tint)) a (tptr tint)) tint) rhs)
      Q e le m := by
  have haddr : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tint)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint32 (intOfZ (Ptrofs.unsigned ofs)) c := by
    apply addr_elem ofs _ .Mint32 rfl rfl (by omega)
    have hf := harr.fits
    have h4 : csize .Mint32 = 4 := rfl
    rw [h4] at hf ⊢
    omega
  obtain ⟨m', hst, harr', -⟩ := store_array harr hc (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hrhs, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint32 m bo (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [haddr, hst]
  exact hQ m' harr' (Unch.store hst rfl) fun z hz => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ hz

end NautyVerified.Proofs.Harness

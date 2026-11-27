import NautyVerified.Proofs.Init.Tables
import NautyVerified.Proofs.Search.Blocks
import NautyVerified.Proofs.Harness.Spec
import NautyVerified.Proofs.Refine.Fn

/-!
# What the initial memory gives `nauty()`

nauty.c's static `int`s and pointers have no initialiser (`Init_space`), so
the initial memory holds 0 in them (`space32`, `space64`); every
non-read-only global is writable over its whole size (`globWritable`);
`dispatch_graph` holds the addresses of naugraph.c's routines
(`dispatchGraph_load`).
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.AST CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Proofs.Init (prog info var_init var_of_map)
open NautyVerified.Proofs.Search (FieldAt)
open NautyVerified.Source

namespace Block
def naugraphFreedyn : Common.Values.block := PArith.BinPos.Pos.of_nat 277
def naugraphCheck : Common.Values.block := PArith.BinPos.Pos.of_nat 133
def nautilCheck : Common.Values.block := PArith.BinPos.Pos.of_nat 217
def nautilFreedyn : Common.Values.block := PArith.BinPos.Pos.of_nat 141
def nautyFreedyn : Common.Values.block := PArith.BinPos.Pos.of_nat 183
end Block

kernel_rfl find_naugraphFreedyn :
  Genv.find_symbol ge.genv_genv dense.id.naugraph_freedyn = some Block.naugraphFreedyn
kernel_rfl find_naugraphCheck :
  Genv.find_symbol ge.genv_genv dense.id.naugraph_check = some Block.naugraphCheck
kernel_rfl find_nautilCheck :
  Genv.find_symbol ge.genv_genv dense.id.nautil_check = some Block.nautilCheck
kernel_rfl find_nautilFreedyn :
  Genv.find_symbol ge.genv_genv dense.id.nautil_freedyn = some Block.nautilFreedyn
kernel_rfl find_nautyFreedyn :
  Genv.find_symbol ge.genv_genv dense.id.nauty_freedyn = some Block.nautyFreedyn
kernel_rfl funct_naugraphCheck :
  Genv.find_funct_ptr ge.genv_genv Block.naugraphCheck = some (.Internal dense.fn.naugraph_check)
kernel_rfl funct_nautilCheck :
  Genv.find_funct_ptr ge.genv_genv Block.nautilCheck = some (.Internal dense.fn.nautil_check)
kernel_rfl funct_naugraphFreedyn :
  Genv.find_funct_ptr ge.genv_genv Block.naugraphFreedyn = some (.Internal dense.fn.naugraph_freedyn)
kernel_rfl funct_nautilFreedyn :
  Genv.find_funct_ptr ge.genv_genv Block.nautilFreedyn = some (.Internal dense.fn.nautil_freedyn)
kernel_rfl funct_nautyFreedyn :
  Genv.find_funct_ptr ge.genv_genv Block.nautyFreedyn = some (.Internal dense.fn.nauty_freedyn)

/-- A function's block has `Nonempty` permission at offset 0 in the initial memory. -/
theorem fnPerm {m : mem} (hm : Genv.init_mem prog = some m) {b : block} {f : Cfrontend.Clight.fundef}
    (hf : Genv.find_funct_ptr ge.genv_genv b = some f) :
    Mem.perm m b (zOfInt 0) .Cur .Nonempty := by
  have hg := Genv.init_mem_characterization_gen _ _ prog m hm
  rw [Init.ge_eq] at hf
  have hd := (Genv.find_funct_ptr_iff _ _ _ _ _).1 hf
  have := hg b _ hd
  exact this.1

/-- A writable global holds its writability over its whole initialiser. -/
theorem globWritable {m : mem} (hm : Genv.init_mem prog = some m) {b : block} {l : List init_data}
    (h : info b = some (l, false, false)) :
    Mem.range_perm m b (zOfInt 0) (init_data_list_size l) .Cur .Writable := by
  obtain ⟨v, hv, hi, hro, hvol⟩ := var_of_map h
  have h1 := (var_init hm hv hvol).1
  have hp : Genv.perm_globvar v = .Writable := by
    unfold Genv.perm_globvar; rw [hro, hvol]; rfl
  rw [hp, hi] at h1
  exact h1

/-- A zero-initialised `int` static holds 0 and is writable. -/
theorem space32 {m : mem} (hm : Genv.init_mem prog = some m) {b : block}
    (h : info b = some ([.Init_space (zOfInt 4)], false, false)) :
    FieldAt m .Mint32 b 0 (.Vint (ir 0)) := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_map h
  have h2 := (var_init hm hv hvol).2
  rw [hi] at h2
  refine ⟨?_, ?_⟩
  · have := h2.1 .Mint32 (zOfInt 0) (by decide) (by decide) ⟨zOfInt 0, rfl⟩
    exact this
  · exact ⟨globWritable hm h, ⟨zOfInt 0, rfl⟩⟩

/-- A zero-initialised pointer static holds `NULL` and is writable. -/
theorem space64 {m : mem} (hm : Genv.init_mem prog = some m) {b : block}
    (h : info b = some ([.Init_space (zOfInt 8)], false, false)) :
    FieldAt m .Mint64 b 0 Vnullptr := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_map h
  have h2 := (var_init hm hv hvol).2
  rw [hi] at h2
  refine ⟨?_, ?_⟩
  · have := h2.1 .Mint64 (zOfInt 0) (by decide) (by decide) ⟨zOfInt 0, rfl⟩
    exact this
  · exact ⟨globWritable hm h, ⟨zOfInt 0, rfl⟩⟩

/-- `dispatch_graph`'s initialiser: naugraph.c's seven routines, `naugraph_freedyn`,
`naugraph_check`, and two `NULL`s (`init`, `cleanup`). -/
def dispatchGraphInit : List init_data :=
  [.Init_addrof dense.id.isautom Ptrofs.zero, .Init_addrof dense.id.testcanlab Ptrofs.zero,
   .Init_addrof dense.id.updatecan Ptrofs.zero, .Init_addrof dense.id.refine Ptrofs.zero,
   .Init_addrof dense.id.refine1 Ptrofs.zero, .Init_addrof dense.id.cheapautom Ptrofs.zero,
   .Init_addrof dense.id.targetcell Ptrofs.zero, .Init_addrof dense.id.naugraph_freedyn Ptrofs.zero,
   .Init_addrof dense.id.naugraph_check Ptrofs.zero, .Init_int64 (lr 0), .Init_int64 (lr 0)]

kernel_rfl info_dispatchGraphInit :
  info Harness.Block.dispatchGraph = some (dispatchGraphInit, false, false)

/-- The values `dispatch_graph`'s fields hold, at `8 i`. -/
def dispatchVals : List val :=
  [.Vptr Search.Block.isautomFn Ptrofs.zero, .Vptr Search.Block.testcanlabFn Ptrofs.zero,
   .Vptr Search.Block.updatecanFn Ptrofs.zero, .Vptr Refine.Block.refine Ptrofs.zero,
   .Vptr Refine.Block.refine1 Ptrofs.zero, .Vptr Search.Block.cheapautomFn Ptrofs.zero,
   .Vptr Search.Block.targetcellFn Ptrofs.zero, .Vptr Block.naugraphFreedyn Ptrofs.zero,
   .Vptr Block.naugraphCheck Ptrofs.zero, .Vlong (lr 0), .Vlong (lr 0)]

theorem dispatchGraph_load {m : mem} (hm : Genv.init_mem prog = some m) :
    ∀ (i : Nat) (hi : i < 11), Mem.load .Mint64 m Harness.Block.dispatchGraph (zOfInt (8 * (i : Int))) =
      some (dispatchVals[i]'(by simp [dispatchVals]; omega)) := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_map info_dispatchGraphInit
  have h2 := (var_init hm hv hvol).2
  rw [hi] at h2
  rw [Init.ge_eq] at h2
  simp only [dispatchGraphInit, Genv.load_store_init_data] at h2
  obtain ⟨⟨b0, f0, l0⟩, ⟨b1, f1, l1⟩, ⟨b2, f2, l2⟩, ⟨b3, f3, l3⟩, ⟨b4, f4, l4⟩, ⟨b5, f5, l5⟩,
    ⟨b6, f6, l6⟩, ⟨b7, f7, l7⟩, ⟨b8, f8, l8⟩, l9, l10, -⟩ := h2
  rw [← Init.ge_eq] at f0 f1 f2 f3 f4 f5 f6 f7 f8
  rw [Search.find_isautomFn] at f0
  rw [Search.find_testcanlabFn] at f1
  rw [Search.find_updatecanFn] at f2
  rw [Refine.find_refine] at f3
  rw [Refine.find_refine1] at f4
  rw [Search.find_cheapautomFn] at f5
  rw [Search.find_targetcellFn] at f6
  rw [find_naugraphFreedyn] at f7
  rw [find_naugraphCheck] at f8
  cases f0; cases f1; cases f2; cases f3; cases f4; cases f5; cases f6; cases f7; cases f8
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first | omega | skip
  · exact l0
  · exact l1
  · exact l2
  · exact l3
  · exact l4
  · exact l5
  · exact l6
  · exact l7
  · exact l8
  · exact l9
  · exact l10

end NautyVerified.Proofs.Top

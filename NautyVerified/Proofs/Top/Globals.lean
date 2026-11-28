import NautyVerified.Proofs.Top.Init

/-!
# nauty.c's statics in the initial memory

`ints0`/`ptrs0`: nauty.c's static `int`s and pointer (or `unsigned long`)
statics that have no initialiser (`Init_space`), so the initial memory holds 0
in them and they are writable (`int0_init`, `ptr0_init`). `dispatch` is
writable over its 88 bytes (`dispatch_writable`). `nauty_kill_request` is a
volatile `int`: the initial memory gives its block a `Nonempty` permission
only (`kill_init`).
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.AST CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Proofs.Init (prog info var_init var_of_map)
open NautyVerified.Proofs.Search (FieldAt IntAt)
open NautyVerified.Source

/-- nauty.c's static `int`s without an initialiser. -/
def ints0 : List block :=
  [Search.Block.gcaFirst, Search.Block.gcaCanon, Search.Block.noncheaplevel,
   Search.Block.allsamelevel, Search.Block.eqlevFirst, Search.Block.eqlevCanon,
   Search.Block.compCanon, Search.Block.samerows, Search.Block.canonlevel,
   Search.Block.stabvertex, Search.Block.cosetindex, Search.Block.needshortprune,
   Search.Block.m, Search.Block.n, Search.Block.invarsuclevel, Search.Block.getcanon,
   Search.Block.digraph, Search.Block.writeautoms, Search.Block.cartesian,
   Search.Block.linelength, Search.Block.tcLevel, Search.Block.mininvarlevel,
   Search.Block.maxinvarlevel, Search.Block.invararg, Search.Block.domarkers,
   Search.Block.doschreier]

/-- nauty.c's static pointers and `unsigned long`s without an initialiser. -/
def ptrs0 : List block :=
  [Search.Block.g, Search.Block.canong, Search.Block.stats, Search.Block.orbits,
   Search.Block.workspace, Search.Block.worktop, Search.Block.fmptr, Search.Block.invapplics,
   Search.Block.invsuccesses, Search.Block.outfile, Search.Block.userautomproc,
   Search.Block.userlevelproc, Search.Block.usernodeproc, Search.Block.usercanonproc,
   Search.Block.invarproc]

kernel_rfl info_ints0 :
  ints0.map info = ints0.map fun _ => some ([.Init_space (zOfInt 4)], false, false)

kernel_rfl info_ptrs0 :
  ptrs0.map info = ptrs0.map fun _ => some ([.Init_space (zOfInt 8)], false, false)

kernel_rfl info_dispatch :
  info Search.Block.dispatch = some ([.Init_space (zOfInt 88)], false, false)

kernel_rfl info_kill :
  (info Search.Block.killRequest).map (fun x => (init_data_list_size x.1, x.2)) =
    some (zOfInt 4, false, true)

theorem info_of_map {l : List block} {x : Option (List init_data × Bool × Bool)}
    (h : l.map info = l.map fun _ => x) {b : block} (hb : b ∈ l) : info b = x := by
  induction l with
  | nil => cases hb
  | cons a l ih =>
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact ih h.2 hb

theorem int0_init {m : mem} (hm : Genv.init_mem prog = some m) {b : block} (hb : b ∈ ints0) :
    IntAt m b 0 :=
  space32 hm (info_of_map info_ints0 hb)

theorem ptr0_init {m : mem} (hm : Genv.init_mem prog = some m) {b : block} (hb : b ∈ ptrs0) :
    FieldAt m .Mint64 b 0 Vnullptr :=
  space64 hm (info_of_map info_ptrs0 hb)

theorem dispatch_writable {m : mem} (hm : Genv.init_mem prog = some m) :
    Mem.range_perm m Search.Block.dispatch (zOfInt 0) (zOfInt 88) .Cur .Writable :=
  globWritable hm info_dispatch

theorem kill_init {m : mem} (hm : Genv.init_mem prog = some m) :
    Mem.valid_access m .Mint32 Search.Block.killRequest (zOfInt 0) .Nonempty := by
  cases hf : Genv.find_var_info ge.genv_genv Search.Block.killRequest with
  | none => have := info_kill; simp [info, hf] at this
  | some v =>
    have hk := info_kill
    simp only [info, hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
    rw [Init.ge_eq] at hf
    have h := (Genv.init_mem_characterization _ _ prog _ v m hf hm).1
    have hp : Genv.perm_globvar v = .Nonempty := by
      unfold Genv.perm_globvar; rw [hk.2.2]; rfl
    rw [hp, hk.1] at h
    exact ⟨h, ⟨zOfInt 0, rfl⟩⟩

end NautyVerified.Proofs.Top

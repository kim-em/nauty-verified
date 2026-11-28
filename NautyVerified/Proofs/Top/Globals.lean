import NautyVerified.Proofs.Top.Init
import NautyVerified.Proofs.Dispatch.Spec
import NautyVerified.Program.Sparse

/-!
# nauty.c's statics in the initial memory

`ints0`/`ptrs0`: nauty.c's static `int`s and pointer (or `unsigned long`)
statics that have no initialiser (`Init_space`), so the initial memory holds 0
in them and they are writable (`int0_init`, `ptr0_init`). `dispatch` is
writable over its 88 bytes (`dispatch_writable`). `nauty_kill_request` is a
volatile `int`: the initial memory gives its block a `Nonempty` permission
only (`kill_init`).

`NautyInitG m` states these facts for any program linking nauty.c and nautil.c
(with their `DYNALLSTAT` pairs empty and the tables), `nautyInit_of` proves
them of any such program's initial memory, and `nautyInit_dense`,
`nautyInit_sparse` are the dense and sparse programs' instances.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.AST CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Proofs.Init (prog info var_init var_of_map)
open NautyVerified.Proofs.Search (FieldAt IntAt)
open NautyVerified.Proofs.Alloc (DynAt)
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

/-! ### Any program linking nauty.c and nautil.c

`NautyInitG m`: what the initial memory `m` of such a program holds in
nauty.c's and nautil.c's statics: the `ints0G`/`ptrs0G` statics at 0 and
writable, `dispatch` writable, the kill flag's permission, `alloc_m` and
`tcnode0.next` at 0, nautil.c's and nauty.c's nine `DYNALLSTAT` pairs at
capacity 0, and the tables. `nautyInit_of`: it holds in `Genv.init_mem p` for
any program `p` whose global environment is `ge`, since `NautyEnv` gives each
of these globals the dense program's initialiser (`var_*`); `nautyInit_dense`
and `nautyInit_sparse` are the two programs' instances. -/

section Generic

variable {ge : genv} [E : NautyEnv ge]

/-- nauty.c's static `int`s without an initialiser. -/
def ints0G : List block :=
  [E.gcaFirst, E.gcaCanon, E.noncheaplevel, E.allsamelevel, E.eqlevFirst, E.eqlevCanon,
   E.compCanon, E.samerows, E.canonlevel, E.stabvertex, E.cosetindex, E.needshortprune,
   E.m, E.n, E.invarsuclevel, E.getcanon, E.digraph, E.writeautoms, E.cartesian,
   E.linelength, E.tcLevel, E.mininvarlevel, E.maxinvarlevel, E.invararg, E.domarkers,
   E.doschreier]

/-- nauty.c's static pointers and `unsigned long`s without an initialiser. -/
def ptrs0G : List block :=
  [E.g, E.canong, E.stats, E.orbits, E.workspace, E.worktop, E.fmptr, E.invapplics,
   E.invsuccesses, E.outfile, E.userautomproc, E.userlevelproc, E.usernodeproc,
   E.usercanonproc, E.invarproc]

/-- nauty.c's and nautil.c's statics in the initial memory. -/
structure NautyInitG (m : mem) : Prop where
  ints0 : ∀ b ∈ (ints0G : List block), IntAt m b 0
  ptrs0 : ∀ b ∈ (ptrs0G : List block), FieldAt m .Mint64 b 0 Vnullptr
  dispatch : Mem.range_perm m E.dispatch (zOfInt 0) (zOfInt 88) .Cur .Writable
  kill : Mem.valid_access m .Mint32 E.killRequest (zOfInt 0) .Nonempty
  allocM : FieldAt m .Mint32 E.allocM 0 (.Vint (ir 0))
  tcnode0 : FieldAt m .Mint64 E.tcnode0 0 Vnullptr
  nautilWorkperm : ∀ c b, DynAt m E.nautilWorkperm E.nautilWorkpermSz c 0 b
  nautyCanonlab : ∀ c b, DynAt m E.nautyCanonlab E.nautyCanonlabSz c 0 b
  nautyDefltwork : ∀ c b, DynAt m E.nautyDefltwork E.nautyDefltworkSz c 0 b
  nautyActive : ∀ c b, DynAt m E.nautyActive E.nautyActiveSz c 0 b
  nautyCanoncode : ∀ c b, DynAt m E.nautyCanoncode E.nautyCanoncodeSz c 0 b
  nautyFixedpts : ∀ c b, DynAt m E.nautyFixedpts E.nautyFixedptsSz c 0 b
  nautyFirstcode : ∀ c b, DynAt m E.nautyFirstcode E.nautyFirstcodeSz c 0 b
  nautyWorkperm : ∀ c b, DynAt m E.nautyWorkperm E.nautyWorkpermSz c 0 b
  nautyFirsttc : ∀ c b, DynAt m E.nautyFirsttc E.nautyFirsttcSz c 0 b
  nautyFirstlab : ∀ c b, DynAt m E.nautyFirstlab E.nautyFirstlabSz c 0 b
  tables : Dispatch.ETables m

section Prog

variable {p : Common.AST.program Cfrontend.Clight.fundef Cfrontend.Ctypes.type}
  (hge : ge.genv_genv = Genv.globalenv p)

/-- A global's initialiser, permission and volatility in `ge`. -/
abbrev infoG (ge : genv) (b : block) : Option (List init_data × Bool × Bool) :=
  (Genv.find_var_info ge.genv_genv b).map
    (fun v => (v.gvar_init, v.gvar_readonly, v.gvar_volatile))

omit E in
include hge in
/-- The facts `init_mem` gives about a non-volatile global. -/
theorem var_initG {m : mem} (hm : Genv.init_mem p = some m) {b : block}
    {v : globvar Cfrontend.Ctypes.type} (hv : Genv.find_var_info ge.genv_genv b = some v)
    (hvol : v.gvar_volatile = false) :
    Mem.range_perm m b .Z0 (init_data_list_size v.gvar_init) .Cur (Genv.perm_globvar v) ∧
      Genv.load_store_init_data ge.genv_genv m b .Z0 v.gvar_init := by
  rw [hge] at hv ⊢
  have h := Genv.init_mem_characterization _ _ p b v m hv hm
  exact ⟨h.1, h.2.2.1 hvol⟩

omit E in
theorem var_of_mapG {b : block} {x : List init_data × Bool × Bool} (h : infoG ge b = some x) :
    ∃ v, Genv.find_var_info ge.genv_genv b = some v ∧ v.gvar_init = x.1 ∧
      v.gvar_readonly = x.2.1 ∧ v.gvar_volatile = x.2.2 := by
  cases hf : Genv.find_var_info ge.genv_genv b with
  | none => simp only [infoG, hf] at h; cases h
  | some v =>
    simp only [infoG, hf] at h
    cases h
    exact ⟨v, rfl, rfl, rfl, rfl⟩

omit E in
/-- Reading back an initialiser of 64-bit integers. -/
theorem loads64G {m : mem} {b : block} :
    ∀ (ws : List int64) (q : Int),
      Genv.load_store_init_data ge.genv_genv m b (zOfInt q) (ws.map .Init_int64) →
      ∀ i (hi : i < ws.length), Mem.load .Mint64 m b (zOfInt (q + 8 * i)) = some (.Vlong ws[i])
  | [], _, _, _, hi => absurd hi (by simp)
  | w :: ws, q, h, i, hi => by
    obtain ⟨h0, hr⟩ := h
    cases i with
    | zero => simpa using h0
    | succ i =>
      have hr' : Genv.load_store_init_data ge.genv_genv m b (zOfInt (q + 8)) (ws.map .Init_int64) := by
        rw [show q + 8 = q + ((8 : Nat) : Int) from rfl, ← Init.zadd_ofs q 8 rfl]; exact hr
      have := loads64G ws (q + 8) hr' i (by simpa using hi)
      rw [show q + 8 * ((i + 1 : Nat) : Int) = q + 8 + 8 * i by push_cast; omega]
      simpa using this

omit E in
/-- Reading back an initialiser of 32-bit integers. -/
theorem loads32G {m : mem} {b : block} :
    ∀ (ws : List Lib.Integers.int) (q : Int),
      Genv.load_store_init_data ge.genv_genv m b (zOfInt q) (ws.map .Init_int32) →
      ∀ i (hi : i < ws.length), Mem.load .Mint32 m b (zOfInt (q + 4 * i)) = some (.Vint ws[i])
  | [], _, _, _, hi => absurd hi (by simp)
  | w :: ws, q, h, i, hi => by
    obtain ⟨h0, hr⟩ := h
    cases i with
    | zero => simpa using h0
    | succ i =>
      have hr' : Genv.load_store_init_data ge.genv_genv m b (zOfInt (q + 4)) (ws.map .Init_int32) := by
        rw [show q + 4 = q + ((4 : Nat) : Int) from rfl, ← Init.zadd_ofs q 4 rfl]; exact hr
      have := loads32G ws (q + 4) hr' i (by simpa using hi)
      rw [show q + 4 * ((i + 1 : Nat) : Int) = q + 4 + 4 * i by push_cast; omega]
      simpa using this

omit E in
include hge in
theorem table64G {m : mem} (hm : Genv.init_mem p = some m) {b : block} {ws : List int64}
    {ro : Bool} (h : infoG ge b = some (ws.map .Init_int64, ro, false)) :
    ∀ i (hi : i < ws.length), Mem.load .Mint64 m b (zOfInt (8 * i)) = some (.Vlong ws[i]) := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_mapG h
  have h2 := (var_initG hge hm hv hvol).2
  rw [hi] at h2
  change Genv.load_store_init_data _ m b (zOfInt 0) (ws.map .Init_int64) at h2
  intro i hi
  simpa using loads64G ws 0 h2 i hi

omit E in
include hge in
theorem table32G {m : mem} (hm : Genv.init_mem p = some m) {b : block}
    {ws : List Lib.Integers.int} {ro : Bool} (h : infoG ge b = some (ws.map .Init_int32, ro, false)) :
    ∀ i (hi : i < ws.length), Mem.load .Mint32 m b (zOfInt (4 * i)) = some (.Vint ws[i]) := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_mapG h
  have h2 := (var_initG hge hm hv hvol).2
  rw [hi] at h2
  change Genv.load_store_init_data _ m b (zOfInt 0) (ws.map .Init_int32) at h2
  intro i hi
  simpa using loads32G ws 0 h2 i hi

omit E in
include hge in
theorem globWritableG {m : mem} (hm : Genv.init_mem p = some m) {b : block} {l : List init_data}
    (h : infoG ge b = some (l, false, false)) :
    Mem.range_perm m b (zOfInt 0) (init_data_list_size l) .Cur .Writable := by
  obtain ⟨v, hv, hi, hro, hvol⟩ := var_of_mapG h
  have h1 := (var_initG hge hm hv hvol).1
  have hp : Genv.perm_globvar v = .Writable := by
    unfold Genv.perm_globvar; rw [hro, hvol]; rfl
  rw [hp, hi] at h1
  exact h1

omit E in
include hge in
theorem space32G {m : mem} (hm : Genv.init_mem p = some m) {b : block}
    (h : infoG ge b = some ([.Init_space (zOfInt 4)], false, false)) :
    FieldAt m .Mint32 b 0 (.Vint (ir 0)) := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_mapG h
  have h2 := (var_initG hge hm hv hvol).2
  rw [hi] at h2
  exact ⟨h2.1 .Mint32 (zOfInt 0) (by decide) (by decide) ⟨zOfInt 0, rfl⟩,
    ⟨globWritableG hge hm h, ⟨zOfInt 0, rfl⟩⟩⟩

omit E in
include hge in
theorem space64G {m : mem} (hm : Genv.init_mem p = some m) {b : block}
    (h : infoG ge b = some ([.Init_space (zOfInt 8)], false, false)) :
    FieldAt m .Mint64 b 0 Vnullptr := by
  obtain ⟨v, hv, hi, -, hvol⟩ := var_of_mapG h
  have h2 := (var_initG hge hm hv hvol).2
  rw [hi] at h2
  exact ⟨h2.1 .Mint64 (zOfInt 0) (by decide) (by decide) ⟨zOfInt 0, rfl⟩,
    ⟨globWritableG hge hm h, ⟨zOfInt 0, rfl⟩⟩⟩

omit E in
include hge in
theorem dynAt_zeroG {m : mem} (hm : Genv.init_mem p = some m) {bp bs : block} (c : Nat)
    (b : block) (hne : bs ≠ bp)
    (hs : infoG ge bs = some ([.Init_int64 (lr 0)], false, false))
    (hp : infoG ge bp = some ([.Init_space (zOfInt 8)], false, false)) :
    DynAt m bp bs c 0 b where
  capLd := by
    have := table64G hge hm (ws := [lr 0]) hs 0 (by decide)
    simpa using this
  bsW := ⟨fun o ho => globWritableG hge hm hs o ho, ⟨zOfInt 0, rfl⟩⟩
  bpW := (space64G hge hm hp).writable
  ptr := fun h => absurd h (Nat.lt_irrefl 0)
  mal := fun h => absurd h (Nat.lt_irrefl 0)
  ne := hne
  bne := fun h => absurd h (Nat.lt_irrefl 0)
  small := by simp
  capLt := by decide
  null := fun _ => (space64G hge hm hp).load

omit E in
/-- Each global of `NautyEnv` has the dense program's initialiser in `ge`. -/
theorem infoG_eq {b b' : block}
    (h : Genv.find_var_info ge.genv_genv b = Genv.find_var_info Program.ge.genv_genv b') :
    infoG ge b = Init.info b' := by
  simp only [infoG, Init.info, h]

include hge in
theorem nautyInit_of {m : mem} (hm : Genv.init_mem p = some m) : NautyInitG m := by
  have dyn : ∀ {bp bs bp' bs' : block},
      Genv.find_var_info ge.genv_genv bp = Genv.find_var_info Program.ge.genv_genv bp' →
      Genv.find_var_info ge.genv_genv bs = Genv.find_var_info Program.ge.genv_genv bs' →
      bs ≠ bp →
      Init.info bs' = some ([.Init_int64 (lr 0)], false, false) →
      Init.info bp' = some ([.Init_space (zOfInt 8)], false, false) →
      ∀ c b, DynAt m bp bs c 0 b := fun hp hs hne is ip c b =>
    dynAt_zeroG hge hm c b hne ((infoG_eq hs).trans is) ((infoG_eq hp).trans ip)
  refine ⟨fun b hb => ?_, fun b hb => ?_, ?_, ?_, ?_, ?_,
    dyn E.var_nautilWorkperm E.var_nautilWorkpermSz (by env_ne) Init.info_nautilWorkpermSz
      Init.info_nautilWorkperm,
    dyn E.var_nautyCanonlab E.var_nautyCanonlabSz (by env_ne) Init.info_nautyCanonlabSz
      Init.info_nautyCanonlab,
    dyn E.var_nautyDefltwork E.var_nautyDefltworkSz (by env_ne) Init.info_nautyDefltworkSz
      Init.info_nautyDefltwork,
    dyn E.var_nautyActive E.var_nautyActiveSz (by env_ne) Init.info_nautyActiveSz
      Init.info_nautyActive,
    dyn E.var_nautyCanoncode E.var_nautyCanoncodeSz (by env_ne) Init.info_nautyCanoncodeSz
      Init.info_nautyCanoncode,
    dyn E.var_nautyFixedpts E.var_nautyFixedptsSz (by env_ne) Init.info_nautyFixedptsSz
      Init.info_nautyFixedpts,
    dyn E.var_nautyFirstcode E.var_nautyFirstcodeSz (by env_ne) Init.info_nautyFirstcodeSz
      Init.info_nautyFirstcode,
    dyn E.var_nautyWorkperm E.var_nautyWorkpermSz (by env_ne) Init.info_nautyWorkpermSz
      Init.info_nautyWorkperm,
    dyn E.var_nautyFirsttc E.var_nautyFirsttcSz (by env_ne) Init.info_nautyFirsttcSz
      Init.info_nautyFirsttc,
    dyn E.var_nautyFirstlab E.var_nautyFirstlabSz (by env_ne) Init.info_nautyFirstlabSz
      Init.info_nautyFirstlab, ⟨?_, ?_, ?_⟩⟩
  · refine space32G hge hm ?_
    simp only [ints0G, List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
      rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      refine (infoG_eq (by first
        | exact E.var_gcaFirst | exact E.var_gcaCanon | exact E.var_noncheaplevel
        | exact E.var_allsamelevel | exact E.var_eqlevFirst | exact E.var_eqlevCanon
        | exact E.var_compCanon | exact E.var_samerows | exact E.var_canonlevel
        | exact E.var_stabvertex | exact E.var_cosetindex | exact E.var_needshortprune
        | exact E.var_m | exact E.var_n | exact E.var_invarsuclevel | exact E.var_getcanon
        | exact E.var_digraph | exact E.var_writeautoms | exact E.var_cartesian
        | exact E.var_linelength | exact E.var_tcLevel | exact E.var_mininvarlevel
        | exact E.var_maxinvarlevel | exact E.var_invararg | exact E.var_domarkers
        | exact E.var_doschreier)).trans ?_
      exact info_of_map info_ints0 (by simp [ints0])
  · refine space64G hge hm ?_
    simp only [ptrs0G, List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      refine (infoG_eq (by first
        | exact E.var_g | exact E.var_canong | exact E.var_stats | exact E.var_orbits
        | exact E.var_workspace | exact E.var_worktop | exact E.var_fmptr
        | exact E.var_invapplics | exact E.var_invsuccesses | exact E.var_outfile
        | exact E.var_userautomproc | exact E.var_userlevelproc | exact E.var_usernodeproc
        | exact E.var_usercanonproc | exact E.var_invarproc)).trans ?_
      exact info_of_map info_ptrs0 (by simp [ptrs0])
  · exact globWritableG hge hm ((infoG_eq E.var_dispatch).trans info_dispatch)
  · cases hf : Genv.find_var_info ge.genv_genv E.killRequest with
    | none => have := info_kill; rw [← infoG_eq E.var_killRequest] at this; simp [infoG, hf] at this
    | some v =>
      have hk := info_kill
      rw [← infoG_eq E.var_killRequest] at hk
      simp only [infoG, hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      rw [hge] at hf
      have h := (Genv.init_mem_characterization _ _ p _ v m hf hm).1
      have hp : Genv.perm_globvar v = .Nonempty := by
        unfold Genv.perm_globvar; rw [hk.2.2]; rfl
      rw [hp, hk.1] at h
      exact ⟨h, ⟨zOfInt 0, rfl⟩⟩
  · have hi := (infoG_eq E.var_allocM).trans info_allocM
    refine ⟨by simpa using table32G hge hm hi 0 (by decide), fun o ho => ?_, ⟨zOfInt 0, rfl⟩⟩
    exact globWritableG hge hm hi o ⟨ho.1, ho.2⟩
  · have hi := (infoG_eq E.var_tcnode0).trans info_tcnode0
    have hl := table64G hge hm hi 0 (by decide)
    have hn : (Vnullptr : val) = .Vlong (lr 0) := by
      unfold Vnullptr; rw [if_pos (by decide)]; rfl
    refine ⟨by rw [hn]; simpa using hl, fun o ho => ?_, ⟨zOfInt 0, rfl⟩⟩
    refine globWritableG hge hm hi o ⟨ho.1, ?_⟩
    have := ho.2
    change intOfZ o < intOfZ _ at this ⊢
    simp only [intOfZ_add, intOfZ_zOfInt] at this
    have h8 : intOfZ (size_chunk .Mint64) = 8 := rfl
    have h16 : intOfZ (init_data_list_size ([lr 0, lr 0].map .Init_int64)) = 16 := rfl
    rw [h16]; omega
  · intro i hi
    have := table64G hge hm ((infoG_eq E.var_nautyBit).trans Init.info_nautyBit) i
      (by simpa [Init.bitWords] using hi)
    simp only [Init.bitWords, List.getElem_map, List.getElem_range] at this
    simp only [elemOfs, Int.zero_add, show csize .Mint64 = 8 from rfl]
    exact this
  · intro i hi
    have := table64G hge hm ((infoG_eq E.var_nautilBit).trans Init.info_nautilBit) i
      (by simpa [Init.bitWords] using hi)
    simp only [Init.bitWords, List.getElem_map, List.getElem_range] at this
    simp only [elemOfs, Int.zero_add, show csize .Mint64 = 8 from rfl]
    exact this
  · intro i hi
    have := table32G hge hm ((infoG_eq E.var_leftbit).trans Init.info_leftbit) i
      (by simpa [Init.leftbitWords] using hi)
    simpa [Init.leftbitWords] using this

end Prog

end Generic

/-- The dense program's instance. -/
theorem nautyInit_dense {m : mem} (hm : Genv.init_mem prog = some m) : NautyInitG m :=
  nautyInit_of Init.ge_eq hm

/-- The linked sparse program, as the memory model sees it. -/
abbrev sparseProg := Cfrontend.Ctypes.program_of_program Source.sparse.locals

kernel_rfl sparse_ge_eq : sparseGe.genv_genv = Genv.globalenv sparseProg

attribute [local instance] NautyEnv.sparse in
/-- The sparse program's instance. -/
theorem nautyInit_sparse {m : mem} (hm : Genv.init_mem sparseProg = some m) :
    NautyInitG (ge := sparseGe) m :=
  nautyInit_of sparse_ge_eq hm

end NautyVerified.Proofs.Top

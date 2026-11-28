import NautyVerified.Proofs.Top.Freedyn
import NautyVerified.Proofs.Top.NautyTc
import NautyVerified.Proofs.Search.Node.TcOps
import NautyVerified.Proofs.Search.Node.Tc
import NautyVerified.Proofs.Search.Node.FirstEnd

/-!
# nauty.c's `nauty_freedyn`

`nauty_freedyn` frees the target-cell list (each node and its cell), resets
`alloc_m` and `tcnode0.next`, and runs `DYNFREE` on nauty.c's nine pairs
(`nautyFreeIds`). `wp_tcLoop`: the list walk, from `TcChain` (whose entries
record `malloc`'s header) and the list's blocks distinct. Both `nauty_freedyn`
and nautil.c's `nautil_freedyn` (`nautilFreedyn_satisfiesG`) are shared by
every program, so their proofs are over any `NautyEnv`.
-/

namespace NautyVerified.Proofs.Top

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Source
open NautyVerified.Proofs.Alloc (DynAt FreeD dynfree seqR wp_dynfrees Malloced freeSpec free_satisfies)
open NautyVerified.Proofs.Search (FieldAt TcChain tcStruct tcF eval_tcF field_tcnodeNext field_tcnodeTcell)
open NautyVerified.Proofs.Set (sk)

set_option linter.unusedSimpArgs false

variable {ge : genv} [E : NautyEnv ge] {xi : ExternalCalls}

/-- A function running `DYNFREE` on the pairs `ds`, over any `NautyEnv`. -/
def dynfreeSpecG (ds : List FreeD) : FunSpec where
  pre args m := args = [] ∧ FreeD.Ok m ds
  post _ m t _ m' := t = E0 ∧ (∀ d ∈ ds, ∀ c b', DynAt m' d.bp d.bs c 0 b') ∧
    Unch m m' (fun z => z ∈ FreeD.globals ds ∨ ∃ d ∈ ds, 0 < d.cap ∧ z = d.blk) ∧
    Mem.nextblock m' = Mem.nextblock m

/-- nautil.c's pair. -/
def nautilDsG (cap : Nat) (b : block) : List FreeD :=
  [⟨dense.id.«nautil:workperm», dense.id.«nautil:workperm_sz», E.nautilWorkperm,
    E.nautilWorkpermSz, tint, 4, cap, b⟩]

theorem nautilFreedyn_satisfiesG (cap : Nat) (b : block) :
    Satisfies xi ge (.Internal dense.fn.nautil_freedyn) (dynfreeSpecG (nautilDsG cap b)) := by
  let le0 := create_undef_temps dense.fn.nautil_freedyn.fn_temps
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧ le = le0 ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, le0, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hok⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.nautil_freedyn.fn_body_eq, body_nautilFreedyn]
    exact wp_dynfrees Alloc.noShadow_empty (nautilDsG cap b) _ hok
      (fun m' hD hu hnb => ⟨m', rfl, rfl, hD, hu, hnb⟩)

/-- The list from a node pointer `v` on: `v` is `NULL` at the end, else the
node `nd` holding its cell `tc`, both `malloc`ed, and the list from `nd`'s
`next` on. -/
def ChainFrom (m : mem) (M : Nat) : val → List (block × block) → Prop
  | v, [] => v = Vnullptr
  | v, (nd, tc) :: rest => v = .Vptr nd Ptrofs.zero ∧
      FieldAt m .Mint64 nd 8 (.Vptr tc Ptrofs.zero) ∧
      (Malloced m nd 16 ∧ Malloced m tc (8 * M)) ∧ TcChain m M nd rest

theorem TcChain.from {m : mem} {M : Nat} {prev : block} :
    ∀ {chain : List (block × block)}, TcChain m M prev chain →
      ∃ v, FieldAt m .Mint64 prev 0 v ∧ ChainFrom m M v chain
  | [], h => ⟨_, h, rfl⟩
  | (_, _) :: _, ⟨h1, h2, _, h4, h5⟩ => ⟨_, h1, rfl, h2, h4, h5⟩

/-- The list's blocks. -/
abbrev flat (chain : List (block × block)) : List block := chain.flatMap fun p => [p.1, p.2]

theorem ChainFrom.unch {m m' : mem} {M : Nat} {S : block → Prop} (hu : Unch m m' S) :
    ∀ {v : val} {chain : List (block × block)}, ChainFrom m M v chain →
      (∀ z ∈ flat chain, ¬ S z) → ChainFrom m' M v chain
  | _, [], h, _ => h
  | _, (nd, tc) :: rest, ⟨h1, h2, ⟨k1, k2⟩, h3⟩, hS => by
    have hnd : ¬ S nd := hS nd (by simp [flat])
    have htc : ¬ S tc := hS tc (by simp [flat])
    refine ⟨h1, Search.FieldAt.unch' h2 hu hnd, ⟨k1.keep (Alloc.Keep.unch hu hnd),
      k2.keep (Alloc.Keep.unch hu htc)⟩, TcChain.unch hu h3 fun z hz => ?_⟩
    simp only [Search.tcBlocks, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hnd
    · exact hS z (by simp only [flat, List.flatMap_cons, List.mem_append]; exact .inr hz)

/-- `while (tcp != NULL) { tcq = tcp->next; FREES(tcp->tcellptr); FREES(tcp); tcp = tcq; }` -/
abbrev tcLoop : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .One (.Etempvar dense.id.«tcp» (tptr tcStruct))
        (.Ecast (ci 0 tint) (tptr .Tvoid)) tint) .Sskip .Sbreak))
      (.Ssequence
        (sk (.Sset dense.id.«tcq» (tcF dense.id.«tcp» dense.id.«next» (tptr tcStruct))))
        (.Ssequence
          (sk (.Scall none (.Evar dense.id.free (tfun [tptr .Tvoid] .Tvoid))
            [tcF dense.id.«tcp» dense.id.«tcellptr» (tptr tulong)]))
          (.Ssequence
            (sk (.Scall none (.Evar dense.id.free (tfun [tptr .Tvoid] .Tvoid))
              [.Etempvar dense.id.«tcp» (tptr tcStruct)]))
            (sk (.Sset dense.id.«tcp» (.Etempvar dense.id.«tcq» (tptr tcStruct))))))))
    .Sskip

omit E in
theorem ne_ptr_null {m : mem} {b : block} (t : type) (hp : Mem.perm m b (zOfInt (-1)) .Cur .Nonempty) :
    Cfrontend.Cop.sem_binary_operation ge.genv_cenv .One (.Vptr b Ptrofs.zero) (tptr t)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
      (tptr .Tvoid) m = some (Val.of_bool true) := by
  have hvp : Mem.valid_pointer m b (zOfInt (-1)) = true := (Mem.valid_pointer_nonempty_perm m b _).2 hp
  have h1 : Cfrontend.Cop.sem_binary_operation ge.genv_cenv .One (.Vptr b Ptrofs.zero) (tptr t)
      (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
      (tptr .Tvoid) m = (Val.cmplu_bool (Mem.valid_pointer m) .Cne (.Vptr b Ptrofs.zero)
        (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))).map
        Val.of_bool := rfl
  rw [h1]
  unfold Val.cmplu_bool
  show Option.map _ (if _ && _ && (Mem.valid_pointer m b _ || Mem.valid_pointer m b (zOfInt (-1)))
    then _ else _) = _
  rw [hvp, Bool.or_true]
  rfl

/-- The walk's state after freeing the prefix `pre` of the list `chain₀`. -/
def WalkAt (M : Nat) (chain₀ : List (block × block)) (m₀ : mem) (le₀ : temp_env) (k : Nat)
    (le : temp_env) (m : mem) : Prop :=
  ∃ pre rest v, pre ++ rest = chain₀ ∧ rest.length = k ∧ PTree.get dense.id.«tcp» le = some v ∧
    ChainFrom m M v rest ∧ Unch m₀ m (· ∈ flat pre) ∧ Mem.nextblock m = Mem.nextblock m₀ ∧
    (∀ x, x ≠ dense.id.«tcp» → x ≠ dense.id.«tcq» → PTree.get x le = PTree.get x le₀)

theorem flat_append (a b : List (block × block)) : flat (a ++ b) = flat a ++ flat b := by
  simp [flat]

/-- The list walk frees exactly the list's blocks. -/
theorem wp_tcLoop {Q : Post} {M : Nat} {chain₀ : List (block × block)} {le₀ : temp_env} {m₀ : mem}
    (hd : (flat chain₀).Pairwise (· ≠ ·))
    (hQ : ∀ le' m', Unch m₀ m' (· ∈ flat chain₀) → Mem.nextblock m' = Mem.nextblock m₀ →
      (∀ x, x ≠ dense.id.«tcp» → x ≠ dense.id.«tcq» → PTree.get x le' = PTree.get x le₀) →
      Q.normal E0 empty_env le' m')
    {le : temp_env} {m : mem} (h : WalkAt M chain₀ m₀ le₀ chain₀.length le m) :
    Wp xi ge dense.fn.nauty_freedyn tcLoop Q empty_env le m := by
  refine wp_loop (I := fun k t e le m => t = E0 ∧ e = empty_env ∧ WalkAt M chain₀ m₀ le₀ k le m)
    (J := fun k t e le m => t = E0 ∧ e = empty_env ∧ ∃ k' < k, WalkAt M chain₀ m₀ le₀ k' le m)
    ?_ ?_ (n := chain₀.length) ⟨rfl, rfl, h⟩
  · rintro k t e le m ⟨rfl, rfl, pre, rest, v, happ, hlen, hv, hc, hu, hnb, ho⟩
    wp_step; wp_step; wp_step
    apply wp_if_eval
    cases rest with
    | nil =>
      have hv' : v = Vnullptr := hc
      subst hv'
      simp only [Exec.evalExpr, hv, typeof]
      rw [show Cfrontend.Cop.sem_cast (Vint (Lib.Integers.Int.repr (zOfInt 0))) tint (tptr .Tvoid) m =
        some (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
        from rfl]
      simp only []
      rw [Search.ne_null]
      simp only [cop, Val.of_bool, Bool.false_eq_true, ite_false]
      rw [show Cfrontend.Cop.bool_val Vfalse tint m = some false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      apply wp_break
      simp only [List.append_nil] at happ
      subst happ
      simpa using hQ le m hu hnb ho
    | cons p rest =>
      obtain ⟨nd, tc⟩ := p
      obtain ⟨rfl, hf8, ⟨mnd, mtc⟩, hrest⟩ := hc
      obtain ⟨v', hf0, hcf⟩ := TcChain.from hrest
      have hd' := hd
      rw [← happ, flat_append, List.pairwise_append] at hd'
      obtain ⟨-, hdr, -⟩ := hd'
      simp only [flat, List.flatMap_cons, List.cons_append, List.nil_append, List.pairwise_cons,
        List.mem_cons] at hdr
      obtain ⟨hnd, htc, hdr'⟩ := hdr
      have ntc : nd ≠ tc := hnd tc (.inl rfl)
      simp only [Exec.evalExpr, hv, typeof]
      rw [show Cfrontend.Cop.sem_cast (Vint (Lib.Integers.Int.repr (zOfInt 0))) tint (tptr .Tvoid) m =
        some (.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))))
        from rfl]
      simp only []
      rw [ne_ptr_null _ (Mem.perm_implies _ _ _ _ _ _ (mnd.perm (-1) (by decide) (by omega)) (.perm_F_any _))]
      simp only []
      rw [show Cfrontend.Cop.bool_val (Val.of_bool true) tint m = some true from rfl]
      simp only [ite_true]
      apply wp_skip
      simp only [seqPost, Post.after, E0_append]
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [eval_tcF (off := 0) hv (field_tcnodeNext _ _) (by decide) hf0]
      simp only []
      wp_step; wp_step; wp_step
      have hv1 : PTree.get dense.id.«tcp» (PTree.set dense.id.«tcq» v' le) = some (.Vptr nd Ptrofs.zero) := by
        rw [temps_gso _ _ (by decide)]; exact hv
      refine wp_call (vf := .Vptr E.free Ptrofs.zero) _ (freeSpec tc (8 * M)) (free_satisfies tc _) rfl
        (by simp [Exec.evalExpr, Exec.lvalOfVar, empty_env, E.find_free, Exec.derefLoc,
          Cfrontend.Ctypes.access_mode])
        (by simp only [Exec.evalExprlist]; rw [eval_tcF (off := 8) hv1 (field_tcnodeTcell _ _) (by decide) hf8]; rfl)
        (by simp [Common.Globalenvs.Genv.find_funct, E.funct_free]) rfl ⟨rfl, mtc⟩ ?_
      rintro t1 r1 m1 ⟨rfl, rfl, hu1, hnb1⟩
      simp only [seqPost, Post.after, E0_append, set_opttemp]
      wp_step; wp_step; wp_step
      refine wp_call (vf := .Vptr E.free Ptrofs.zero) _ (freeSpec nd 16) (free_satisfies nd _) rfl
        (by simp [Exec.evalExpr, Exec.lvalOfVar, empty_env, E.find_free, Exec.derefLoc,
          Cfrontend.Ctypes.access_mode])
        (by simp only [Exec.evalExprlist, Exec.evalExpr, hv1]; rfl)
        (by simp [Common.Globalenvs.Genv.find_funct, E.funct_free]) rfl
        ⟨rfl, mnd.keep (Alloc.Keep.unch hu1 ntc)⟩ ?_
      rintro t2 r2 m2 ⟨rfl, rfl, hu2, hnb2⟩
      simp only [seqPost, Post.after, E0_append, set_opttemp]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss]
      refine ⟨by first | rfl | trivial, by first | rfl | trivial, rest.length, by simp at hlen ⊢; omega, pre ++ [(nd, tc)], rest, v',
        by simpa using happ, rfl, temps_gss _ _ _, ?_, ?_, ?_, ?_⟩
      · refine (hcf.unch hu1 fun z hz e => ?_).unch hu2 fun z hz e => ?_
        · subst e; exact htc z hz rfl
        · subst e; exact hnd z (.inr hz) rfl
      · refine ((hu.mono fun z hz => ?_).trans (hu1.mono fun z hz => ?_)).trans (hu2.mono fun z hz => ?_)
        · simp [flat_append, hz]
        · subst hz; simp [flat_append, flat]
        · subst hz; simp [flat_append, flat]
      · rw [hnb2, hnb1, hnb]
      · intro x h1 h2
        rw [temps_gso _ _ h1, temps_gso _ _ h2, ho x h1 h2]
  · rintro k t e le m ⟨rfl, rfl, k', hk', hw⟩
    apply wp_skip
    exact ⟨k', hk', rfl, rfl, hw⟩


theorem FreeD.Ok.unch' {m m' : mem} {ds : List FreeD} (h : FreeD.Ok m ds) {W : block → Prop}
    (hu : Unch m m' W) (hg : ∀ z ∈ FreeD.globals ds, ¬ W z)
    (hb : ∀ d ∈ ds, 0 < d.cap → ¬ W d.blk) : FreeD.Ok m' ds :=
  { h with
    dyn := fun d hd => (h.dyn d hd).keep hu (hg _ (FreeD.mem_globals hd).2)
      (hg _ (FreeD.mem_globals hd).1) (fun hc => Alloc.Keep.unch hu (hb d hd hc)) }

/-- nauty.c's nine `DYNALLSTAT` pairs as `nauty_freedyn` releases them. -/
def nautyFreeIds : List (ident × ident × type) :=
  [(dense.id.«nauty:firsttc», dense.id.«nauty:firsttc_sz», tint),
   (dense.id.«nauty:canoncode», dense.id.«nauty:canoncode_sz», tshort),
   (dense.id.«nauty:firstcode», dense.id.«nauty:firstcode_sz», tshort),
   (dense.id.«nauty:workperm», dense.id.«nauty:workperm_sz», tint),
   (dense.id.«nauty:canonlab», dense.id.«nauty:canonlab_sz», tint),
   (dense.id.«nauty:firstlab», dense.id.«nauty:firstlab_sz», tint),
   (dense.id.«nauty:defltwork», dense.id.«nauty:defltwork_sz», tulong),
   (dense.id.«nauty:fixedpts», dense.id.«nauty:fixedpts_sz», tulong),
   (dense.id.«nauty:active», dense.id.«nauty:active_sz», tulong)]

/-- `tcnode0.next`, in `nauty_freedyn`. -/
abbrev tcHead0 : expr :=
  .Efield (.Evar dense.id.«nauty:tcnode0» tcStruct) dense.id.«next» (tptr tcStruct)

kernel_rfl body_nautyFreedyn : dense.body.nauty_freedyn =
  .Ssequence (sk (.Sset dense.id.«tcp» tcHead0))
    (.Ssequence tcLoop
      (.Ssequence (sk (.Sassign (.Evar dense.id.«nauty:alloc_m» tint) (ci 0 tint)))
        (.Ssequence (sk (.Sassign tcHead0 (.Ecast (ci 0 tint) (tptr .Tvoid))))
          (seqR (nautyFreeIds.map fun p => dynfree p.1 p.2.1 p.2.2)))))

/-- `nauty_freedyn()` on the target-cell list `chain` and the pairs `ds`. -/
def nautyFreedynSpec (M : Nat) (chain : List (block × block)) (ds : List FreeD) : FunSpec where
  pre args m := args = [] ∧ ds.map (fun d => (d.gp, d.gs, d.elt)) = nautyFreeIds ∧
    TcChain m M E.tcnode0 chain ∧ (flat chain).Pairwise (· ≠ ·) ∧
    (∀ z ∈ flat chain, z ≠ E.allocM ∧ z ≠ E.tcnode0 ∧
      z ∉ FreeD.globals ds ∧ ∀ d ∈ ds, 0 < d.cap → z ≠ d.blk) ∧
    FreeD.Ok m ds ∧ Mem.valid_access m .Mint32 E.allocM (zOfInt 0) .Writable ∧
    E.allocM ∉ FreeD.globals ds ∧ E.tcnode0 ∉ FreeD.globals ds ∧
    (∀ d ∈ ds, 0 < d.cap → d.blk ≠ E.allocM ∧ d.blk ≠ E.tcnode0)
  post _ m t _ m' := t = E0 ∧ Search.IntAt m' E.allocM 0 ∧
    FieldAt m' .Mint64 E.tcnode0 0 Vnullptr ∧ (∀ d ∈ ds, ∀ c b', DynAt m' d.bp d.bs c 0 b') ∧
    Unch m m' (fun z => z ∈ flat chain ∨ z = E.allocM ∨ z = E.tcnode0 ∨
      z ∈ FreeD.globals ds ∨ ∃ d ∈ ds, 0 < d.cap ∧ z = d.blk) ∧
    (∀ z, Mem.valid_block m z → Mem.valid_block m' z)

theorem nautyFreedyn_satisfies (M : Nat) (chain : List (block × block)) (ds : List FreeD) :
    Satisfies xi ge (.Internal dense.fn.nauty_freedyn) (nautyFreedynSpec M chain ds) := by
  let le0 := create_undef_temps dense.fn.nauty_freedyn.fn_temps
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧ le = le0 ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, le0, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hids, hT, hd, hap, hok, hwA, hgA, hgT, hbl⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.nauty_freedyn.fn_body_eq, body_nautyFreedyn]
    obtain ⟨v, hf0, hcf⟩ := TcChain.from hT
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [tcHead0, Exec.evalExpr, Exec.evalLvalue, Exec.lvalOfVar,
      show PTree.get Source.dense.id.«nauty:tcnode0» (empty_env : env) = none from rfl,
      E.find_tcnode0, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv, typeof]
    rw [field_tcnodeNext]
    show match Mem.load _ _ _ (Ptrofs.unsigned _) with | some v => _ | none => False
    rw [Search.unsigned_add_off Ptrofs.zero (by decide) (by decide)]
    rw [Alloc.Mptr_eq, show Mem.load .Mint64 _ E.tcnode0
      (zOfInt (intOfZ (Ptrofs.unsigned Ptrofs.zero) + 0)) = some v by simpa using hf0.load]
    simp only []
    wp_step
    refine wp_tcLoop (M := M) (le₀ := le0) hd ?_ ⟨[], chain, v, rfl, rfl, temps_gss _ _ _, hcf,
      Unch.refl _ _, rfl, fun x h1 _ => temps_gso _ _ h1⟩
    intro le1 m1 hu1 hnb1 ho1
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine Search.wp_gint rfl E.find_allocM (hu1.access _ _ _ _ (fun h => (hap _ h).1 rfl) hwA)
      (rhs := ci 0 tint) (x := 0) rfl rfl ?_
    intro m2 hA2 hu2 hv2
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    have hTw : Mem.valid_access m2 .Mint64 E.tcnode0 (zOfInt 0) .Writable :=
      hu2.access _ _ _ _ (by env_ne) (hu1.access _ _ _ _ (fun h => (hap _ h).2.1 rfl) hf0.writable)
    obtain ⟨m3, hst⟩ := Mem.valid_access_store _ Mptr _ _ Vnullptr hTw
    apply wp_assign_eval
    simp only [tcHead0, Exec.evalLvalue, Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get Source.dense.id.«nauty:tcnode0» (empty_env : env) = none from rfl,
      E.find_tcnode0, typeof, cop, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
    rw [field_tcnodeNext]
    simp only [Exec.assignLoc, Cfrontend.Ctypes.access_mode, Mem.storev]
    rw [Search.unsigned_add_off Ptrofs.zero (by decide) (by decide),
      show zOfInt (intOfZ (Ptrofs.unsigned Ptrofs.zero) + 0) = zOfInt 0 from rfl,
      show val.Vlong (Lib.Integers.Int64.repr (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 0)))) =
        Vnullptr from rfl, cast_null_ptr]
    simp only [hst, E0_append]
    rw [← hids, List.map_map]
    have hu3 : Unch m m3 (fun z => z ∈ flat chain ∨ z = E.allocM ∨ z = E.tcnode0) :=
      ((hu1.mono fun z h => .inl h).trans (hu2.mono fun z h => .inr (.inl h))).trans
        ((Unch.store hst rfl).mono fun z h => .inr (.inr h.symm))
    have hok3 : FreeD.Ok m3 ds := FreeD.Ok.unch' hok hu3
      (fun z hz h => by
        rcases h with h | rfl | rfl
        · exact (hap z h).2.2.1 hz
        · exact hgA hz
        · exact hgT hz)
      (fun d hd hc h => by
        rcases h with h | h | h
        · exact (hap _ h).2.2.2 d hd hc rfl
        · exact (hbl d hd hc).1 h
        · exact (hbl d hd hc).2 h)
    refine wp_dynfrees Alloc.noShadow_empty ds m3 hok3 (fun m4 hD4 hu4 hnb4 => ⟨m4, rfl, rfl, ?_, ?_, hD4,
      ?_, ?_⟩)
    · have nA : ¬ (E.allocM ∈ FreeD.globals ds ∨
          ∃ d ∈ ds, 0 < d.cap ∧ E.allocM = d.blk) := by
        rintro (h | ⟨d, hd, hc, e⟩)
        · exact hgA h
        · exact (hbl d hd hc).1 e.symm
      exact (hA2.unch (Unch.store hst rfl) (by env_ne)).unch hu4 nA
    · have nT : ¬ (E.tcnode0 ∈ FreeD.globals ds ∨
          ∃ d ∈ ds, 0 < d.cap ∧ E.tcnode0 = d.blk) := by
        rintro (h | ⟨d, hd, hc, e⟩)
        · exact hgT h
        · exact (hbl d hd hc).2 e.symm
      exact (FieldAt.store_same hst hTw).unch hu4 nT
    · exact (hu3.mono fun z h => by rcases h with h | h | h <;> simp [h]).trans
        (hu4.mono fun z h => by rcases h with h | h <;> simp [h])
    · intro z hz
      unfold Mem.valid_block at hz ⊢
      rw [hnb4, Mem.nextblock_store _ _ _ _ _ _ hst]
      exact hv2 _ (by unfold Mem.valid_block; rw [hnb1]; exact hz)

end NautyVerified.Proofs.Top

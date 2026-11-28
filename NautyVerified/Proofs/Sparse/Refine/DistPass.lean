import NautyVerified.Proofs.Sparse.Refine.Dist
import NautyVerified.Proofs.Sparse.Refine.Wide

/-!
# The distance pass of `refine_sg`

`wp_dist`: when `distCond` holds, the sole queue entry is removed from the
queue and from `active`, `distvals` fills `HITS` with the distances from
its vertex (and may move `work4`, its queue), and the cell loop
(`wp_distLoop`) runs HexGraphIso's `Refinement.distance` from
`Refinement.distanceStart`; otherwise nothing happens. `distRes` is the
state either way.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk pv delElementB)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Sparse.Distvals (cast_b distvalsSpec distvals_satisfies)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph splitCounts DistanceState)
open Hex.GraphIso.Nauty.Sparse.Refinement (distance distanceStart)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n}

/-- The state after the distance pass. -/
def distRes (g : Graph n) (level : Nat) (t : RefineSt n) : RefineSt n :=
  if distCond level t then distance level (distanceStart g t) else t

/-- The temporaries `dist` assigns besides those of the cell loop. -/
def distSet : List ident := [idOf 715, idOf 726, idOf 727, idOf 728, id.«isplit»]

/-- The removal of the sole queue entry. -/
abbrev takeS : statement :=
  .Ssequence
    (.Ssequence
      (sk (.Sset (idOf 715) (.Ecast (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint) tint)))
      (.Sset id.«nactive» (tv (idOf 715))))
    (.Sset id.«isplit» (gix id.«nausparse:work2» (tv (idOf 715))))

/-- `distvals(g, lab[isplit], work3, n)`. -/
abbrev callS : statement :=
  sk
    (.Scall none
      (.Evar id.«distvals» (tfun [(tptr (Tstruct id.«_1406» noattr)), tint, (tptr tint), tint] Tvoid))
      [(.Ecast (pv id.«g») (tptr (Tstruct id.«_1406» noattr))),
       (ix id.«lab» (tv id.«isplit»)),
       (.Evar id.«nausparse:work3» (tptr tint)),
       (tv id.«n»)])

theorem dist_eq : dist =
    .Ssequence distTest (.Sifthenelse (tv (idOf 728))
      (.Ssequence takeS (.Ssequence (delElementB id.«active» id.«nausparse:bit» (tv id.«isplit»))
        (.Ssequence callS (.Ssequence (sk (.Sset id.«v1» (ci 0 tint))) distLoop)))) .Sskip) := rfl

theorem w4_eq : Sparse.Block.work4 = Block.work4 := rfl
theorem w4s_eq : Sparse.Block.work4Sz = Block.work4Sz := rfl

theorem type_distvals :
    type_of_fundef (.Internal sparse.fn.distvals) =
      tfun [(tptr (Tstruct id.«_1406» noattr)), tint,
        (tptr tint), tint] Tvoid := rfl

theorem wp_dist (hC : CountPass (xi := xi)) {Q : Post} {le : temp_env} {m : mem} {t : RefineSt n}
    {S : Scr} (hok : Ok n L) (hm : Mem m L G t S) (hr : Rep L t S) (ht : Tmp le L t)
    (hv : t.Valid L.level) (hb : Budget L.level t) (hc : t.longcode < 2 ^ 62) (hgs : GSep L)
    (hbe : Mem.valid_block m L.be)
    (hQ : ∀ (b4 : block) (c4 : Nat) le' m' S', ((c4 = L.c4 ∧ b4 = L.b4) ∨ ¬ Mem.valid_block m b4) →
      n ≤ c4 →
      Mem m' (L.with4 b4 c4) G (distRes (.ofGraph G) L.level t) S' →
      Rep (L.with4 b4 c4) (distRes (.ofGraph G) L.level t) S' →
      Tmp le' (L.with4 b4 c4) (distRes (.ofGraph G) L.level t) →
      (distRes (.ofGraph G) L.level t).Valid L.level →
      Budget L.level (distRes (.ofGraph G) L.level t) →
      (distRes (.ofGraph G) L.level t).longcode < 2 ^ 62 → WFrame L m m' →
      (∀ x, x ∉ distTemps → x ∉ distSet → x ∉ args → x ≠ id.longcode → x ≠ id.nactive →
        PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F dist Q empty_env le m := by
  have hnl := hok.nlt
  have hbc := Hex.GraphIso.Nauty.bcount_le t.ptn L.level n
  have hnc : t.numcells ≤ 2 * n := by unfold Budget at hb; omega
  rw [dist_eq]
  wp_step
  refine wp_distTest hok hm hr ht hv hnc ?_
  intro v726 v727
  apply wp_if_eval
  simp only [Exec.evalExpr, temps_gss, typeof]
  cases hd : distCond L.level t
  · simp (config := {decide := true}) only [Val.of_bool, cop, ite_false]
    rw [show distRes (.ofGraph G) L.level t = t from if_neg (by simp only [hd]; decide)] at hQ
    apply wp_skip
    refine hQ L.b4 L.c4 _ m S (.inl ⟨rfl, rfl⟩) hok.c4 hm hr
      (((ht.set (x := idOf 726) v726 (by decide)).set (x := idOf 727) v727 (by decide)).set
        (x := idOf 728) _ (by decide)) hv hb hc (WFrame.refl L m) fun x _ hx' _ _ _ => ?_
    simp only [distSet, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx'
    rw [temps_gso _ _ hx'.2.2.2.1, temps_gso _ _ hx'.2.2.1, temps_gso _ _ hx'.2.1]
  · simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
    have hd' := hd
    simp only [distCond, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd'
    obtain ⟨⟨⟨hl2, hq1⟩, hp0⟩, hc8⟩ := hd'
    have hq0 := queue_lt hv (show 0 < t.queue.size by omega)
    have ht1 := ((ht.set (x := idOf 726) v726 (by decide)).set (x := idOf 727) v727 (by decide)).set
      (x := idOf 728) Vtrue (by decide)
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, ht1.nactive, typeof, cop, ir_sub, hq1]
    rw [show ((1 : Nat) : Int) - 1 = 0 from rfl]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    let s1 : RefineSt n := { t with queue := #[] }
    have ht2 := (ht1.set (x := idOf 715) (.Vint (ir 0)) (by decide)).setNactive s1 rfl
    apply wp_set_eval
    rw [eval_gw2 hok hm (c := 0) (by simp (config := {decide := true}) only [Exec.evalExpr, temps_gso,
      temps_gss]) rfl (by have := hok.c2; have := hok.n0; omega), hr.queue 0 (by omega)]
    dsimp only
    have ht3 := ht2.set (x := id.«isplit») (.Vint (ir t.queue[0]!)) (by decide)
    have hm1 : Mem m L G s1 S := hm.congr rfl rfl rfl rfl
    wp_step
    refine wp_delAct hok hm1 ht3 (c := t.queue[0]!) (by simp only [Exec.evalExpr, temps_gss]) rfl hq0 ?_
    intro m1 aw hm2 hf1
    let s0 := Hex.GraphIso.Nauty.Sparse.Refinement.distanceStart (.ofGraph G) t
    have hm3 : Mem m1 L G s0 { S with aw } := hm2.congr rfl rfl rfl rfl
    have hlq := perm_bound' hv hq0
    wp_step; wp_step; wp_step
    refine wp_call (vf := .Vptr Block.distvals Ptrofs.zero)
      (targs := [(tptr (Tstruct id.«_1406» noattr)), tint, (tptr tint), tint]) (tres := Tvoid)
      (cc := Common.AST.cc_default) (vargs := [.Vptr L.bsg L.sofs, .Vint (ir t.lab[t.queue[0]!]!),
        .Vptr L.b3 Ptrofs.zero, .Vint (ir n)]) _
      (distvalsSpec G L.bsg L.sofs L.bv L.vo L.bd L.dofs L.be L.eo t.lab[t.queue[0]!]! L.b3 Ptrofs.zero
        L.c4 L.b4) (distvals_satisfies _ _ _ _ _ _ _ _ _ _ _ _ _ _) rfl
      (by simp only [Exec.evalExpr, Exec.lvalOfVar,
        show PTree.get sparse.id.distvals (empty_env : env) = none from rfl,
        find_distvals, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
      ?_ (by simp [Common.Globalenvs.Genv.find_funct, funct_distvals]) type_distvals ?_ ?_
    · have ht4 : Tmp _ L s0 := ht3.congr rfl rfl
      have h2 := eval_lab hok hm3 ht4 (a := tv id.«isplit») (c := t.queue[0]!) (by simp only [Exec.evalExpr, temps_gss]) rfl hq0
      have h4 : Exec.evalExpr sge empty_env _ m1 (tv id.«n») = _ := ht4.n
      simp only [Exec.evalExprlist, h2, eval_w3 hok hm3, h4]
      simp [Exec.evalExpr, ht4.g, typeof, cop]
      rfl
    · have hbe1 : Mem.valid_block m1 L.be := hf1.valid _ hbe
      have hrv := hm3.rvalid hok hbe1
      have hwv := hm3.wvalid hok
      have gs := fun z hz => (hgs z hz)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at gs
      have h3w : L.b3 ∈ L.wblocks := by simp [Loc.wblocks]
      have h4w : L.b4 ∈ L.wblocks := by simp [Loc.wblocks]
      have h34 : L.b3 ≠ L.b4 := pw_ne hok.wdistinct 7 8 (by decide) (by simp [Loc.wblocks])
      refine ⟨rfl, hm3.graph, ⟨_, hm3.w3⟩, hlq, by omega, hm3.d4, ?_,
        hok.wr h3w (by simp [Loc.rblocks]), hok.wr h3w (by simp [Loc.rblocks]),
        hok.wr h3w (by simp [Loc.rblocks]), hok.wr h3w (by simp [Loc.rblocks])⟩
      rintro z (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨hrv _ (by simp [Loc.rblocks]), gs.1.1, gs.1.2,
          fun _ => (hok.wr h4w (by simp [Loc.rblocks])).symm⟩
      · exact ⟨hrv _ (by simp [Loc.rblocks]), gs.2.1.1, gs.2.1.2,
          fun _ => (hok.wr h4w (by simp [Loc.rblocks])).symm⟩
      · exact ⟨hrv _ (by simp [Loc.rblocks]), gs.2.2.1.1, gs.2.2.1.2,
          fun _ => (hok.wr h4w (by simp [Loc.rblocks])).symm⟩
      · exact ⟨hrv _ (by simp [Loc.rblocks]), gs.2.2.2.1, gs.2.2.2.2,
          fun _ => (hok.wr h4w (by simp [Loc.rblocks])).symm⟩
      · exact ⟨hwv _ h3w, by rw [w4_eq]; exact hok.wr h3w (by simp [Loc.rblocks]),
          by rw [w4s_eq]; exact hok.wr h3w (by simp [Loc.rblocks]), fun _ => h34⟩
    · rintro tr - m2 ⟨rfl, harr, hk3, c4', b4', hd4, hn4, hor, hu2, hg2⟩
      simp only [set_opttemp, E0_append]
      have hcq : 0 < c4' := by have := hok.n0; omega
      obtain ⟨w4v, hw4⟩ := Alloc.malloced_array (hd4.mal hcq) .Mint32 4 rfl rfl c4' (by omega)
      have hbe1 : Mem.valid_block m1 L.be := hf1.valid _ hbe
      let g := Graph.ofGraph G
      have hm4 := Mem.swap4 hok hm3 hgs hbe1 hu2 (fun z hz => by
          rcases hz with h | h | h | ⟨-, h⟩ | ⟨hnv, h⟩
          · exact .inl h
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr (.inl h)))
          · exact .inr (.inl h)
          · exact .inr (.inr (.inr (.inr (h ▸ hnv))))) hk3 hd4 hw4 harr
      have hok' := hok.with4 hm3 hbe1 hn4 hor
      have hor' : (c4' = L.c4 ∧ b4' = L.b4) ∨ ¬ Mem.valid_block m b4' :=
        hor.imp_right fun h hv => h (hf1.valid _ hv)
      have hdb := (Hex.GraphIso.Nauty.Sparse.distvals_correct G ⟨t.lab[t.queue[0]!]!, hlq⟩).bound
      have hr4 : Rep (L.with4 b4' c4') s0 { { S with aw } with
          w3 := Hex.GraphIso.Nauty.Sparse.distvals g t.lab[t.queue[0]!]!, w4 := w4v } :=
        { starts := hr.starts
          queue := fun i hi => absurd hi (by simp [s0, Hex.GraphIso.Nauty.Sparse.Refinement.distanceStart])
          w3size := Hex.GraphIso.Nauty.Sparse.distvals_size _ _
          w3small := fun i hi => Nat.lt_of_le_of_lt (hdb ⟨i, hi⟩) (by omega)
          ptnSmall := hr.ptnSmall }
      have hv0 : s0.Valid L.level := hv.distance_start G hq1
      wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr]
      have ht5 := ((ht3.congr (t' := s0) rfl rfl).with4 b4' c4').set (x := id.«v1») (.Vint (Lib.Integers.Int.repr (zOfInt 0))) (by decide)
      refine wp_distLoop hC hok' hv0 (fun v hv => hdb ⟨v, hv⟩) ⟨s0, _, n, DistanceState.initial hv0, hm4, hr4,
        fun v _ => rfl, ht5, hb, hc, Frame.refl _ _, by omega,
        (distance_eq L.level s0), by rw [temps_gss]; rfl, fun _ _ _ _ _ => rfl⟩ ?_
      intro le' m' S'' hm' hr' _ ht' hds hb' hc' hf' ho'
      have hcv : ∀ z ∈ L.cblocks, Mem.valid_block m z := fun z hz =>
        hm.wvalid hok z (by simp only [Loc.cblocks, List.mem_cons, List.mem_nil_iff, or_false] at hz
                            rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp [Loc.wblocks])
      have hcw : ∀ z ∈ L.cblocks, z ∈ L.wblocks := fun z hz => by
        simp only [Loc.cblocks, List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp [Loc.wblocks]
      have hc34 : ∀ z ∈ L.cblocks, z ≠ L.b3 ∧ z ≠ L.b4 := fun z hz => by
        have d := hok.wdistinct
        simp only [Loc.cblocks, List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact ⟨pw_ne d 0 7 (by decide) (by simp [Loc.wblocks]), pw_ne d 0 8 (by decide) (by simp [Loc.wblocks])⟩
        · exact ⟨pw_ne d 1 7 (by decide) (by simp [Loc.wblocks]), pw_ne d 1 8 (by decide) (by simp [Loc.wblocks])⟩
        · exact ⟨pw_ne d 2 7 (by decide) (by simp [Loc.wblocks]), pw_ne d 2 8 (by decide) (by simp [Loc.wblocks])⟩
        · exact ⟨pw_ne d 3 7 (by decide) (by simp [Loc.wblocks]), pw_ne d 3 8 (by decide) (by simp [Loc.wblocks])⟩
        · exact ⟨pw_ne d 4 7 (by decide) (by simp [Loc.wblocks]), pw_ne d 4 8 (by decide) (by simp [Loc.wblocks])⟩
      have W2 : WFrame L m1 m2 :=
        ⟨hu2.mono fun z hz => by
            rcases hz with h | h | h | ⟨-, h⟩ | ⟨hnv, h⟩
            · exact .inl (.inl (h ▸ by simp [Loc.writes, Loc.wblocks]))
            · exact .inl (.inr (h ▸ by simp [scrGlobals]; decide))
            · exact .inl (.inr (h ▸ by simp [scrGlobals]; decide))
            · exact .inl (.inl (h ▸ by simp [Loc.writes, Loc.wblocks]))
            · exact .inr (h ▸ hnv),
          fun z hz => Keep.unch hu2 (by
            rintro (h | h | h | ⟨-, h⟩ | ⟨hnv, h⟩)
            · exact (hc34 z hz).1 h
            · exact hok.wr (hcw z hz) (by simp [Loc.rblocks]) (h.trans w4_eq)
            · exact hok.wr (hcw z hz) (by simp [Loc.rblocks]) (h.trans w4s_eq)
            · exact (hc34 z hz).2 h
            · exact hnv (h ▸ hf1.valid _ (hcv z hz))),
          hg2⟩
      have W13 := ((hf1.wide hcv).trans W2 (fun z hz => .inl hz) rfl).trans
        (hf'.wide (fun z hz => hg2 _ (hf1.valid _ (hcv z hz)))) (Loc.with4_wide hor') rfl
      rw [show distRes (.ofGraph G) L.level t = Hex.GraphIso.Nauty.Sparse.Refinement.distance L.level s0
        from if_pos hd] at hQ
      refine hQ b4' c4' le' m' S'' hor' hn4 hm' hr' ht' hds.valid hb' hc' W13 fun x hx hx' h1 h2 h3 => ?_
      rw [ho' x hx h1 h2 h3]
      simp only [distSet, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx'
      have hv1 : x ≠ id.«v1» := by intro e; subst e; exact hx (by unfold distTemps cellTemps; decide)
      rw [temps_gso _ _ hv1, temps_gso _ _ hx'.2.2.2.2, temps_gso _ _ h3, temps_gso _ _ hx'.1,
        temps_gso _ _ hx'.2.2.2.1, temps_gso _ _ hx'.2.2.1, temps_gso _ _ hx'.2.1]

end NautyVerified.Proofs.Sparse.Refine

import NautyVerified.Proofs.Fmperm.Loop
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# `fmperm` meets its specification

`fmpermSpec`: called with a permutation `perm` of `0 .. n-1` and sets `fix`,
`mcr` of `M` words, nauty's `fmperm` leaves in `fix` and `mcr` words
representing HexGraphIso's `fmperm perm n`. Along the way `DYNALLOC1` may
replace nautil.c's `workperm` array (`DynAt`); nothing else changes.
-/

namespace NautyVerified.Proofs.Fmperm

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Spec
open NautyVerified.Proofs.Set (longs addW BitTable)
open NautyVerified.Proofs.Alloc (DynAt)
open Hex.GraphIso.Nauty (VSet)

/-- The blocks nautil.c's `workperm` pair occupies. -/
abbrev WP := Block.nautilWorkperm
abbrev WPS := Block.nautilWorkpermSz

/-- The specification of `fmperm`. -/
def fmpermSpec (bpm : block) (pofs : ptrofs) (bf : block) (fofs : ptrofs) (bm : block)
    (mofs : ptrofs) (perm : Array Nat) (n M : Nat) (wf wm : Nat → Lib.Integers.int64)
    (cap : Nat) (b0 : block) : FunSpec where
  pre args m := args = [.Vptr bpm pofs, .Vptr bf fofs, .Vptr bm mofs, .Vint (ir M), .Vint (ir n)] ∧
    ArrayAt m .Mint32 bpm (intOfZ (Ptrofs.unsigned pofs)) (ints perm) n ∧
    ArrayAt m .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf) M ∧
    ArrayAt m .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm) M ∧
    BitTable m Block.nautilBit ∧ DynAt m WP WPS 4 cap b0 ∧
    Mem.valid_block m bpm ∧ Mem.valid_block m bf ∧ Mem.valid_block m bm ∧
    Apart bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M ∧
    bf ≠ bpm ∧ bm ≠ bpm ∧
    (∀ z, z = WP ∨ z = WPS ∨ z = Block.nautilBit → z ≠ bpm ∧ z ≠ bf ∧ z ≠ bm) ∧
    (0 < cap → b0 ≠ bpm ∧ b0 ≠ bf ∧ b0 ≠ bm ∧ b0 ≠ Block.nautilBit) ∧
    perm.size = n ∧ (∀ x, x < n → perm[x]! < n) ∧
    (∀ x y, x < n → y < n → perm[x]! = perm[y]! → x = y) ∧
    n < 2147483648 ∧ 0 < M ∧ M < 2147483648 ∧ n ≤ 64 * M
  post _ m t _ m' := t = E0 ∧ ∃ wf' wm' cap' b',
    ArrayAt m' .Mint64 bf (intOfZ (Ptrofs.unsigned fofs)) (longs wf') M ∧
    ArrayAt m' .Mint64 bm (intOfZ (Ptrofs.unsigned mofs)) (longs wm') M ∧
    SetRep (fun w => bv64 (wf' w)) M (Hex.GraphIso.Nauty.fmperm perm n).1 ∧
    SetRep (fun w => bv64 (wm' w)) M (Hex.GraphIso.Nauty.fmperm perm n).2 ∧
    DynAt m' WP WPS 4 cap' b' ∧ n ≤ cap' ∧ ((cap' = cap ∧ b' = b0) ∨ ¬ Mem.valid_block m b') ∧
    Unch m m' (fun z => z = bf ∨ z = bm ∨ z = WPS ∨ z = WP ∨ (0 < cap ∧ z = b0) ∨
      (¬ Mem.valid_block m b' ∧ z = b')) ∧
    Rest m m' bf (intOfZ (Ptrofs.unsigned fofs)) bm (intOfZ (Ptrofs.unsigned mofs)) M ∧
    ∀ z ∈ [bf, bm], Alloc.Keep m m' z

/-- The temporaries on entry. -/
def entryTemps (bpm : block) (pofs : ptrofs) (bf : block) (fofs : ptrofs) (bm : block)
    (mofs : ptrofs) (n M : Nat) : temp_env :=
  PTree.set id.n (.Vint (ir n)) (PTree.set id.m (.Vint (ir M))
    (PTree.set id.mcr (.Vptr bm mofs) (PTree.set id.fix (.Vptr bf fofs)
      (PTree.set id.perm (.Vptr bpm pofs) (create_undef_temps Source.dense.fn.fmperm.fn_temps)))))

theorem fmperm_satisfies {xi : ExternalCalls} (bpm : block) (pofs : ptrofs) (bf : block)
    (fofs : ptrofs) (bm : block) (mofs : ptrofs) (perm : Array Nat) (n M : Nat)
    (wf wm : Nat → Lib.Integers.int64) (cap : Nat) (b0 : block) :
    Satisfies xi ge (.Internal Source.dense.fn.fmperm)
      (fmpermSpec bpm pofs bf fofs bm mofs perm n M wf wm cap b0) := by
  refine satisfies_internal (Entry := fun _ m₀ e le m =>
    e = empty_env ∧ le = entryTemps bpm pofs bf fofs bm mofs n M ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, entryTemps bpm pofs bf fofs bm mofs n M, m,
      ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hparr, hfarr, hmarr, hbit, hD, hvp, hvf, hvm, hfm, hfp, hmp, hglob, hb0,
      hps, hpl, hpi, hn, hM, hM2, hnM⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [Source.dense.fn.fmperm.fn_body_eq, body_eq]
    simp only [body]
    have hnil : ∀ i, PTree.get i (empty_env : env) = none := fun _ => rfl
    have hc4 : 4 * n < 2 ^ 62 := by omega
    wp_step
    refine Alloc.wp_dynalloc1 find_nautilWorkpermSz find_nautilWorkperm rfl hD
      (by simp (config := {decide := true}) only [entryTemps, temps_gss]) hn hc4 ?_
    intro le1 m1 cap' b' hD' hcap hu1 hb' _ ho1
    -- the caller's blocks are outside what `DYNALLOC1` changed
    have hout : ∀ z, Mem.valid_block m z → z ≠ WPS → z ≠ WP → ¬ (0 < cap ∧ z = b0) →
        ¬ (z = WPS ∨ z = WP ∨ (0 < cap ∧ z = b0) ∨ (¬ Mem.valid_block m b' ∧ z = b')) := by
      rintro z hv h1 h2 h3 (h | h | h | ⟨hb, rfl⟩)
      · exact h1 h
      · exact h2 h
      · exact h3 h
      · exact hb hv
    have hgWP := hglob WP (.inl rfl)
    have hgWPS := hglob WPS (.inr (.inl rfl))
    have hgBit := hglob Block.nautilBit (.inr (.inr rfl))
    have hbitv : Mem.valid_block m Block.nautilBit := by
      obtain h0 := hbit 0 (by decide)
      exact Alloc.valid_of_access (Mem.load_valid_access _ _ _ _ _ h0)
    have hbit_out := hout _ hbitv (by decide) (by decide) (fun ⟨h1, h2⟩ => (hb0 h1).2.2.2 h2.symm)
    have hbD : 0 < cap' → b' ≠ bpm ∧ b' ≠ bf ∧ b' ≠ bm ∧ b' ≠ Block.nautilBit := by
      intro hc0
      rcases hb' with ⟨hcc, rfl⟩ | hnv
      · exact hb0 (by omega)
      · exact ⟨fun h => hnv (h ▸ hvp), fun h => hnv (h ▸ hvf), fun h => hnv (h ▸ hvm),
          fun h => hnv (h ▸ hbitv)⟩
    have hparr1 := hparr.unch hu1 (hout _ hvp hgWPS.1.symm hgWP.1.symm (fun ⟨h1, h2⟩ => (hb0 h1).1 h2.symm))
    have hfarr1 := hfarr.unch hu1 (hout _ hvf hgWPS.2.1.symm hgWP.2.1.symm
      (fun ⟨h1, h2⟩ => (hb0 h1).2.1 h2.symm))
    have hmarr1 := hmarr.unch hu1 (hout _ hvm hgWPS.2.2.symm hgWP.2.2.symm
      (fun ⟨h1, h2⟩ => (hb0 h1).2.2.1 h2.symm))
    have hbit1 := hbit.unch hu1 hbit_out
    have hT1 : ∀ k, k ≠ Fmperm.id.t1 → k ≠ Fmperm.id.t2 →
        PTree.get k le1 = PTree.get k (entryTemps bpm pofs bf fofs bm mofs n M) := ho1
    wp_step
    refine Set.wp_emptySet' (vals := Set.longs wf) (by decide) (by decide) (by decide) hfarr1 hM hM2
      (by rw [hT1 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (by rw [hT1 _ (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]) ?_
    intro le2 m2 harr2 hu2 hO2 ho2
    have hT2 : ∀ k, k ≠ Fmperm.id.t1 → k ≠ Fmperm.id.t2 → k ≠ Fmperm.id.es → k ≠ Fmperm.id.t3 →
        PTree.get k le2 = PTree.get k (entryTemps bpm pofs bf fofs bm mofs n M) := fun k h1 h2 h3 h4 => by
      rw [ho2 k h3 h4, hT1 k h1 h2]
    wp_step
    refine Set.wp_emptySet' (vals := Set.longs wm) (by decide) (by decide) (by decide)
      (hmarr1.acrossF hu2 hO2 hfm) hM hM2
      (by rw [hT2 _ (by decide) (by decide) (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
      (by rw [hT2 _ (by decide) (by decide) (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss]) ?_
    intro le3 m3 harr3 hu3 hO3 ho3
    have hT3 : ∀ k, k ≠ Fmperm.id.t1 → k ≠ Fmperm.id.t2 → k ≠ Fmperm.id.es → k ≠ Fmperm.id.t3 →
        k ≠ Fmperm.id.es1 → k ≠ Fmperm.id.t4 →
        PTree.get k le3 = PTree.get k (entryTemps bpm pofs bf fofs bm mofs n M) :=
      fun k h1 h2 h3 h4 h5 h6 => by rw [ho3 k h5 h6, hT2 k h1 h2 h3 h4]
    have hp3 : 0 < n → Mem.load .Mint64 m3 WP (zOfInt 0) = some (.Vptr b' Ptrofs.zero) := fun hn0 => by
      rw [hu3.load _ _ _ hgWP.2.2, hu2.load _ _ _ hgWP.2.1]; exact hD'.ptr (by omega)
    have hw3 : ∃ vals, ArrayAt m3 .Mint32 b' 0 vals n := by
      by_cases hn0 : n = 0
      · subst hn0
        exact ⟨fun _ => .Vundef, ⟨Int.le_refl _, by decide, fun _ h => absurd h (by omega),
          fun _ h => absurd h (by omega)⟩⟩
      · obtain ⟨vals, hv⟩ := Alloc.malloced_array (hD'.mal (by omega)) .Mint32 4 rfl rfl n
          (Nat.mul_le_mul_left 4 hcap)
        have hb := hbD (by omega)
        exact ⟨vals, (hv.unch hu2 hb.2.1).unch hu3 hb.2.2.1⟩
    obtain ⟨vals, hw3⟩ := hw3
    wp_step
    refine wp_clearWp rfl hp3 hw3 hn (fun hn0 => (hD'.bne (by omega)).2.symm)
      (by rw [hT3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp (config := {decide := true}) only [entryTemps, temps_gss]) ?_
    intro le4 m4 harr4 hu4 hk4 ho4
    have hT4 : ∀ k, k ≠ Fmperm.id.t1 → k ≠ Fmperm.id.t2 → k ≠ Fmperm.id.es → k ≠ Fmperm.id.t3 →
        k ≠ Fmperm.id.es1 → k ≠ Fmperm.id.t4 → k ≠ Fmperm.id.i → k ≠ Fmperm.id.t5 →
        PTree.get k le4 = PTree.get k (entryTemps bpm pofs bf fofs bm mofs n M) :=
      fun k h1 h2 h3 h4 h5 h6 h7 h8 => by rw [ho4 k h7 h8, hT3 k h1 h2 h3 h4 h5 h6]
    have nb : ∀ z, (0 < cap' → b' ≠ z) → ¬ (0 < n ∧ z = b') := fun z hz ⟨h0, h⟩ =>
      hz (by omega) h.symm
    have hlk : ∀ k v, PTree.get k (entryTemps bpm pofs bf fofs bm mofs n M) = some v →
        k ≠ Fmperm.id.t1 → k ≠ Fmperm.id.t2 → k ≠ Fmperm.id.es → k ≠ Fmperm.id.t3 →
        k ≠ Fmperm.id.es1 → k ≠ Fmperm.id.t4 → k ≠ Fmperm.id.i → k ≠ Fmperm.id.t5 →
        PTree.get k le4 = some v := fun k v hv h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [hT4 k h1 h2 h3 h4 h5 h6 h7 h8]; exact hv
    have hf : Frame m4 le4 bpm pofs b' perm n :=
      { hperm := hlk _ _ (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hn := hlk _ _ (by simp (config := {decide := true}) only [entryTemps, temps_gss])
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        parr := ((hparr1.unch hu2 (Ne.symm hfp)).unch hu3 (Ne.symm hmp)).unch hu4
          (nb _ fun h => (hbD h).1)
        wpPtr := fun hn0 => by
          rw [hu4.load _ _ _ (nb _ fun h => (hD'.bne h).2)]; exact hp3 hn0
        psize := hps, psmall := hpl, pinj := hpi, nlt := hn
        bpm_b := fun h0 => ((hbD (by omega)).1).symm
        wp_b := fun h0 => (hD'.bne (by omega)).2.symm }
    have hs : St m4 le4 b' bf fofs bm mofs n M (fun _ => lr 0) (fun _ => lr 0)
        (VSet.empty, VSet.empty, Array.replicate n false) :=
      { hfix := hlk _ _ (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hmcr := hlk _ _ (by simp (config := {decide := true}) only [entryTemps, temps_gso, temps_gss])
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        farr := (harr2.acrossM hu3 hO3 hfm).unch hu4 (nb _ fun h => (hbD h).2.1)
        marr := harr3.unch hu4 (nb _ fun h => (hbD h).2.2.1)
        frep := Set.setRep_zero hnM
        mrep := Set.setRep_zero hnM
        warr := by rw [seenVals_replicate]; exact harr4
        ssize := by simp
        bit := ((hbit1.unch hu2 hgBit.2.1).unch hu3 hgBit.2.2).unch hu4 (nb _ fun h => (hbD h).2.2.2)
        Mlt := hM2, nM := hnM }
    have hd : Disj n bpm b' bf bm :=
      { fp := hfp, mp := hmp
        fb := fun h0 => ((hbD (by omega)).2.1).symm
        mb := fun h0 => ((hbD (by omega)).2.2.1).symm
        wf := hgWP.2.1, wm := hgWP.2.2, bitf := hgBit.2.1, bitm := hgBit.2.2
        bitb := fun h0 => ((hbD (by omega)).2.2.2).symm }
    refine wp_main (e := empty_env) hf hs hd hfm rfl rfl ?_
    intro le5 m5 wf5 wm5 hf5 hs5 hu5 hr5 hk5 ho5
    have hR := fmperm_eq perm n
    refine ⟨m5, Nextelement.free_empty m5, rfl, wf5, wm5, cap', b', hs5.farr, hs5.marr,
      by rw [hR]; exact hs5.frep, by rw [hR]; exact hs5.mrep, ?_, hcap, hb', ?_, ?_, ?_⟩
    · refine (((hD'.keep hu2 hgWP.2.1 hgWPS.2.1 fun hc0 => Alloc.Keep.unch hu2 (hbD hc0).2.1).keep
        hu3 hgWP.2.2 hgWPS.2.2 fun hc0 => Alloc.Keep.unch hu3 (hbD hc0).2.2.1).keep hu4
        (nb _ fun h => (hD'.bne h).2) (nb _ fun h => (hD'.bne h).1) fun _ => hk4).keep hu5 ?_ ?_
        fun _ => hk5 b'
      · rintro (⟨h0, h⟩ | h | h)
        · exact (hD'.bne (by omega)).2 h.symm
        · exact hgWP.2.1 h
        · exact hgWP.2.2 h
      · rintro (⟨h0, h⟩ | h | h)
        · exact (hD'.bne (by omega)).1 h.symm
        · exact hgWPS.2.1 h
        · exact hgWPS.2.2 h
    · have hbS : ∀ z, 0 < n ∧ z = b' → (z = bf ∨ z = bm ∨ z = WPS ∨ z = WP ∨ (0 < cap ∧ z = b0) ∨
          (¬ Mem.valid_block m b' ∧ z = b')) := by
        rintro z ⟨h0, rfl⟩
        rcases hb' with ⟨hcc, hbb⟩ | hnv
        · exact .inr (.inr (.inr (.inr (.inl ⟨by omega, hbb⟩))))
        · exact .inr (.inr (.inr (.inr (.inr ⟨hnv, rfl⟩))))
      refine (((hu1.mono fun z hz => ?_).trans (hu2.mono fun z hz => .inl hz)).trans
        (hu3.mono fun z hz => .inr (.inl hz))).trans ((hu4.mono fun z hz => hbS z hz).trans
          (hu5.mono fun z hz => ?_))
      · rcases hz with h | h | h | h
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr (.inl h))))
        · exact .inr (.inr (.inr (.inr (.inr h))))
      · rcases hz with h | h | h
        · exact hbS z h
        · exact .inl h
        · exact .inr (.inl h)
    · exact ((((Rest.unch hu1 (hout _ hvf hgWPS.2.1.symm hgWP.2.1.symm
        (fun ⟨h1, h2⟩ => (hb0 h1).2.1 h2.symm))).trans (Rest.fix hu2 hO2)).trans
        (Rest.mcr hu3 hO3)).trans (Rest.unch hu4 (nb _ fun h => (hbD h).2.1))).trans hr5
    · have kf1 : Alloc.Keep m m1 bf := Alloc.Keep.unch hu1 (hout _ hvf hgWPS.2.1.symm hgWP.2.1.symm
        (fun ⟨h1, h2⟩ => (hb0 h1).2.1 h2.symm))
      have km1 : Alloc.Keep m m1 bm := Alloc.Keep.unch hu1 (hout _ hvm hgWPS.2.2.symm hgWP.2.2.symm
        (fun ⟨h1, h2⟩ => (hb0 h1).2.2.1 h2.symm))
      have kA : Alloc.KeepA m1 m3 := (Alloc.KeepA.of_outside hu2 hO2 hfarr1.base_nonneg).trans
        (Alloc.KeepA.of_outside hu3 hO3 hmarr1.base_nonneg)
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact ((kf1.trans (kA _)).trans (Alloc.Keep.unch hu4 (nb _ fun h => (hbD h).2.1))).trans (hk5 _)
      · exact ((km1.trans (kA _)).trans (Alloc.Keep.unch hu4 (nb _ fun h => (hbD h).2.2.1))).trans
          (hk5 _)

end NautyVerified.Proofs.Fmperm

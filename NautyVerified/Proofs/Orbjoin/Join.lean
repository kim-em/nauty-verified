import NautyVerified.Proofs.Refine.Arr
import NautyVerified.Proofs.Orbjoin.Chase

/-!
# The first loop of `orbjoin`

`wp_joinStep`: one iteration of nauty's first `orbjoin` loop, for vertex `i`,
turns the `orbits` array from `o` into `join map n o i`, HexGraphIso's step.
-/

namespace NautyVerified.Proofs.Orbjoin

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open Hex.GraphIso.Nauty.Orbit

variable {xi : ExternalCalls}

/-- The state `orbjoin` works in: its pointer and length arguments in
temporaries, the `orbits` array (holding a descending forest `o`) and the
`map` array (holding `mp`) in different blocks. -/
structure Frame (m : mem) (le : temp_env) (bo : block) (ofs : ptrofs) (bm : block)
    (mofs : ptrofs) (o mp : Array Nat) (n : Nat) : Prop where
  horb : PTree.get id.orbits le = some (.Vptr bo ofs)
  hmap : PTree.get id.map le = some (.Vptr bm mofs)
  hn : PTree.get id.n le = some (.Vint (ir n))
  arr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n
  marr : ArrayAt m .Mint32 bm (intOfZ (Ptrofs.unsigned mofs)) (ints mp) n
  hne : bo ≠ bm
  nlt : n < 2147483648
  mlt : ∀ i < n, mp[i]! < n
  desc : Descending o n

/-- The arrays and pointer temporaries survive a change of other temporaries. -/
theorem Frame.temps {m : mem} {le le' : temp_env} {bo : block} {ofs : ptrofs} {bm : block}
    {mofs : ptrofs} {o mp : Array Nat} {n : Nat} (h : Frame m le bo ofs bm mofs o mp n)
    (hle : ∀ k, k = id.orbits ∨ k = id.map ∨ k = id.n → PTree.get k le' = PTree.get k le) :
    Frame m le' bo ofs bm mofs o mp n :=
  { h with
    horb := by rw [hle _ (.inl rfl)]; exact h.horb
    hmap := by rw [hle _ (.inr (.inl rfl))]; exact h.hmap
    hn := by rw [hle _ (.inr (.inr rfl))]; exact h.hn }

/-- One iteration of the first loop: `orbits` becomes `join map n o i`. -/
theorem wp_joinStep {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem}
    {bo : block} {ofs : ptrofs} {bm : block} {mofs : ptrofs} {o mp : Array Nat} {n : Nat}
    (h : Frame m le bo ofs bm mofs o mp n) {i : Nat} (hi : i < n)
    (hiv : PTree.get id.i le = some (.Vint (ir i)))
    (hQ : ∀ le' m', Frame m' le' bo ofs bm mofs (join mp n o i) mp n → Unch m m' (· = bo) →
      Alloc.KeepA m m' → PTree.get id.i le' = some (.Vint (ir i)) → Q.normal E0 e le' m') :
    Wp xi ge f joinStep Q e le m := by
  have hii : Exec.evalExpr ge e le m (tv id.i) = some (.Vint (ir i)) := hiv
  have hmi := eval_at h.marr h.nlt id.map h.hmap (tv id.i) i hi hii rfl
  have hmlt := h.mlt i hi
  have hnl := h.nlt
  simp only [joinStep, sk]
  wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, hmi, hii]
  simp only [ints, typeof, cop]
  rw [ir_eq (a := (mp[i]! : Int)) (b := i) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hfix : mp[i]! = i
  · rw [ite_eq_right (by simp [hfix])]
    apply wp_skip
    have : join mp n o i = o := by simp [join, hfix]
    exact hQ le m (by rw [this]; exact h) (Unch.refl _ _) (Alloc.KeepA.refl _) hiv
  · rw [ite_eq_left (by simp; omega)]
    have hoi := ints_lt h.desc hi
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_orb h.arr h.nlt h.horb (tv id.i) i hi hii rfl]
    simp only [ints, seqPost, Post.after, E0_append]
    wp_step
    refine wp_chase f id.j1 (by decide) h.arr h.nlt (by rw [temps_gso _ _ (by decide)]; exact h.horb)
      h.desc hoi (temps_gss _ _ _) ?_
    intro le1 hj1 hother1
    have h1 : Frame m le1 bo ofs bm mofs o mp n := h.temps fun k hk => by
      rw [hother1 k (by rcases hk with rfl | rfl | rfl <;> decide), temps_gso _ _ (by
        rcases hk with rfl | rfl | rfl <;> decide)]
    have hii1 : Exec.evalExpr ge e le1 m (tv id.i) = some (.Vint (ir i)) := by
      show PTree.get _ _ = _
      rw [hother1 _ (by decide), temps_gso _ _ (by decide)]; exact hiv
    have hmi1 := eval_at h1.marr h1.nlt id.map h1.hmap (tv id.i) i hi hii1 rfl
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_orb h1.arr h1.nlt h1.horb (mapAt (tv id.i)) mp[i]! hmlt hmi1 rfl]
    simp only [ints, seqPost, Post.after, E0_append]
    have hom := ints_lt h.desc hmlt
    wp_step
    refine wp_chase f id.j2 (by decide) h1.arr h1.nlt (by rw [temps_gso _ _ (by decide)]; exact h1.horb)
      h.desc hom (temps_gss _ _ _) ?_
    intro le2 hj2 hother2
    have h2 : Frame m le2 bo ofs bm mofs o mp n := h1.temps fun k hk => by
      rw [hother2 k (by rcases hk with rfl | rfl | rfl <;> decide), temps_gso _ _ (by
        rcases hk with rfl | rfl | rfl <;> decide)]
    have hiv2 : PTree.get id.i le2 = some (.Vint (ir i)) := by
      rw [hother2 _ (by decide), temps_gso _ _ (by decide)]; exact hii1
    have hj1' : PTree.get id.j1 le2 = some (.Vint (ir (chaseList o (List.range n) o[i]!))) := by
      rw [hother2 _ (by decide), temps_gso _ _ (by decide)]; exact hj1
    have hjoin : join mp n o i =
        if chaseList o (List.range n) o[i]! < chaseList o (List.range n) o[mp[i]!]! then
          o.set! (chaseList o (List.range n) o[mp[i]!]!) (chaseList o (List.range n) o[i]!)
        else if chaseList o (List.range n) o[i]! > chaseList o (List.range n) o[mp[i]!]! then
          o.set! (chaseList o (List.range n) o[i]!) (chaseList o (List.range n) o[mp[i]!]!)
        else o := by
      simp only [join]
      rw [if_pos (by simpa using hfix)]
    have halt := chase_lt h.desc hoi
    have hblt := chase_lt h.desc hom
    generalize chaseList o (List.range n) o[i]! = a at hj1' hjoin halt
    generalize chaseList o (List.range n) o[mp[i]!]! = b at hj2 hjoin hblt
    have hja : Exec.evalExpr ge e le2 m (tv id.j1) = some (.Vint (ir a)) := hj1'
    have hjb : Exec.evalExpr ge e le2 m (tv id.j2) = some (.Vint (ir b)) := hj2
    have hsz : o.size = n := h.desc.1
    simp only [seqPost, Post.after, E0_append, link, sk]
    wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, hja, hjb]
    simp only [typeof, cop]
    rw [ir_lt (a := a) (b := b) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hab : a < b
    · rw [ite_eq_left (by simpa using hab)]
      wp_step; wp_step
      refine Refine.wp_storeV h2.arr h2.nlt id.orbits h2.horb (tv id.j2) b hblt hjb rfl (tv id.j1) a hja rfl ?_
      intro m' harr' hu hk
      apply hQ le2 m' _ hu hk hiv2
      rw [hjoin, if_pos hab]
      exact { h2 with
        arr := by rw [ints_set (by omega)]; exact harr'
        marr := h2.marr.unch hu h.hne.symm
        desc := h.desc.set hblt (by omega) }
    · rw [ite_eq_right (by simpa using hab)]
      wp_step; wp_step
      apply wp_if_eval
      rw [Exec.evalExpr, hja, hjb]
      simp only [typeof, cop]
      rw [ir_lt (a := b) (b := a) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      by_cases hba : b < a
      · rw [ite_eq_left (by simpa using hba)]
        wp_step; wp_step
        refine Refine.wp_storeV h2.arr h2.nlt id.orbits h2.horb (tv id.j1) a halt hja rfl (tv id.j2) b hjb rfl ?_
        intro m' harr' hu hk
        apply hQ le2 m' _ hu hk hiv2
        rw [hjoin, if_neg hab, if_pos hba]
        exact { h2 with
          arr := by rw [ints_set (by omega)]; exact harr'
          marr := h2.marr.unch hu h.hne.symm
          desc := h.desc.set halt (by omega) }
      · rw [ite_eq_right (by simpa using hba)]
        apply wp_skip
        apply hQ le2 m _ (Unch.refl _ _) (Alloc.KeepA.refl _) hiv2
        rw [hjoin, if_neg hab, if_neg hba]
        exact h2

end NautyVerified.Proofs.Orbjoin

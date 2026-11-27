import NautyVerified.Proofs.Harness.PartMain
import NautyVerified.Proofs.Harness.Graph

/-!
# The input phase of `main`

`wp_tInput`: with the reads returning the colours `cs`, the edge count and
the edges `es`, the input loops leave `cs` in `colour` (their maximum in
`maxc`) and the adjacency words of `es` in `g`.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk longs)

/-- The temporaries the input phase sets. -/
abbrev InputTemp (x : ident) : Prop :=
  x ≠ dense.id.i ∧ x ≠ dense.id.maxc ∧ x ≠ idOf 710 ∧ x ≠ idOf 711 ∧ x ≠ dense.id.ne ∧
    x ≠ dense.id.es_ ∧ x ≠ idOf 712 ∧ x ≠ dense.id.a ∧ x ≠ dense.id.b ∧ x ≠ idOf 713 ∧ x ≠ idOf 714

theorem wp_tInput {Q : Post} {e : env} {le : temp_env} {m : mem} {bcol bg : block} {Mw N : Nat}
    (cs : List Nat) (hlen : cs.length = N) (hcs : ∀ j < N, cs[j]! < 2147483648)
    (es : List (Fin N × Fin N)) (hne : es.length < 2147483648)
    (hN0 : 0 < N) (hN : N < 2147483648) (hMN : Mw * N < 2147483648) (hNM : N ≤ 64 * Mw)
    (hMw : Mw < 2147483648)
    (her : PTree.get dense.id.nv_read e = none)
    (heb : PTree.get dense.id.«dense_main:bit» e = none) (heg : PTree.get dense.id.g e = none)
    (hcol : PTree.get dense.id.colour le = some (.Vptr bcol Ptrofs.zero))
    (hg : PTree.get dense.id.g le = some (.Vptr bg Ptrofs.zero))
    (hn : PTree.get dense.id.n le = some (.Vint (ir N)))
    (hm : PTree.get dense.id.m le = some (.Vint (ir Mw)))
    (hcz : ArrayAt m .Mint32 bcol 0 (fun _ => .Vint (ir 0)) N)
    (hgz : ArrayAt m .Mint64 bg 0 (fun _ => .Vlong (lr 0)) (Mw * N))
    (hbit : Set.BitTable m Block.denseMainBit) (hb1 : bg ≠ Block.denseMainBit)
    (hb2 : bcol ≠ Block.denseMainBit) (hb3 : bcol ≠ bg)
    (hQ : ∀ t le' m', Reads t (cs.map (fun c : Nat => (c : Int)) ++ [(es.length : Int)] ++
        edgeIns es es.length) →
      ArrayAt m' .Mint32 bcol 0 (ints (prefixArr cs N N)) N →
      ArrayAt m' .Mint64 bg 0 (longs (edgeWords Mw es es.length)) (Mw * N) →
      Unch m m' (fun z => z = bcol ∨ z = bg) →
      PTree.get dense.id.maxc le' = some (.Vint (ir (maxPrefix cs N))) →
      (∀ x, InputTemp x → PTree.get x le' = PTree.get x le) →
      Wp Statement.xi ge dense.fn.main tPart (Q.after t) e le' m') :
    Wp Statement.xi ge dense.fn.main tInput Q e le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  apply wp_seq
  refine wp_colours cs hlen hN hcs her (by rw [temps_gso _ _ (by decide)]; exact hcol)
    (by rw [temps_gso _ _ (by decide)]; exact hn) (temps_gss _ _ _)
    (hcz.congr (ints_prefixArr_zero cs N)) fun t1 le1 m1 hr1 ha1 hu1 hmx1 ho1 => ?_
  simp only [seqPost, Post.after]
  have hle1 : ∀ x, x ≠ dense.id.i → x ≠ dense.id.maxc → x ≠ idOf 710 →
      PTree.get x le1 = PTree.get x le := fun x h1 h2 h3 => by rw [ho1 x h1 h2 h3, temps_gso _ _ h2]
  apply wp_seq; apply wp_seq; apply wp_seq; apply wp_skip
  simp only [seqPost, Post.after, E0_append]
  refine wp_rd (idOf 711) (lr (es.length : Int)) her ?_
  apply wp_set_eval
  rw [show Exec.evalExpr ge e (PTree.set (idOf 711) (.Vlong (lr (es.length : Int))) le1) m1
      (.Ecast (.Etempvar (idOf 711) tlong) tint) = some (.Vint (ir (es.length : Int))) by
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    rw [Refine.repr_unsigned_lr hne]]
  have hz0 : intOfZ (Ptrofs.unsigned Ptrofs.zero) = 0 := rfl
  have hnb1 : ¬ (bg = bcol) := fun h => hb3 h.symm
  let le2 := PTree.set dense.id.ne (.Vint (ir (es.length : Int)))
    (PTree.set (idOf 711) (.Vlong (lr (es.length : Int))) le1)
  have hle2 : ∀ x, x ≠ dense.id.i → x ≠ dense.id.maxc → x ≠ idOf 710 → x ≠ idOf 711 →
      x ≠ dense.id.ne → PTree.get x le2 = PTree.get x le := fun x h1 h2 h3 h4 h5 => by
    simp only [le2]; rw [temps_gso _ _ h5, temps_gso _ _ h4, hle1 x h1 h2 h3]
  apply wp_seq
  refine wp_emptyG (Mw := Mw) (N := N) (hz0 ▸ hgz.unch hu1 hnb1) (by
      have : 0 < Mw := by omega
      exact Nat.mul_pos this hN0) hMN hMw hN
    (by rw [hle2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg)
    (by rw [hle2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm)
    (by rw [hle2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hn)
    fun le3 m3 ha3 hu3 _ ho3 => ?_
  simp only [seqPost, Post.after, E0_append]
  rw [hz0] at ha3
  have hbit3 : Set.BitTable m3 Block.denseMainBit :=
    ((hbit.unch hu1 hb2.symm).unch hu3 hb1.symm)
  apply wp_seq
  refine wp_edges es hne hMN hNM ha3
    (by rw [ho3 _ (by decide) (by decide), hle2 _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hg)
    (by rw [ho3 _ (by decide) (by decide), hle2 _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hm)
    (by rw [ho3 _ (by decide) (by decide)]; exact temps_gss _ _ _)
    hbit3 heb heg her hb1 fun t4 le4 m4 hr4 ha4 hu4 ho4 => ?_
  simp only [seqPost, Post.after]
  have hrd : Reads (tr1 (readEv (lr (es.length : Int)))) [(es.length : Int)] := by
    have := Reads.one (lr (es.length : Int))
    rwa [signed_lr (by omega) (by omega)] at this
  have h := hQ (t1 ++ (tr1 (readEv (lr (es.length : Int))) ++ t4)) le4 m4
    ((hr1.append hrd).append hr4 |> fun h => by rwa [trace_append_assoc] at h)
    (ha1.unch (hu3.trans hu4) hb3)
    ha4
    (hu1.mono (fun z hz => .inl hz) |>.trans ((hu3.trans hu4).mono fun z hz => .inr hz))
    (by rw [ho4 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      ho3 _ (by decide) (by decide), temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hmx1)
    (fun x ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ => by
      rw [ho4 x h1 h8 h9 h10 h11, ho3 x h6 h7, temps_gso _ _ h5, temps_gso _ _ h4, ho1 x h1 h2 h3,
        temps_gso _ _ h2])
  simp only [Post.after, trace_append_assoc, append_E0] at h ⊢
  exact h

end NautyVerified.Proofs.Harness

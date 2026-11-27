import NautyVerified.Proofs.Harness.Part

/-!
# The harness's partition loops

`wp_cells`: `cellLoop` lists the vertices colour by colour into `lab` and
puts 1 in the matching `ptn` entries; `wp_ends`: `endLoop` puts 0 at each
cell end.
-/

namespace NautyVerified.Proofs.Harness

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Set (sk)

theorem prefixArr_snoc {L : List Nat} {N : Nat} (j : Nat) {x : Nat} (hx : x < N) :
    upd (ints (prefixArr L N L.length)) L.length (.Vint (ir (j : Int))) x =
      ints (prefixArr (L ++ [j]) N (L.length + 1)) x := by
  simp only [upd, ints]
  split
  · rename_i h; subst h
    rw [prefixArr_get hx]; simp
  · rename_i h
    rw [prefixArr_get hx, prefixArr_get hx]
    by_cases hxl : x < L.length
    · rw [if_pos hxl, if_pos (by omega), getElem!_append, if_pos hxl]
    · rw [if_neg hxl, if_neg (by omega)]

theorem prefixArr_one {N k x : Nat} (hx : x < N) (hk : k < N) :
    upd (ints (prefixArr (List.replicate N 1) N k)) k (.Vint (ir 1)) x =
      ints (prefixArr (List.replicate N 1) N (k + 1)) x := by
  simp only [upd, ints]
  split
  · rename_i h; subst h
    rw [prefixArr_get hx]; simp [hx]
  · rename_i h
    rw [prefixArr_get hx, prefixArr_get hx]
    by_cases hxk : x < k
    · rw [if_pos hxk, if_pos (by omega)]
    · rw [if_neg hxk, if_neg (by omega)]

theorem listed_succ (key : Nat → Nat) (n c j : Nat) :
    listed key n c (j + 1) = listed key n c j ++ (if key j = c then [j] else []) := by
  simp only [listed, List.range_succ, List.filter_append, List.append_assoc]
  congr 2
  by_cases h : key j = c <;> simp [h]

theorem listed_next (key : Nat → Nat) (n c : Nat) :
    listed key n c n = listed key n (c + 1) 0 := by
  simp [listed, List.range_succ, List.flatMap_append, clsOf]

/-- The inner body of `cellLoop`. -/
abbrev cellInner : statement :=
  sk (.Sifthenelse (.Ebinop .Oeq (ix dense.id.colour (tv dense.id.j)) (tv dense.id.c) tint)
    (.Ssequence (sk (.Sassign (ix dense.id.lab (tv dense.id.pos)) (tv dense.id.j)))
      (.Ssequence (sk (.Sassign (ix dense.id.ptn (tv dense.id.pos)) (ci 1 tint)))
        (sk (.Sset dense.id.pos (.Ebinop .Oadd (tv dense.id.pos) (ci 1 tint) tint)))))
    .Sskip)

theorem cellLoop_eq :
    .Ssequence (sk (.Sset dense.id.c (ci 0 tint))) cellLoop =
      forLe dense.id.c (tv dense.id.maxc) (forT dense.id.j (tv dense.id.n) cellInner) := rfl

/-- The arrays after `L` has been listed. -/
structure Listed (m : mem) (bl bp : block) (N : Nat) (L : List Nat) : Prop where
  lab : ArrayAt m .Mint32 bl 0 (ints (prefixArr L N L.length)) N
  ptn : ArrayAt m .Mint32 bp 0 (ints (prefixArr (List.replicate N 1) N L.length)) N

theorem wp_cellInner {Q : Post} {e : env} {le : temp_env} {m : mem} {bcol bl bp : block}
    {N : Nat} (key : Nat → Nat) (cs : List Nat) (hcs : ∀ v < N, cs[v]! = key v)
    (hkey : ∀ v < N, key v < 2147483648) (hN : N < 2147483648) (c j : Nat) (hj : j < N)
    (hcol : PTree.get dense.id.colour le = some (.Vptr bcol Ptrofs.zero))
    (hlab : PTree.get dense.id.lab le = some (.Vptr bl Ptrofs.zero))
    (hptn : PTree.get dense.id.ptn le = some (.Vptr bp Ptrofs.zero))
    (hjv : PTree.get dense.id.j le = some (.Vint (ir j)))
    (hcv : PTree.get dense.id.c le = some (.Vint (ir c))) (hc : c < 2147483648)
    (hpos : PTree.get dense.id.pos le = some (.Vint (ir (listed key N c j).length)))
    (hcarr : ArrayAt m .Mint32 bcol 0 (ints (prefixArr cs N N)) N)
    (hL : Listed m bl bp N (listed key N c j)) (hb1 : bl ≠ bcol) (hb2 : bp ≠ bcol) (hb3 : bl ≠ bp)
    (hQ : ∀ le' m', Listed m' bl bp N (listed key N c (j + 1)) → Unch m m' (fun z => z = bl ∨ z = bp) →
      PTree.get dense.id.pos le' = some (.Vint (ir (listed key N c (j + 1)).length)) →
      (∀ x, x ≠ dense.id.pos → PTree.get x le' = PTree.get x le) → Q.normal E0 e le' m') :
    Wp Statement.xi ge dense.fn.main cellInner Q e le m := by
  have hlen := length_listed_le key (c := c) (show j + 1 ≤ N by omega)
  have hkj := hkey j hj
  have hcj : Exec.evalExpr ge e le m (ix dense.id.colour (tv dense.id.j)) = some (.Vint (ir (key j))) := by
    rw [eval_at hcarr hN dense.id.colour hcol (tv dense.id.j) j hj hjv rfl]
    simp [ints, prefixArr_get hj, hcs j hj, hj]
  wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, hcj, show Exec.evalExpr ge e le m (tv dense.id.c) = _ from hcv]
  simp only [typeof, cop]
  rw [ir_eq (a := (key j : Int)) (b := (c : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hk : key j = c
  · rw [ite_eq_left (by simp [hk])]
    have hls := listed_succ key N c j
    rw [ite_eq_left hk] at hls
    rw [hls] at hlen
    simp only [List.length_append, List.length_singleton] at hlen
    wp_step; wp_step; wp_step
    refine Logic.wp_store hL.lab hN dense.id.lab hlab (tv dense.id.pos) _ (by omega) hpos rfl
      (tv dense.id.j) j hjv rfl ?_
    intro m1 hl1 hu1
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step; wp_step
    refine Logic.wp_store (hL.ptn.unch hu1 (Ne.symm hb3)) hN dense.id.ptn hptn (tv dense.id.pos) _
      (by omega) hpos rfl (ci 1 tint) 1 rfl rfl ?_
    intro m2 hp2 hu2
    simp only [seqPost, Post.after, E0_append]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hpos, typeof, cop, ir_add]
    refine hQ _ m2 ⟨?_, ?_⟩ ((hu1.mono fun z hz => .inl hz).trans (hu2.mono fun z hz => .inr hz))
      ?_ fun x hx => temps_gso _ _ hx
    · rw [hls]
      exact ((hl1.unch hu2 hb3).congr fun x hx => prefixArr_snoc j hx).congr fun x hx => by
        simp [List.length_append]
    · rw [hls]
      exact hp2.congr fun x hx => by
        rw [prefixArr_one hx (by omega)]; simp [List.length_append]
    · rw [temps_gss, hls]; simp [List.length_append]
  · rw [ite_eq_right (by simp; omega)]
    apply wp_skip
    have hls := listed_succ key N c j
    rw [ite_eq_right hk, List.append_nil] at hls
    refine hQ le m (by rw [hls]; exact hL) (Unch.refl _ _) (by rw [hls]; exact hpos)
      fun _ _ => rfl

theorem wp_cells {Q : Post} {e : env} {le : temp_env} {m : mem} {bcol bl bp : block}
    {N K : Nat} (key : Nat → Nat) (cs : List Nat) (hcs : ∀ v < N, cs[v]! = key v)
    (hkey : ∀ v < N, key v < 2147483648) (hN : N < 2147483648) (hK : K < 2147483648) (hK0 : 0 < K)
    (hcol : PTree.get dense.id.colour le = some (.Vptr bcol Ptrofs.zero))
    (hlab : PTree.get dense.id.lab le = some (.Vptr bl Ptrofs.zero))
    (hptn : PTree.get dense.id.ptn le = some (.Vptr bp Ptrofs.zero))
    (hn : PTree.get dense.id.n le = some (.Vint (ir N)))
    (hmaxc : PTree.get dense.id.maxc le = some (.Vint (ir ((K - 1 : Nat) : Int))))
    (hpos : PTree.get dense.id.pos le = some (.Vint (ir 0)))
    (hcarr : ArrayAt m .Mint32 bcol 0 (ints (prefixArr cs N N)) N)
    (hL : Listed m bl bp N []) (hb1 : bl ≠ bcol) (hb2 : bp ≠ bcol) (hb3 : bl ≠ bp)
    (hQ : ∀ le' m', Listed m' bl bp N (listed key N K 0) → Unch m m' (fun z => z = bl ∨ z = bp) →
      PTree.get dense.id.pos le' = some (.Vint (ir (listed key N K 0).length)) →
      (∀ x, x ≠ dense.id.c → x ≠ dense.id.j → x ≠ dense.id.pos → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp Statement.xi ge dense.fn.main
      (forLe dense.id.c (tv dense.id.maxc) (forT dense.id.j (tv dense.id.n) cellInner)) Q e le m := by
  let Oth := fun (le' : temp_env) => ∀ x, x ≠ dense.id.c → x ≠ dense.id.j → x ≠ dense.id.pos →
    PTree.get x le' = PTree.get x le
  let Inv := fun (c : Nat) (t : trace) (le' : temp_env) (m' : mem) =>
    t = E0 ∧ c ≤ K ∧ PTree.get dense.id.c le' = some (.Vint (ir c)) ∧
    Listed m' bl bp N (listed key N c 0) ∧
    PTree.get dense.id.pos le' = some (.Vint (ir (listed key N c 0).length)) ∧
    Unch m m' (fun z => z = bl ∨ z = bp) ∧ Oth le'
  refine wp_forLe (Inv := Inv) dense.id.c (tv dense.id.maxc) _ K hK hK0 ?_ ?_ ?_ ?_
  · rintro c t le' m' ⟨-, hc, hcv, -, -, -, ho⟩
    refine ⟨hc, hcv, ?_, rfl⟩
    show PTree.get _ _ = _
    rw [ho _ (by decide) (by decide) (by decide)]; exact hmaxc
  · refine ⟨rfl, Nat.zero_le _, temps_gss _ _ _, by simpa [listed] using hL, ?_, Unch.refl _ _,
      fun x h1 _ _ => temps_gso _ _ h1⟩
    rw [temps_gso _ _ (by decide)]; simpa [listed] using hpos
  · rintro c t le' m' hc ⟨rfl, -, hcv, hL', hpos', hu, ho⟩
    have get' : ∀ x, x ≠ dense.id.c → x ≠ dense.id.j → x ≠ dense.id.pos →
        PTree.get x le' = PTree.get x le := ho
    let Inv' := fun (j : Nat) (t : trace) (le'' : temp_env) (m'' : mem) =>
      t = E0 ∧ j ≤ N ∧ PTree.get dense.id.j le'' = some (.Vint (ir j)) ∧
      Listed m'' bl bp N (listed key N c j) ∧
      PTree.get dense.id.pos le'' = some (.Vint (ir (listed key N c j).length)) ∧
      Unch m m'' (fun z => z = bl ∨ z = bp) ∧
      ∀ x, x ≠ dense.id.j → x ≠ dense.id.pos → PTree.get x le'' = PTree.get x le'
    refine wp_forT (Inv := Inv') dense.id.j (tv dense.id.n) cellInner N hN ?_ ?_ ?_ ?_
    · rintro j t le'' m'' ⟨-, hj, hjv, -, -, -, ho'⟩
      refine ⟨hj, hjv, ?_, rfl⟩
      show PTree.get _ _ = _
      rw [ho' _ (by decide) (by decide), get' _ (by decide) (by decide) (by decide)]; exact hn
    · exact ⟨rfl, Nat.zero_le _, temps_gss _ _ _, hL', by rw [temps_gso _ _ (by decide)]; exact hpos',
        hu, fun x h1 _ => temps_gso _ _ h1⟩
    · rintro j t le'' m'' hj ⟨rfl, -, hjv, hL'', hpos'', hu', ho'⟩
      have g2 : ∀ x, x ≠ dense.id.c → x ≠ dense.id.j → x ≠ dense.id.pos →
          PTree.get x le'' = PTree.get x le := fun x h1 h2 h3 => by rw [ho' x h2 h3, get' x h1 h2 h3]
      refine wp_cellInner key cs hcs hkey hN c j hj (by rw [g2 _ (by decide) (by decide) (by decide)]; exact hcol)
        (by rw [g2 _ (by decide) (by decide) (by decide)]; exact hlab)
        (by rw [g2 _ (by decide) (by decide) (by decide)]; exact hptn) hjv
        (by rw [ho' _ (by decide) (by decide)]; exact hcv) (by omega) hpos''
        (hcarr.unch hu' (by rintro (h | h); exact hb1 h.symm; exact hb2 h.symm)) hL'' hb1 hb2 hb3 ?_
      intro le3 m3 hL3 hu3 hpos3 ho3
      refine ⟨by rw [ho3 _ (by decide)]; exact hjv, rfl, by omega, temps_gss _ _ _, hL3, ?_,
        hu'.trans hu3, fun x h1 h2 => ?_⟩
      · rw [temps_gso _ _ (by decide)]; exact hpos3
      · rw [temps_gso _ _ h1, ho3 x h2, ho' x h1 h2]
    · rintro t le'' m'' ⟨rfl, -, -, hL'', hpos'', hu', ho'⟩
      refine ⟨by rw [ho' _ (by decide) (by decide)]; exact hcv, rfl, by omega, temps_gss _ _ _, ?_, ?_,
        hu', fun x h1 h2 h3 => ?_⟩
      · rw [← listed_next]; exact hL''
      · rw [temps_gso _ _ (by decide), ← listed_next]; exact hpos''
      · rw [temps_gso _ _ h1, ho' x h2 h3, get' x h1 h2 h3]
  · rintro t le' m' ⟨rfl, -, -, hL', hpos', hu, ho⟩
    exact hQ le' m' hL' hu hpos' ho

/-- The body of `endLoop`. -/
abbrev endBody : statement :=
  .Ssequence
    (sk (.Sifthenelse (.Ebinop .Oeq (tv dense.id.i) (.Ebinop .Osub (tv dense.id.n) (ci 1 tint) tint) tint)
      (.Sset (idOf 715) (ci 1 tint))
      (sk (.Sset (idOf 715) (.Ecast (.Ebinop .One (ix dense.id.colour (ix dense.id.lab (tv dense.id.i)))
        (ix dense.id.colour (ix dense.id.lab (.Ebinop .Oadd (tv dense.id.i) (ci 1 tint) tint))) tint)
        tbool)))))
    (.Sifthenelse (tv (idOf 715)) (sk (.Sassign (ix dense.id.ptn (tv dense.id.i)) (ci 0 tint))) .Sskip)

theorem endLoop_eq :
    .Ssequence (sk (.Sset dense.id.i (ci 0 tint))) endLoop = forT dense.id.i (tv dense.id.n) endBody :=
  rfl

/-- `ptn` after the end marks below `i`. -/
def endPtn (key : Nat → Nat) (L : List Nat) (N i : Nat) : Array Nat :=
  Array.ofFn (n := N) fun x =>
    if x.val < i ∧ (x.val + 1 = N ∨ key L[x.val]! ≠ key L[x.val + 1]!) then 0 else 1

theorem listed_lt (key : Nat → Nat) {n c j : Nat} (hj : j ≤ n) :
    ∀ x ∈ listed key n c j, x < n := by
  intro x hx
  simp only [listed, List.mem_append, List.mem_flatMap, clsOf, List.mem_filter, List.mem_range] at hx
  rcases hx with ⟨_, _, h, _⟩ | ⟨h, _⟩ <;> omega

theorem endPtn_get {key : Nat → Nat} {L : List Nat} {N i x : Nat} (hx : x < N) :
    (endPtn key L N i)[x]! =
      if x < i ∧ (x + 1 = N ∨ key L[x]! ≠ key L[x + 1]!) then 0 else 1 := by
  simp [endPtn, hx]

theorem endPtn_mark {key : Nat → Nat} {L : List Nat} {N i : Nat}
    (h : i + 1 = N ∨ key L[i]! ≠ key L[i + 1]!) {x : Nat} (hx : x < N) :
    upd (ints (endPtn key L N i)) i (.Vint (ir 0)) x = ints (endPtn key L N (i + 1)) x := by
  simp only [upd, ints]
  split
  · rename_i hxi; subst hxi
    rw [endPtn_get hx, if_pos ⟨by omega, h⟩]; rfl
  · rename_i hxi
    rw [endPtn_get hx, endPtn_get hx]
    by_cases hxi' : x < i
    · simp [hxi', show x < i + 1 by omega]
    · simp [hxi', show ¬ x < i + 1 by omega]

theorem endPtn_keep {key : Nat → Nat} {L : List Nat} {N i : Nat}
    (h : ¬ (i + 1 = N ∨ key L[i]! ≠ key L[i + 1]!)) {x : Nat} (hx : x < N) :
    ints (endPtn key L N i) x = ints (endPtn key L N (i + 1)) x := by
  simp only [ints]
  rw [endPtn_get hx, endPtn_get hx]
  by_cases hxi : x = i
  · subst hxi; simp only [h, and_false, ite_false, show ¬ x < x by omega, false_and]
  · by_cases hxi' : x < i
    · simp [hxi', show x < i + 1 by omega]
    · simp [hxi', show ¬ x < i + 1 by omega]

theorem wp_ends {Q : Post} {e : env} {le : temp_env} {m : mem} {bcol bl bp : block}
    {N : Nat} (key : Nat → Nat) (cs : List Nat) (hcs : ∀ v < N, cs[v]! = key v)
    (hkey : ∀ v < N, key v < 2147483648) (hN0 : 0 < N) (hN : N < 2147483648)
    (L : List Nat) (hLs : ∀ x ∈ L, x < N) (hLlen : L.length = N)
    (hcol : PTree.get dense.id.colour le = some (.Vptr bcol Ptrofs.zero))
    (hlab : PTree.get dense.id.lab le = some (.Vptr bl Ptrofs.zero))
    (hptn : PTree.get dense.id.ptn le = some (.Vptr bp Ptrofs.zero))
    (hn : PTree.get dense.id.n le = some (.Vint (ir N)))
    (hcarr : ArrayAt m .Mint32 bcol 0 (ints (prefixArr cs N N)) N)
    (hlarr : ArrayAt m .Mint32 bl 0 (ints (prefixArr L N N)) N)
    (hparr : ArrayAt m .Mint32 bp 0 (ints (endPtn key L N 0)) N)
    (hb1 : bp ≠ bcol) (hb2 : bp ≠ bl)
    (hQ : ∀ le' m', ArrayAt m' .Mint32 bp 0 (ints (endPtn key L N N)) N → Unch m m' (· = bp) →
      (∀ x, x ≠ dense.id.i → x ≠ idOf 715 → PTree.get x le' = PTree.get x le) →
      Q.normal E0 e le' m') :
    Wp Statement.xi ge dense.fn.main (forT dense.id.i (tv dense.id.n) endBody) Q e le m := by
  let Inv := fun (i : Nat) (t : trace) (le' : temp_env) (m' : mem) =>
    t = E0 ∧ i ≤ N ∧ PTree.get dense.id.i le' = some (.Vint (ir i)) ∧
    ArrayAt m' .Mint32 bp 0 (ints (endPtn key L N i)) N ∧ Unch m m' (· = bp) ∧
    ∀ x, x ≠ dense.id.i → x ≠ idOf 715 → PTree.get x le' = PTree.get x le
  have hLx : ∀ x < N, L[x]! < N := fun x hx => hLs _ (by
    rw [getElem!_pos L x (by omega)]; exact List.getElem_mem _)
  refine wp_forT (Inv := Inv) dense.id.i (tv dense.id.n) endBody N hN ?_ ?_ ?_ ?_
  · rintro i t le' m' ⟨-, hi, hiv, -, -, ho⟩
    refine ⟨hi, hiv, ?_, rfl⟩
    show PTree.get _ _ = _
    rw [ho _ (by decide) (by decide)]; exact hn
  · exact ⟨rfl, Nat.zero_le _, temps_gss _ _ _, hparr, Unch.refl _ _, fun x h1 _ => temps_gso _ _ h1⟩
  · rintro i t le' m' hi ⟨rfl, -, hiv, hp, hu, ho⟩
    have g : ∀ x, x ≠ dense.id.i → x ≠ idOf 715 → PTree.get x le' = PTree.get x le := ho
    have hcol' := (g _ (by decide) (by decide)).trans hcol
    have hlab' := (g _ (by decide) (by decide)).trans hlab
    have hptn' := (g _ (by decide) (by decide)).trans hptn
    have hn' := (g _ (by decide) (by decide)).trans hn
    have hcarr' := hcarr.unch hu (Ne.symm hb1)
    have hlarr' := hlarr.unch hu (Ne.symm hb2)
    -- the end of the loop body, once `t715` is known
    have fin : ∀ le2 (b : Bool), (b = true ↔ (i + 1 = N ∨ key L[i]! ≠ key L[i + 1]!)) →
        PTree.get (idOf 715) le2 = some (.Vint (if b then Lib.Integers.Int.one else Lib.Integers.Int.zero)) →
        PTree.get dense.id.i le2 = some (.Vint (ir i)) →
        PTree.get dense.id.ptn le2 = some (.Vptr bp Ptrofs.zero) →
        (∀ x, x ≠ dense.id.i → x ≠ idOf 715 → PTree.get x le2 = PTree.get x le) →
        Wp Statement.xi ge dense.fn.main
          (.Sifthenelse (tv (idOf 715)) (sk (.Sassign (ix dense.id.ptn (tv dense.id.i)) (ci 0 tint))) .Sskip)
          { normal := fun t' _ le' m' => PTree.get dense.id.i le' = some (.Vint (ir i)) ∧
              Inv (i + 1) (E0 ++ t') (PTree.set dense.id.i (.Vint (ir (i + 1))) le') m',
            brk := fun _ _ _ _ => False, cont := fun _ _ _ _ => False, ret := fun _ _ _ => False }
          e le2 m' := by
      intro le2 b hb h715 hi2 hp2 ho2
      apply wp_if_eval
      simp only [Exec.evalExpr, h715, typeof]
      cases b
      · simp only [Bool.false_eq_true, ite_false, cop]
        rw [ite_eq_right (by decide)]
        apply wp_skip
        refine ⟨hi2, rfl, by omega, temps_gss _ _ _, hp.congr fun x hx => endPtn_keep
          (fun h => absurd (hb.2 h) (by simp)) hx, hu, fun x h1 h2 => ?_⟩
        rw [temps_gso _ _ h1, ho2 x h1 h2]
      · simp only [ite_true, cop]
        rw [ite_eq_left (by decide)]
        wp_step; wp_step
        refine Logic.wp_store hp hN dense.id.ptn hp2 (tv dense.id.i) i hi hi2 rfl (ci 0 tint) 0 rfl rfl ?_
        intro m2 hp3 hu2
        refine ⟨hi2, rfl, by omega, temps_gss _ _ _, hp3.congr fun x hx => ?_, hu.trans hu2,
          fun x h1 h2 => ?_⟩
        · exact endPtn_mark (hb.1 rfl) hx
        · rw [temps_gso _ _ h1, ho2 x h1 h2]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hiv, hn', typeof, cop, ir_sub]
    rw [ir_eq (a := (i : Int)) (b := (N : Int) - 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hlast : i + 1 = N
    · rw [ite_eq_left (by simp; omega)]
      apply wp_set_eval
      simp only [Exec.evalExpr, seqPost, Post.after, E0_append]
      exact fin _ true (by simp [hlast]) (temps_gss _ _ _) (by rw [temps_gso _ _ (by decide)]; exact hiv)
        (by rw [temps_gso _ _ (by decide)]; exact hptn') fun x h1 h2 => by
          rw [temps_gso _ _ h2, ho x h1 h2]
    · rw [ite_eq_right (by simp; omega)]
      have hi1 : i + 1 < N := by omega
      have hl0 : Exec.evalExpr ge e le' m' (ix dense.id.lab (tv dense.id.i)) =
          some (.Vint (ir (L[i]! : Int))) := by
        rw [eval_at hlarr' hN dense.id.lab hlab' (tv dense.id.i) i hi hiv rfl]
        simp [ints, prefixArr_get hi, hi]
      have hl1 : Exec.evalExpr ge e le' m'
          (ix dense.id.lab (.Ebinop .Oadd (tv dense.id.i) (ci 1 tint) tint)) =
          some (.Vint (ir (L[i + 1]! : Int))) := by
        rw [eval_at hlarr' hN dense.id.lab hlab' _ (i + 1) hi1
          (by simp only [Exec.evalExpr, hiv, typeof, cop, ir_add]; push_cast; rfl) rfl]
        simp [ints, prefixArr_get hi1, hi1]
      have hc0 : Exec.evalExpr ge e le' m' (ix dense.id.colour (ix dense.id.lab (tv dense.id.i))) =
          some (.Vint (ir (key L[i]! : Int))) := by
        rw [eval_at hcarr' hN dense.id.colour hcol' _ _ (hLx i hi) hl0 rfl]
        simp only [ints]
        rw [prefixArr_get (hLx i hi), if_pos (hLx i hi), hcs _ (hLx i hi)]
      have hc1 : Exec.evalExpr ge e le' m'
          (ix dense.id.colour (ix dense.id.lab (.Ebinop .Oadd (tv dense.id.i) (ci 1 tint) tint))) =
          some (.Vint (ir (key L[i + 1]! : Int))) := by
        rw [eval_at hcarr' hN dense.id.colour hcol' _ _ (hLx _ hi1) hl1 rfl]
        simp only [ints]
        rw [prefixArr_get (hLx _ hi1), if_pos (hLx _ hi1), hcs _ (hLx _ hi1)]
      have hk0 := hkey _ (hLx i hi)
      have hk1 := hkey _ (hLx _ hi1)
      wp_step; wp_step
      apply wp_set_eval
      rw [Exec.evalExpr, Exec.evalExpr, hc0, hc1]
      simp only [typeof, cop]
      rw [ir_eq (a := (key L[i]! : Int)) (b := (key L[i + 1]! : Int)) ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩]
      simp only [seqPost, Post.after, E0_append]
      by_cases hk : key L[i]! = key L[i + 1]!
      · simp only [show decide ((key L[i]! : Int) = (key L[i + 1]! : Int)) = true from
          decide_eq_true (by rw [hk]), Bool.not_true, Val.of_bool, Bool.false_eq_true, ite_false,
          Vfalse, cop]
        refine fin (PTree.set (idOf 715) _ le') false
          ⟨fun h => absurd h (by decide), fun h => by
            rcases h with h | h
            · exact absurd h hlast
            · exact absurd hk h⟩
          (by rw [temps_gss]; rfl) (by rw [temps_gso _ _ (by decide)]; exact hiv)
          (by rw [temps_gso _ _ (by decide)]; exact hptn') fun x h1 h2 => by
            rw [temps_gso _ _ h2, ho x h1 h2]
      · simp only [show decide ((key L[i]! : Int) = (key L[i + 1]! : Int)) = false from
          decide_eq_false (by omega), Bool.not_false, Val.of_bool, ite_true, Vtrue, cop]
        refine fin (PTree.set (idOf 715) _ le') true
          ⟨fun _ => .inr hk, fun _ => rfl⟩
          (by rw [temps_gss]; rfl) (by rw [temps_gso _ _ (by decide)]; exact hiv)
          (by rw [temps_gso _ _ (by decide)]; exact hptn') fun x h1 h2 => by
            rw [temps_gso _ _ h2, ho x h1 h2]
  · rintro t le' m' ⟨rfl, -, -, hp, hu, ho⟩
    exact hQ le' m' hp hu ho

end NautyVerified.Proofs.Harness

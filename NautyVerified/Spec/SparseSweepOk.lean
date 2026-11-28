import NautyVerified.Spec.SparseNodeOk

/-!
# The sparse sweep invariants at the start of a sweep and at each child

`sparse_sweepOff_start`, `sparse_sweepFirst_start`: a sparse node that reaches
its sweep starts it in `SparseSweepOff`/`SparseSweepFirst`;
`sparse_sweepOff_child`, `sparse_sweepFirst_child`: each child of a sweep is
called in `SparseNodeOk`.
-/

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso.Nauty
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {n k : Nat}

local notation "SState" => Hex.GraphIso.Nauty.Sparse.State

/-- The renamed-run part of `sparse_sweepOff_start`. -/
theorem sparse_sweepOff_start₀ {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat}
    {st : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : SparseNodeOk₀ G false level numcells st)
    (tcLevel : Nat) :
    let g : Sparse.Graph n := .ofGraph G.graph
    let v := Sparse.visit g level numcells st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := Sparse.chooseTarget false g tcLevel level v.1 st₁
    let cl := Sparse.classify g level v.1 ct.2.2.2
    let lx := leafExit cl.1 level cl.2
    lx.1 = .done →
      SparseSweepOff₀ G level v.1 ct.1.toNat ct.2.1 (ct.2.1.nextElem none) (cheapCheck false level lx.2) := by
  obtain ⟨t, st₀, rfl, hlevel, h, hinv, -, hoff⟩ := h
  obtain ⟨last, hd, ha⟩ := hoff rfl
  have hln := sparse_level_le' h
  have hL1 : level < n + 2 := by omega
  have hL2 : level < nautyInfinity := by omega
  have D := Sparse.depthPolicy (.ofGraph G.graph) (n + 2) tcLevel last
  have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) tcLevel
  have hv := h.visit_ready hn0 hlevel
  have hvd := D.visit level numcells st₀ hd
  have hvf := F.visit level numcells st₀
  have hcode := D.code level numcells st₀
  have hvi : InvS (Sparse.visit (.ofGraph G.graph) level numcells st₀).2.2 := hinv
  dsimp only [Sparse.policy, Generic.Policy.visit, Generic.Policy.compareCodes,
    Generic.Policy.chooseTarget, Generic.Policy.classify, Generic.Policy.leafExit,
    Generic.Policy.cheapCheck] at hvd hvf hcode ⊢
  rw [sparse_visit_twG t _ level numcells st₀ hL1 hL2]
  generalize Sparse.visit (.ofGraph G.graph) level numcells st₀ = r at hv hvd hvf hcode hvi ⊢
  obtain ⟨nc, code, s1⟩ := r
  dsimp only at hv hvd hvf hcode hvi ⊢
  have hcd := compareCodes_depth (level := level) hvd hcode
  have hcf := F.compare level code s1
  have hcl := hv.compare code
  dsimp only [Sparse.policy, Generic.Policy.compareCodes] at hcf
  have hci : InvS (compareCodes level code s1) :=
    ⟨by rw [compareCodes_noncheapG]; exact hvi.1, by rw [(reference_fields hcf).2]; exact hvi.2.1,
      leafI_compare hvi.2.2 level code⟩
  rw [compareCodes_twG]
  generalize compareCodes level code s1 = s2 at hcd hcf hcl hci ⊢
  have ht : false = false → s2.eqlevFirst = level → t[level]! = s2.firsttc[level]! := by
    intro _ he
    rw [(reference_fields hcf).1, (reference_fields hvf).1]
    exact ha.2 level hlevel (by have := hcd.1; omega)
  rw [sparse_chooseTarget_twG t false _ tcLevel level nc s2 hL1 hL2 ht]
  have htd := D.target level nc s2 hcd
  have htf := F.target level nc s2
  have htl := hcl.ready.target_frame false tcLevel
  have htarget := hcl.ready.target hn0 hlevel false tcLevel
  have hk := sparse_chooseTarget_keeps false (.ofGraph G.graph) tcLevel level nc s2
  dsimp only [Sparse.policy, Generic.Policy.chooseTarget] at htd htf hk htarget
  have hti : InvS (Sparse.chooseTarget false (.ofGraph G.graph) tcLevel level nc s2).2.2.2 :=
    ⟨by rw [hk.1]; exact hci.1, by rw [hk.2.1]; exact hci.2.1,
      sparse_leafI_target hci.2.2 false _ tcLevel level nc⟩
  generalize Sparse.chooseTarget false (.ofGraph G.graph) tcLevel level nc s2 = c
    at htd htf htl htarget hti hk ⊢
  obtain ⟨tc, cell, size, s3⟩ := c
  dsimp only at htd htf htl htarget hti hk ⊢
  simp only [Bool.false_eq_true, ite_false]
  rw [sparse_classify_twG]
  have hcld := (D.classify level nc s3 htd).1
  have hclf := F.classify level nc s3
  have hclr := htl.ready.classify
  dsimp only [Sparse.policy, Generic.Policy.classify] at hcld hclf
  have hcli : InvS (Sparse.classify (.ofGraph G.graph) level nc s3).2 :=
    ⟨by rw [sparse_classify_noncheap]; exact hti.1, by rw [(reference_fields hclf).2]; exact hti.2.1,
      sparse_leafI_classify hti.2.2 _ level nc⟩
  generalize Sparse.classify (.ofGraph G.graph) level nc s3 = cl at hcld hclf hclr hcli ⊢
  obtain ⟨leaf, s4⟩ := cl
  dsimp only at hcld hclf hclr hcli ⊢
  rw [leafExit_twG t leaf level s4 (by have := hcli.1; omega) (by have := hcli.1; omega)]
  have hled := D.leaf leaf level s4 trivial hcld
  have hlef := F.leaf leaf level s4
  have hler := hclr.ready.leaf leaf
  dsimp only [Sparse.policy, Generic.Policy.leafExit] at hled hlef
  have hlei : InvS (leafExit leaf level s4).2 :=
    ⟨by rw [leafExit_noncheap]; exact hcli.1, by rw [(reference_fields hlef).2]; exact hcli.2.1,
      leafI_leafExit hcli.2.2 leaf level (sparse_labPerm hn0 hclr.ready)⟩
  generalize leafExit leaf level s4 = le at hled hlef hler hlei ⊢
  obtain ⟨exit, s5⟩ := le
  dsimp only at hled hlef hler hlei ⊢
  intro _
  have hf5 : s5.firsttc = s1.firsttc := by
    rw [(reference_fields hlef).1, (reference_fields hclf).1, (reference_fields htf).1,
      (reference_fields hcf).1]
  rw [cheapCheck_twG t false level s5 hL1 hL2]
  have hchd := D.cheap false level s5 hled
  have hchf := F.cheap false level s5
  have hchr := hler.ready.cheap false
  dsimp only [Sparse.policy, Generic.Policy.cheapCheck] at hchd hchf
  have hchi : InvS (cheapCheck false level s5) := by
    refine ⟨?_, by rw [(reference_fields hchf).2]; exact hlei.2.1, leafI_cheap hlei.2.2 false level⟩
    unfold cheapCheck; split
    · show level + 1 ≤ n + 1; omega
    · exact hlei.1
  have htarget6 : Generic.Target Sparse.State.frame level tc.toNat cell (cheapCheck false level s5) :=
    ((htarget.of_out hclr.frame.effect).of_out hler.frame.effect).of_out hchr.frame.effect
  refine ⟨t, cheapCheck false level s5, rfl, hlevel, hchr.ready, htarget6,
    fun v hv => VSet.nextElem_mem hv, hchi, last, hchd, ?_⟩
  rw [(reference_fields hchf).1, hf5, (reference_fields hvf).1]; exact ha

/-- The refined labelling of a sparse off-path node parses as a label. -/
theorem SparseNodeOk₀.visit_parse {G : Hex.GraphIso.Sparse.Colored n k} {first : Bool} {level numcells : Nat}
    {st : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : SparseNodeOk₀ G first level numcells st) :
    ∃ l : Hex.GraphIso.Label n,
      Hex.GraphIso.Label.ofArray? n (Sparse.visit (.ofGraph G.graph) level numcells st).2.2.lab = some l := by
  obtain ⟨t, st₀, rfl, hlevel, h, -⟩ := h
  have hln := sparse_level_le' h
  rw [sparse_visit_twG t _ level numcells st₀ (by omega) (by omega)]
  exact (h.visit_ready hn0 hlevel).parse hn0

/-- An off-path node that reaches its sweep starts it in `SparseSweepOff`. -/
theorem sparse_sweepOff_start {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat}
    {st : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : SparseNodeOk G false level numcells st)
    (tcLevel : Nat) :
    let g : Sparse.Graph n := .ofGraph G.graph
    let v := Sparse.visit g level numcells st
    let st₁ := compareCodes level v.2.1 v.2.2
    let ct := Sparse.chooseTarget false g tcLevel level v.1 st₁
    let cl := Sparse.classify g level v.1 ct.2.2.2
    let lx := leafExit cl.1 level cl.2
    lx.1 = .done →
      SparseSweepOff G level v.1 ct.1.toNat ct.2.1 (ct.2.1.nextElem none) (cheapCheck false level lx.2) :=
  fun hd => ⟨sparse_sweepOff_start₀ hn0 hn h.1 tcLevel hd,
    (sparse_store_sweepOff tcLevel level numcells st (h.2.2 rfl).1 (h.1.visit_parse hn0 hn)).2,
    sparse_gcaSw_sweepOff _ tcLevel level numcells st (h.2.2 rfl).2 hd⟩

/-- Each child of an off-path sweep is called in `SparseNodeOk`. -/
theorem sparse_sweepOff_child {G : Hex.GraphIso.Sparse.Colored n k} {level numcells tc tv : Nat}
    {cell : VSet n} {st : SState n} (hn0 : 0 < n)
    (h : SparseSweepOff G level numcells tc cell (some tv) st) :
    SparseNodeOk G false (level + 1) (numcells + 1) ((Sparse.policy (n := n)).child false level tc tv st) := by
  obtain ⟨h, hs, hg⟩ := h
  refine ⟨?_, fun h => absurd h (by decide), fun _ => ⟨hs.child false level tc tv, gcaOk_child hg false tc tv⟩⟩
  obtain ⟨t, st₀, rfl, hlevel, hok, htarget, hcur, hinv, last, hd, ha⟩ := h
  have hln := sparse_level_le hok
  have D := Sparse.depthPolicy (.ofGraph G.graph) (n + 2) 100 last
  have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) 100
  have hch := hok.child hn0 hlevel false htarget (hcur tv rfl)
  have hcd := D.child false level tc tv st₀ hd
  have hcf := F.child false level tc tv st₀
  rw [sparse_child_twG t false level tc tv st₀ (by omega)]
  refine ⟨t, _, rfl, by omega, hch, ⟨hinv.1, hinv.2.1,
    (leafI_child hinv.2.2 false level tc tv (fun h => absurd h (by decide))).congr rfl rfl rfl rfl rfl rfl⟩,
    fun h => absurd h (by decide), fun _ => ⟨last, hcd, ?_⟩⟩
  rw [(reference_fields hcf).1]; exact ha

/-- The renamed-run part of `sparse_sweepFirst_start`. -/
theorem sparse_sweepFirst_start₀ {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat}
    {st : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : SparseNodeOk₀ G true level numcells st)
    (tcLevel : Nat) :
    let g : Sparse.Graph n := .ofGraph G.graph
    let v := Sparse.visit g level numcells st
    let st₁ := recordFirst level v.2.1 v.2.2
    let ct := Sparse.chooseTarget true g tcLevel level v.1 st₁
    v.1 ≠ n → ∃ tv1, ct.2.1.nextElem none = some tv1 ∧
      SparseSweepFirst₀ G level v.1 ct.1.toNat tv1 ct.2.1 (some tv1) (cheapCheck true level ct.2.2.2) := by
  obtain ⟨t, st₀, rfl, hlevel, h, hinv, hfirst, -⟩ := h
  obtain ⟨horb, ha⟩ := hfirst rfl
  have hln := sparse_level_le' h
  have hL1 : level < n + 2 := by omega
  have hL2 : level < nautyInfinity := by omega
  have hv := h.visit_ready hn0 hlevel
  have hvi : InvS (Sparse.visit (.ofGraph G.graph) level numcells st₀).2.2 := hinv
  have hvo : OrbIdS (Sparse.visit (.ofGraph G.graph) level numcells st₀).2.2 := horb
  have hva : AgreeTo (level - 1) t (Sparse.visit (.ofGraph G.graph) level numcells st₀).2.2.firsttc := ha
  have hcode := (Sparse.depthPolicy (.ofGraph G.graph) (n + 2) tcLevel 0).code level numcells st₀
  dsimp only [Sparse.policy, Generic.Policy.visit] at hcode ⊢
  rw [sparse_visit_twG t _ level numcells st₀ hL1 hL2]
  generalize Sparse.visit (.ofGraph G.graph) level numcells st₀ = r at hv hvi hvo hva hcode ⊢
  obtain ⟨nc, code, s1⟩ := r
  dsimp only at hv hvi hvo hva hcode ⊢
  rw [recordFirst_twG]
  have hrl := hv.record code
  have hri : InvS (recordFirst level code s1) := ⟨hvi.1, by simp [recordFirst, hvi.2.1],
    leafI_record hvi.2.2 hcode⟩
  have hro : OrbIdS (recordFirst level code s1) := hvo
  have hra : AgreeTo (level - 1) t (recordFirst level code s1).firsttc := hva
  generalize recordFirst level code s1 = s2 at hrl hri hro hra ⊢
  rw [sparse_chooseTarget_twG t true _ tcLevel level nc s2 hL1 hL2 (fun h => absurd h (by decide))]
  have htl := hrl.ready.target_frame true tcLevel
  have htarget := hrl.ready.target hn0 hlevel true tcLevel
  have hk := sparse_chooseTarget_keeps true (.ofGraph G.graph) tcLevel level nc s2
  have hcell := sparse_first_cell (tcLevel := tcLevel) hn0 hlevel hrl.ready
  have hl3 := sparse_leafI_target hri.2.2 true (.ofGraph G.graph) tcLevel level nc
  generalize Sparse.chooseTarget true (.ofGraph G.graph) tcLevel level nc s2 = c
    at htl htarget hk hcell hl3 ⊢
  obtain ⟨tc, cell, size, s3⟩ := c
  dsimp only at htl htarget hk hcell hl3 ⊢
  simp only [ite_true]
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk
  simp only [ite_true] at hk4
  intro hnc
  have hi3 : InvS s3 := ⟨by rw [hk1]; exact hri.1, by rw [hk2]; exact hri.2.1, hl3⟩
  have ho3 : OrbIdS s3 := fun v hv => by rw [hk3]; exact hro v hv
  have ha3 : AgreeTo level (t.set! level tc) s3.firsttc := by
    rw [hk4]
    have := hra.set tc
    rwa [Nat.sub_add_cancel hlevel] at this
  obtain ⟨v, hv⟩ := hcell hnc
  rw [cheapCheck_twG (t.set! level tc) true level s3 hL1 hL2]
  have hchr := htl.ready.cheap true
  have hcheq : ∃ k', cheapCheck true level s3 = { s3 with noncheaplevel := k' } ∧ k' ≤ n + 1 := by
    unfold cheapCheck; split
    · exact ⟨level + 1, rfl, by omega⟩
    · exact ⟨s3.noncheaplevel, rfl, hi3.1⟩
  obtain ⟨k', hk', hk'le⟩ := hcheq
  have hchi : InvS (cheapCheck true level s3) :=
    ⟨by rw [hk']; exact hk'le, by rw [hk']; exact hi3.2.1, leafI_cheap hi3.2.2 true level⟩
  refine ⟨v, hv, t.set! level tc, cheapCheck true level s3, rfl, hlevel, hchr.ready,
    htarget.of_out hchr.frame.effect, fun w hw => by cases hw; exact VSet.nextElem_mem hv,
    hchi, .inl ⟨rfl, by rw [hk']; exact ho3, by rw [hk']; exact ha3⟩⟩

theorem sparse_rows_cheap (first : Bool) (level : Nat) (st : SState n) :
    (cheapCheck first level st).canong.toRows = st.canong.toRows := by
  unfold cheapCheck; split <;> rfl

/-- A first-path node that is not a leaf starts its sweep in `SparseSweepFirst`. -/
theorem sparse_sweepFirst_start {G : Hex.GraphIso.Sparse.Colored n k} {level numcells : Nat}
    {st : SState n} (hn0 : 0 < n) (hn : n + 2 < nautyInfinity) (h : SparseNodeOk G true level numcells st)
    (tcLevel : Nat) :
    let g : Sparse.Graph n := .ofGraph G.graph
    let v := Sparse.visit g level numcells st
    let st₁ := recordFirst level v.2.1 v.2.2
    let ct := Sparse.chooseTarget true g tcLevel level v.1 st₁
    v.1 ≠ n → ∃ tv1, ct.2.1.nextElem none = some tv1 ∧
      SparseSweepFirst G level v.1 ct.1.toNat tv1 ct.2.1 (some tv1) (cheapCheck true level ct.2.2.2) :=
  fun hv => by
    obtain ⟨tv1, he, hs⟩ := sparse_sweepFirst_start₀ hn0 hn h.1 tcLevel hv
    refine ⟨tv1, he, hs, fun _ => ?_, fun v hc hne => absurd (Option.some.inj hc).symm hne⟩
    rw [sparse_rows_cheap, Sparse.chooseTarget_rows]
    exact h.2.1 rfl

/-- Each child of a first-path sweep is called in `SparseNodeOk`. -/
theorem sparse_sweepFirst_child {G : Hex.GraphIso.Sparse.Colored n k} {level numcells tc tv1 tv : Nat}
    {cell : VSet n} {st : SState n} (hn0 : 0 < n)
    (h : SparseSweepFirst G level numcells tc tv1 cell (some tv) st) :
    SparseNodeOk G (tv == tv1) (level + 1) (numcells + 1)
      ((Sparse.policy (n := n)).child true level tc tv st) := by
  obtain ⟨h, hb, hsg⟩ := h
  have hpart : (tv == tv1) = true → tv = tv1 := by simp
  refine ⟨?_, fun he => hb (by rw [hpart he]), fun hf => ?_⟩
  · obtain ⟨t, st₀, rfl, hlevel, hok, htarget, hcur, hinv, hph⟩ := h
    have hln := sparse_level_le hok
    have F := Sparse.referencePolicy (.ofGraph G.graph) (n + 2) 100
    have hch := hok.child hn0 hlevel true htarget (hcur tv rfl)
    have hcf := F.child true level tc tv st₀
    have hci : InvS ((Sparse.policy (n := n)).child true level tc tv st₀) := ⟨hinv.1, hinv.2.1,
      (leafI_child hinv.2.2 true level tc tv (fun _ => VSet.mem_lt (hcur tv rfl))).congr
        rfl rfl rfl rfl rfl rfl⟩
    rw [sparse_child_twG t true level tc tv st₀ (by omega)]
    rcases hph with ⟨hc, horb, ha⟩ | ⟨hpast, last, hd, ha⟩
    · have htv : tv = tv1 := Option.some.inj hc
      subst htv
      simp only [beq_self_eq_true]
      refine ⟨t, _, rfl, by omega, hch, hci, fun _ => ⟨fun v hv => horb v hv, ?_⟩,
        fun h => absurd h (by decide)⟩
      rw [(reference_fields hcf).1, Nat.add_sub_cancel]; exact ha
    · have hlt := hpast rfl tv rfl
      have hne : (tv == tv1) = false := by simp; omega
      rw [hne]
      have D := Sparse.depthPolicy (.ofGraph G.graph) (n + 2) 100 last
      have hcd := D.child true level tc tv st₀ hd
      refine ⟨t, _, rfl, by omega, hch, hci, fun h => absurd h (by decide), fun _ => ⟨last, hcd, ?_⟩⟩
      rw [(reference_fields hcf).1]; exact ha
  · have hne : tv ≠ tv1 := by simpa using hf
    obtain ⟨hs, hg⟩ := hsg tv rfl hne
    exact ⟨hs.child true level tc tv, gcaOk_child hg true tc tv⟩

end NautyVerified.Spec.SearchInf

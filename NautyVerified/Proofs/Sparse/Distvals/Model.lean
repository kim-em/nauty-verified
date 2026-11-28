import HexGraphIso.Nauty.Sparse.Graph
import Std.Tactic.Do

/-!
# HexGraphIso's `Sparse.distvals`, step by step

`distvals_eq`: `Sparse.distvals g root` is the `dist` array of `run g n
(start n root)`, where `run` repeats `outer` (one dequeue and the scan of its
row, `scan`) until the queue is exhausted or full. This is the form
`distvals`'s loops establish.
-/

namespace NautyVerified.Proofs.Sparse.Distvals

open Std.Do
open Hex.GraphIso.Nauty.Sparse
set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- The breadth-first search state: distances, queue, and its two cursors. -/
structure St where
  dist : Array Nat
  queue : Array Nat
  head : Nat
  tail : Nat

/-- The initial state from `root`. -/
def start (n root : Nat) : St :=
  ⟨(Array.replicate n n).set! root 0, (Array.replicate n 0).set! 0 root, 0, 1⟩

/-- Edge `j` of the scanned row, with distance `next` for a new vertex. -/
def edge {n : Nat} (g : Graph n) (next : Nat) (s : Array Nat × Array Nat × Nat) (j : Nat) :
    Array Nat × Array Nat × Nat :=
  if s.1[g.neighbor j]! == n then
    (s.1.set! (g.neighbor j) next, s.2.1.set! s.2.2 (g.neighbor j), s.2.2 + 1)
  else s

/-- The edges `l` of a row. -/
def scan {n : Nat} (g : Graph n) (next : Nat) (s : Array Nat × Array Nat × Nat) (l : List Nat) :
    Array Nat × Array Nat × Nat :=
  l.foldl (edge g next) s

/-- The edges of row `i`. -/
abbrev row {n : Nat} (g : Graph n) (i : Nat) : List Nat :=
  List.range' g.offsets[i]! (g.offsets[i + 1]! - g.offsets[i]!)

/-- Dequeue a vertex and scan its row. -/
def outer {n : Nat} (g : Graph n) (s : St) : St :=
  let i := s.queue[s.head]!
  let r := scan g (s.dist[i]! + 1) (s.dist, s.queue, s.tail) (row g i)
  ⟨r.1, r.2.1, s.head + 1, r.2.2⟩

/-- The search is over. -/
abbrev Stop (n : Nat) (s : St) : Prop := n ≤ s.tail ∨ s.tail ≤ s.head

/-- At most `k` steps of the search. -/
def run {n : Nat} (g : Graph n) : Nat → St → St
  | 0, s => s
  | k + 1, s => if Stop n s then s else run g k (outer g s)

theorem run_stop {n : Nat} {g : Graph n} {s : St} (h : Stop n s) : ∀ k, run g k s = s
  | 0 => rfl
  | _ + 1 => by simp [run, h]

theorem run_succ {n : Nat} {g : Graph n} {s : St} (h : ¬ Stop n s) (k : Nat) :
    run g (k + 1) s = run g k (outer g s) := by
  simp [run, h]

/-- What the search keeps true of distances `d`, queue `q` and tail `t`: the
queue below `t` holds distinct vertices, exactly the ones with a distance
other than `n`, and the vertex at position `p` has distance at most `p`. -/
structure Good (n : Nat) (d q : Array Nat) (t : Nat) : Prop where
  dsize : d.size = n
  qsize : q.size = n
  tle : t ≤ n
  qlt : ∀ p < t, q[p]! < n
  inj : ∀ p < t, ∀ p' < t, q[p]! = q[p']! → p = p'
  seen : ∀ v < n, (d[v]! ≠ n ↔ ∃ p < t, q[p]! = v)
  depth : ∀ p < t, d[q[p]!]! ≤ p

theorem Good.dle {n : Nat} {d q : Array Nat} {t : Nat} (h : Good n d q t) {v : Nat} (hv : v < n) :
    d[v]! ≤ n := by
  by_cases hd : d[v]! = n
  · omega
  · obtain ⟨p, hp, rfl⟩ := (h.seen v hv).1 hd
    have := h.depth p hp
    have := h.tle
    omega

/-- `t` distinct values below `n`. -/
theorem card_le {f : Nat → Nat} {t n : Nat} (hlt : ∀ p < t, f p < n)
    (hinj : ∀ p < t, ∀ p' < t, f p = f p' → p = p') : t ≤ n := by
  have hnd : ((List.range t).map f).Nodup := by
    refine List.pairwise_map.2 (List.nodup_range.imp_of_mem fun ha hb hab hf => hab ?_)
    exact hinj _ (List.mem_range.1 ha) _ (List.mem_range.1 hb) hf
  have := hnd.length_le_of_subset (l₂ := List.range n) (fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (hlt p (List.mem_range.1 hp)))
  simpa using this

/-- An unseen vertex leaves room in the queue. -/
theorem Good.tlt {n : Nat} {d q : Array Nat} {t : Nat} (h : Good n d q t) {k : Nat} (hk : k < n)
    (hd : d[k]! = n) : t < n := by
  have := card_le (f := fun p => if p < t then q[p]! else k) (t := t + 1) (n := n)
    (fun p hp => by by_cases h' : p < t <;> simp [h', h.qlt, hk])
    (fun p hp p' hp' hf => by
      by_cases h1 : p < t <;> by_cases h2 : p' < t <;> simp only [h1, h2, ite_true, ite_false] at hf
      · exact h.inj p h1 p' h2 hf
      · exact absurd ((h.seen k hk).2 ⟨p, h1, hf⟩) (by simp [hd])
      · exact absurd ((h.seen k hk).2 ⟨p', h2, hf.symm⟩) (by simp [hd])
      · omega)
  omega

theorem get_set {a : Array Nat} {k x v : Nat} (hv : v < a.size) :
    (a.set! k x)[v]! = if k = v then x else a[v]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ v (by simpa using hv),
    Array.getElem_setIfInBounds hv, getElem!_pos a v hv]

/-- `edge` keeps `Good`. -/
theorem Good.edge {n : Nat} {g : Graph n} {next : Nat} {d q : Array Nat} {t : Nat} (h : Good n d q t)
    (hnext : next < n) (hnt : next ≤ t) {j : Nat} (hj : g.neighbor j < n) :
    Good n (edge g next (d, q, t) j).1 (edge g next (d, q, t) j).2.1 (edge g next (d, q, t) j).2.2 ∧
      next ≤ (edge g next (d, q, t) j).2.2 ∧ t ≤ (edge g next (d, q, t) j).2.2 := by
  unfold Distvals.edge
  by_cases hd : d[g.neighbor j]! = n
  · simp only [hd, beq_self_eq_true, ite_true]
    have htn := h.tlt hj hd
    have hds := h.dsize
    have hqs := h.qsize
    refine ⟨⟨by simp [hds], by simp [hqs], htn, fun p hp => ?_, fun p hp p' hp' hf => ?_,
      fun v hv => ?_, fun p hp => ?_⟩, by omega, by omega⟩
    · rw [get_set (by omega)]
      by_cases hpt : t = p
      · simp [hpt, hj]
      · simp only [hpt, ite_false]; exact h.qlt p (by omega)
    · rw [get_set (by omega), get_set (by omega)] at hf
      by_cases h1 : t = p <;> by_cases h2 : t = p'
      · omega
      · rw [ite_eq_left h1, ite_eq_right h2] at hf
        exact absurd ((h.seen _ hj).2 ⟨p', by omega, hf.symm⟩) (by simp [hd])
      · rw [ite_eq_right h1, ite_eq_left h2] at hf
        exact absurd ((h.seen _ hj).2 ⟨p, by omega, hf⟩) (by simp [hd])
      · rw [ite_eq_right h1, ite_eq_right h2] at hf
        exact h.inj p (by omega) p' (by omega) hf
    · rw [get_set (by omega)]
      by_cases hkv : g.neighbor j = v
      · subst hkv
        simp only [ite_true]
        exact ⟨fun _ => ⟨t, by omega, by rw [get_set (by omega)]; simp⟩, fun _ => by omega⟩
      · simp only [hkv, ite_false]
        rw [h.seen v hv]
        constructor
        · rintro ⟨p, hp, rfl⟩
          refine ⟨p, by omega, ?_⟩
          rw [get_set (by omega)]
          have : t ≠ p := by omega
          simp [this]
        · rintro ⟨p, hp, hpv⟩
          rw [get_set (by omega)] at hpv
          by_cases htp : t = p
          · simp only [htp, ite_true] at hpv; exact absurd hpv hkv
          · simp only [htp, ite_false] at hpv; exact ⟨p, by omega, hpv⟩
    · rw [get_set (show p < q.size by omega)]
      by_cases htp : t = p
      · simp only [htp, ite_true]
        rw [get_set (by omega)]; simp; omega
      · simp only [htp, ite_false]
        have hq := h.qlt p (by omega)
        rw [get_set (by omega)]
        by_cases hk : g.neighbor j = q[p]!
        · exact absurd ((h.seen _ hj).2 ⟨p, by omega, hk.symm⟩) (by simp [hd])
        · simp only [hk, ite_false]; exact h.depth p (by omega)
  · have : (d[g.neighbor j]! == n) = false := by simpa using hd
    simp only [this]
    exact ⟨h, hnt, Nat.le_refl _⟩

/-- `scan` keeps `Good`. -/
theorem Good.scan {n : Nat} {g : Graph n} {next : Nat} (l : List Nat) (hl : ∀ j ∈ l, g.neighbor j < n) :
    ∀ {d q : Array Nat} {t : Nat}, Good n d q t → next < n → next ≤ t →
      Good n (scan g next (d, q, t) l).1 (scan g next (d, q, t) l).2.1 (scan g next (d, q, t) l).2.2 ∧
        t ≤ (scan g next (d, q, t) l).2.2 := by
  induction l with
  | nil => intro d q t h _ _; exact ⟨h, Nat.le_refl _⟩
  | cons j l ih =>
    intro d q t h hn ht
    have ⟨h1, h2, h3⟩ := h.edge (g := g) hn ht (hl j (List.mem_cons_self ..))
    have := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) h1 hn h2
    have e : Distvals.scan g next (d, q, t) (j :: l) = Distvals.scan g next
        ((Distvals.edge g next (d, q, t) j).1, (Distvals.edge g next (d, q, t) j).2.1,
          (Distvals.edge g next (d, q, t) j).2.2) l :=
      rfl
    rw [e]
    exact ⟨this.1, by omega⟩

/-- `edge` and `scan` keep the distance of a vertex already seen. -/
theorem edge_keep {n : Nat} {g : Graph n} {next : Nat} {d q : Array Nat} {t v j : Nat}
    (hv : v < d.size) (hd : d[v]! ≠ n) : (edge g next (d, q, t) j).1[v]! = d[v]! := by
  unfold edge
  by_cases hk : d[g.neighbor j]! = n
  · simp only [hk, beq_self_eq_true, ite_true]
    rw [get_set hv]
    have : g.neighbor j ≠ v := fun h => hd (h ▸ hk)
    simp [this]
  · have : (d[g.neighbor j]! == n) = false := by simpa using hk
    simp only [this, Bool.false_eq_true, ite_false]

theorem scan_keep {n : Nat} {g : Graph n} {next : Nat} (l : List Nat) :
    ∀ {d q : Array Nat} {t v : Nat}, v < d.size → d[v]! ≠ n →
      (scan g next (d, q, t) l).1[v]! = d[v]! ∧ (scan g next (d, q, t) l).1.size = d.size := by
  induction l with
  | nil => intro d q t v _ _; exact ⟨rfl, rfl⟩
  | cons j l ih =>
    intro d q t v hv hd
    have hs : (edge g next (d, q, t) j).1.size = d.size := by
      unfold edge; split <;> simp
    have hk := edge_keep (g := g) (next := next) (q := q) (t := t) (j := j) hv hd
    have e : scan g next (d, q, t) (j :: l) = scan g next
        ((edge g next (d, q, t) j).1, (edge g next (d, q, t) j).2.1, (edge g next (d, q, t) j).2.2) l :=
      rfl
    rw [e]
    have := ih (d := (edge g next (d, q, t) j).1) (q := (edge g next (d, q, t) j).2.1)
      (t := (edge g next (d, q, t) j).2.2) (v := v) (by omega) (by rw [hk]; exact hd)
    exact ⟨this.1.trans hk, this.2.trans hs⟩

/-- Every edge of a row ends below `n`. -/
abbrev Rows (n : Nat) (g : Graph n) : Prop := ∀ i < n, ∀ j ∈ row g i, g.neighbor j < n

/-- `outer` keeps `Good` while the search runs. -/
theorem Good.outer {n : Nat} {g : Graph n} (hg : Rows n g) {s : St}
    (h : Good n s.dist s.queue s.tail) (hs : ¬ Stop n s) :
    Good n (outer g s).dist (outer g s).queue (outer g s).tail ∧ (outer g s).head = s.head + 1 ∧
      (outer g s).head ≤ (outer g s).tail := by
  simp only [Stop, not_or, Nat.not_le] at hs
  have hi := h.qlt s.head hs.2
  have hdi := h.depth s.head hs.2
  have := (Good.scan (g := g) (next := s.dist[s.queue[s.head]!]! + 1) (row g s.queue[s.head]!)
    (hg _ hi) h (by omega) (by omega))
  exact ⟨this.1, rfl, by have := this.2; unfold Distvals.outer; dsimp only; omega⟩

theorem good_start {n root : Nat} (hr : root < n) :
    Good n (start n root).dist (start n root).queue (start n root).tail where
  dsize := by simp [start]
  qsize := by simp [start]
  tle := by simp [start]; omega
  qlt p hp := by
    simp only [start] at hp ⊢
    rw [show p = 0 by omega, get_set (by simp; omega)]; simpa using hr
  inj p hp p' hp' _ := by simp only [start] at hp hp'; omega
  seen v hv := by
    simp only [start]
    have hq : ((Array.replicate n 0).set! 0 root)[0]! = root := by
      rw [get_set (by simp; omega)]; simp
    rw [get_set (by simp; omega)]
    constructor
    · intro hne
      by_cases hrv : root = v
      · exact ⟨0, by omega, by rw [hq, hrv]⟩
      · simp only [hrv, ite_false] at hne
        rw [getElem!_pos _ v (by simp; omega)] at hne
        simp at hne
    · rintro ⟨p, hp, hpv⟩
      rw [show p = 0 by omega, hq] at hpv
      subst hpv
      simp only [ite_true]
      omega
  depth p hp := by
    simp only [start] at hp ⊢
    have hq : ((Array.replicate n 0).set! 0 root)[0]! = root := by
      rw [get_set (by simp; omega)]; simp
    rw [show p = 0 by omega, hq, get_set (by simp; omega)]
    simp

theorem distvals_eq {n : Nat} (g : Graph n) (root : Nat) :
    distvals g root = (run g n (start n root)).dist := by
  unfold distvals
  apply Id.of_wp_run_eq rfl (fun r => r = (run g n (start n root)).dist)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜run g cursor.suffix.length ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩ =
      run g n (start n root)⌝
  | inv2 pref cur suff h b dist s1 queue s2 head tail hs i head' next hinv => ⇓⟨cursor, r⟩ =>
      ⌜r = scan g next (b.1, b.2.1, b.2.2.2) cursor.prefix⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one, List.length_cons, List.length_nil] at *
  case vc1.step.isTrue =>
    rename_i hstop hrun _
    rw [← hrun, run_stop (by simpa [Stop, or_comm] using hstop), run_stop (by simpa [Stop] using hstop)]
  case vc2.step.isTrue =>
    rename_i hd hb _ _
    subst hb
    simp only [scan, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [edge]
    rw [ite_eq_left (by assumption)]
  case vc3.step.isFalse =>
    rename_i hd hb _ _
    subst hb
    simp only [scan, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [edge]
    rw [ite_eq_right (by assumption)]
  case vc5.step.isFalse.post.success =>
    subst ‹_ = scan _ _ _ _›
    have hrun : run g (_ + 1) _ = _ := ‹run g (_ + 1) _ = run g n (start n root)›
    rw [← hrun, run_succ (by simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at *; simp only [Stop]; omega)]
    rfl
  case vc6.pre => simp [start]
  case vc7.post.success =>
    have hrun := ‹run g 0 _ = run g n (start n root)›
    rw [← hrun]
    rfl

end NautyVerified.Proofs.Sparse.Distvals

import NautyVerified.Proofs.Sparse.Refine.Ops
import NautyVerified.Proofs.Sparse.Distvals.Search

/-!
# The splitter choice of `refine_sg`'s main loop

`for (i = 0; i < nactive && i < 10; ++i) if (ptn[ACTIVE[i]] <= level) break;`
(`selectLoop`) stops at HexGraphIso's `RefineSt.position` when it finds a
singleton among the first ten queue entries, and at `min nactive 10`
otherwise (`position_found`, `position_none`): `wp_selectLoop`. `wp_pick` then
takes the entry at `RefineSt.position` out of the queue as the C does
(`ACTIVE[i] = ACTIVE[--nactive]`, `dropAt`), sets `isplit` to it and
`trivsplit` to whether it is a singleton.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Sparse.Distvals (cast_b)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- The first-ten scan from `k`, as a `forIn` over a list. -/
theorem scan_found (c : Nat → Bool) : ∀ (len k i p : Nat), k ≤ i → i < k + len → c i = true →
    (∀ j, k ≤ j → j < i → c j = false) →
    (forIn (m := Id) (List.range' k len) p fun j r =>
      if c j = true then pure (ForInStep.done j) else pure (ForInStep.yield r)) = i
  | 0, _, _, _, _, h, _, _ => absurd h (by omega)
  | len + 1, k, i, p, hk, hi, hc, hb => by
    rw [List.range'_succ, List.forIn_cons]
    by_cases hki : k = i
    · subst hki; simp only [hc, ite_true]; rfl
    · have hck := hb k (Nat.le_refl _) (by omega)
      simp only [hck, Bool.false_eq_true, ite_false]
      exact scan_found c len (k + 1) i p (by omega) (by omega) hc fun j h1 h2 => hb j (by omega) h2

theorem scan_none (c : Nat → Bool) : ∀ (len k p : Nat), (∀ j, k ≤ j → j < k + len → c j = false) →
    (forIn (m := Id) (List.range' k len) p fun j r =>
      if c j = true then pure (ForInStep.done j) else pure (ForInStep.yield r)) = p
  | 0, _, _, _ => rfl
  | len + 1, k, p, hb => by
    rw [List.range'_succ, List.forIn_cons]
    simp only [hb k (Nat.le_refl _) (by omega), Bool.false_eq_true, ite_false]
    exact scan_none c len (k + 1) p fun j h1 h2 => hb j (by omega) (by omega)

theorem position_eq (level : Nat) (s : RefineSt n) :
    RefineSt.position level s =
      forIn (m := Id) (List.range' 0 (min s.queue.size 10)) (s.queue.size - 1) fun j r =>
        if decide (s.ptn[s.queue[j]!]! ≤ level) = true then pure (ForInStep.done j)
        else pure (ForInStep.yield r) := by
  unfold RefineSt.position
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  refine congrArg (forIn (m := Id) (List.range' 0 (min s.queue.size 10)) (s.queue.size - 1))
    (funext fun j => funext fun r => ?_)
  by_cases h : s.ptn[s.queue[j]!]! ≤ level <;> simp [h]

/-- The scan finds the first singleton at `i`. -/
theorem position_found (level : Nat) (s : RefineSt n) {i : Nat} (hi : i < min s.queue.size 10)
    (hc : s.ptn[s.queue[i]!]! ≤ level) (hb : ∀ j < i, ¬ s.ptn[s.queue[j]!]! ≤ level) :
    RefineSt.position level s = i := by
  rw [position_eq]
  exact scan_found _ _ 0 i _ (Nat.zero_le _) (by omega) (by simpa using hc)
    fun j _ hj => by simpa using hb j hj

/-- The scan finds no singleton among the first `min size 10` entries. -/
theorem position_none (level : Nat) (s : RefineSt n)
    (hb : ∀ j < min s.queue.size 10, ¬ s.ptn[s.queue[j]!]! ≤ level) :
    RefineSt.position level s = s.queue.size - 1 := by
  rw [position_eq]
  exact scan_none _ _ 0 _ fun j _ hj => by simpa using hb j (by omega)

theorem eval_binop {e : env} {le : temp_env} {m : mem} {op : Cfrontend.Cop.binary_operation}
    {a b : expr} {ty : Cfrontend.Ctypes.type} {va vb : val}
    (ha : Exec.evalExpr sge e le m a = some va) (hb : Exec.evalExpr sge e le m b = some vb) :
    Exec.evalExpr sge e le m (.Ebinop op a b ty) =
      Cfrontend.Cop.sem_binary_operation sge.genv_cenv op va (typeof a) vb (typeof b) m := by
  simp only [Exec.evalExpr, ha, hb]

/-- The queue entry at `i` is a position below `n`. -/
theorem queue_lt (hv : t.Valid L.level) {i : Nat} (hi : i < t.queue.size) : t.queue[i]! < n :=
  (hv.queue_cell hi).1

/-- `selectLoop`, from `i = 0`: it stops at `i ≤ min nactive 10` with every
earlier entry nontrivial, at a singleton when `i < min nactive 10`. -/
theorem wp_selectLoop {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (hr : Rep L t S) (ht : Tmp le L t) (hv : t.Valid L.level)
    (hi : PTree.get id.«i» le = some (.Vint (ir 0)))
    (hQ : ∀ (i : Nat) (le' : temp_env), i ≤ min t.queue.size 10 →
      (∀ j < i, ¬ t.ptn[t.queue[j]!]! ≤ L.level) →
      (i < min t.queue.size 10 → t.ptn[t.queue[i]!]! ≤ L.level) →
      PTree.get id.«i» le' = some (.Vint (ir i)) →
      (∀ x, x ∉ [id.«i», idOf 730] → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m) :
    Wp xi sge F selectLoop Q empty_env le m := by
  have hnl := hok.nlt
  have hqn : t.queue.size ≤ n := queue_size_le hv.queue.set
  have hc2 := hok.c2
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ k, v = 10 - k ∧ k ≤ min t.queue.size 10 ∧
      (∀ j < k, ¬ t.ptn[t.queue[j]!]! ≤ L.level) ∧ PTree.get id.«i» le' = some (.Vint (ir k)) ∧
      ∀ x, x ∉ [id.«i», idOf 730] → PTree.get x le' = PTree.get x le
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ m' = m ∧ ∃ k, v = 10 - k ∧ k < min t.queue.size 10 ∧
      (∀ j < k + 1, ¬ t.ptn[t.queue[j]!]! ≤ L.level) ∧ PTree.get id.«i» le' = some (.Vint (ir k)) ∧
      ∀ x, x ∉ [id.«i», idOf 730] → PTree.get x le' = PTree.get x le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := 10 - 0)
    ⟨rfl, rfl, rfl, 0, rfl, Nat.zero_le _, fun j hj => absurd hj (by omega), hi, fun _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, rfl, k, rfl, hk, hpre, hik, ho⟩
    have ht' := ht.frame ho (by decide)
    have hset : ∀ v, (∀ x, x ∉ [id.«i», idOf 730] → PTree.get x (PTree.set (idOf 730) v le') =
        PTree.get x le) ∧ PTree.get id.«i» (PTree.set (idOf 730) v le') = some (.Vint (ir k)) :=
      fun v => ⟨fun x hx => by
        rw [temps_gso _ _ (fun h => hx (by simp [h]))]; exact ho x hx,
        by rw [temps_gso _ _ (by decide)]; exact hik⟩
    wp_step; wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hik, ht'.nactive, typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := (t.queue.size : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hks : k < t.queue.size
    · rw [ite_eq_left (by simpa using hks)]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hik, typeof, cop, cast_b]
      rw [ir_lt (a := (k : Int)) (b := 10) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      by_cases hk10 : k < 10
      · rw [show decide ((k : Int) < 10) = true from decide_eq_true (by omega)]
        simp (config := {decide := true}) only [Val.of_bool, cop, ite_true]
        apply wp_skip
        simp only [E0_append]
        wp_step; wp_step
        apply wp_if_eval
        have hq := queue_lt hv hks
        have ht2 := ht'.set (x := idOf 730) Vtrue (by decide)
        have hik2 : PTree.get id.«i» (PTree.set (idOf 730) Vtrue le') = some (.Vint (ir k)) := by
          rw [temps_gso _ _ (by decide)]; exact hik
        have hw2 := eval_gw2 (S := S) (le := PTree.set (idOf 730) Vtrue le') hok hm
          (show Exec.evalExpr sge empty_env _ m' (tv id.«i») = _ from hik2) rfl (show k < L.c2 by omega)
        rw [hr.queue k hks] at hw2
        rw [eval_binop (eval_ptn hok hm ht2 hw2 rfl hq) (show Exec.evalExpr sge empty_env _ m' (tv id.«level») = _
          from ht2.level)]
        simp only [typeof, cop]
        have hpl := hr.ptnSmall _ hq
        have hll := hok.levlt
        rw [ir_lt (a := (L.level : Int)) (b := (t.ptn[t.queue[k]!]! : Int)) ⟨by omega, by omega⟩
          ⟨by omega, by omega⟩]
        by_cases hle : t.ptn[t.queue[k]!]! ≤ L.level
        · rw [show decide ((L.level : Int) < (t.ptn[t.queue[k]!]! : Int)) = false from
            decide_eq_false (by omega)]
          simp (config := {decide := true}) only [cop, ite_true]
          apply wp_break
          exact hQ k _ (by omega) hpre (fun _ => hle) (hset _).2 (hset _).1
        · rw [show decide ((L.level : Int) < (t.ptn[t.queue[k]!]! : Int)) = true from
            decide_eq_true (by omega)]
          simp (config := {decide := true}) only [cop, ite_false]
          apply wp_skip
          refine ⟨by simp, rfl, rfl, k, rfl, by omega, fun j hj => ?_, (hset _).2, (hset _).1⟩
          by_cases hjk : j = k
          · subst hjk; exact hle
          · exact hpre j (by omega)
      · rw [show decide ((k : Int) < 10) = false from decide_eq_false (by omega)]
        simp (config := {decide := true}) only [Val.of_bool, cop]
        apply wp_break
        simp only [E0_append]
        exact hQ k _ hk hpre (fun h => absurd h (by omega)) (hset _).2 (hset _).1
    · rw [ite_eq_right (by simpa using hks)]
      wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp (config := {decide := true}) only [ite_false]
      apply wp_break
      simp only [E0_append]
      exact hQ k _ hk hpre (fun h => absurd h (by omega)) (hset _).2 (hset _).1
  · rintro v tr e' le' m' ⟨rfl, rfl, rfl, k, rfl, hk, hpre, hik, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hik, typeof, cop, ir_add]
    refine ⟨10 - (k + 1), by omega, by simp, rfl, rfl, k + 1, rfl, by omega, hpre,
      by simp, fun x hx => ?_⟩
    rw [temps_gso _ _ (fun h => hx (by simp [h])), ho x hx]

/-- `work2[a] = x`, with the block's permissions kept. -/
theorem wp_storeW2K {f : function} {Q : Post} {le : temp_env} {m : mem} {c x : Nat} (hok : Ok n L)
    (hm : Mem m L G t S) {a : expr}
    (ha : Exec.evalExpr sge empty_env le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (hc : c < L.c2) {rhs : expr}
    (hrhs : Exec.evalExpr sge empty_env le m rhs = some (.Vint (ir x))) (hrty : typeof rhs = tint)
    (hQ : ∀ m', Mem m' L G t { S with w2 := upd S.w2 c (.Vint (ir x)) } → Unch m m' (· = L.b2) →
      Alloc.Keep m m' L.b2 → (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      Q.normal E0 empty_env le m') :
    Wp xi sge f (.Sassign (gix id.«nausparse:work2» a) rhs) Q empty_env le m := by
  refine wp_idx_store hm.w2 hm.d2.capLt (eval_w2 hok hm) rfl rfl rfl a c hc ha hty rhs tint hrty
    _ (.Vint (ir x)) hrhs rfl rfl ?_
  intro m' harr hu hk hg
  exact hQ m' (hm.setW2 hok hu hk _ harr) hu hk hg

/-- The choice after `selectLoop`: the found singleton, swapped with the last
queue entry, or the last queue entry. -/
abbrev pick : statement :=
  (.Ssequence
    (sk
      (.Sifthenelse
        (.Ebinop .Olt (tv id.«i») (tv id.«nactive») tint)
        (sk (.Sset (idOf 733) (.Ecast (.Ebinop .Olt (tv id.«i») (ci 10 tint) tint) tbool)))
        (.Sset (idOf 733) (ci 0 tint))))
    (.Sifthenelse
      (tv (idOf 733))
      (.Ssequence
        (sk (.Sset id.«trivsplit» (ci 1 tint)))
        (.Ssequence
          (sk (.Sset id.«isplit» (gix id.«nausparse:work2» (tv id.«i»))))
          (.Ssequence
            (.Ssequence
              (sk
                (.Sset
                  (idOf 731)
                  (.Ecast (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint) tint)))
              (.Sset id.«nactive» (tv (idOf 731))))
            (.Sassign
              (gix id.«nausparse:work2» (tv id.«i»))
              (gix id.«nausparse:work2» (tv (idOf 731)))))))
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (sk
              (.Sset
                (idOf 732)
                (.Ecast (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint) tint)))
            (.Sset id.«nactive» (tv (idOf 732))))
          (.Sset id.«isplit» (gix id.«nausparse:work2» (tv (idOf 732)))))
        (sk
          (.Sset id.«trivsplit»
            (.Ebinop .Ole (ix id.«ptn» (tv id.«isplit»)) (tv id.«level») tint))))))

/-- The queue after removing position `pos`, as the C leaves it. -/
abbrev dropAt {n : Nat} (t : RefineSt n) (pos : Nat) : RefineSt n :=
  { t with queue := (t.queue.set! pos t.queue[t.queue.size - 1]!).pop }

theorem dropAt_get {q : Array Nat} {pos i : Nat} (hp : pos < q.size) (hi : i < q.size - 1) :
    ((q.set! pos q[q.size - 1]!).pop)[i]! = if i = pos then q[q.size - 1]! else q[i]! := by
  have hs : ((q.set! pos q[q.size - 1]!).pop).size = q.size - 1 := by simp
  rw [getElem!_pos _ i (by omega)]
  simp only [Array.getElem_pop]
  have hs' : i < (q.set! pos q[q.size - 1]!).size := by simp; omega
  rw [show (q.set! pos q[q.size - 1]!)[i]'hs' = (q.set! pos q[q.size - 1]!)[i]! from
    (getElem!_pos _ i hs').symm]
  by_cases h : i = pos
  · subst h; rw [Array.getElem!_set!_self _ _ _ hp, ite_eq_left rfl]
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm h), ite_eq_right h]

/-- `pick`, after `selectLoop` stopped at `i`. -/
theorem wp_pick {Q : Post} {le : temp_env} {m : mem} (hok : Ok n L) (hm : Mem m L G t S)
    (hr : Rep L t S) (ht : Tmp le L t) (hv : t.Valid L.level) (hq0 : 0 < t.queue.size) {i : Nat}
    (hi : i ≤ min t.queue.size 10) (hpre : ∀ j < i, ¬ t.ptn[t.queue[j]!]! ≤ L.level)
    (hsing : i < min t.queue.size 10 → t.ptn[t.queue[i]!]! ≤ L.level)
    (hil : PTree.get id.«i» le = some (.Vint (ir i)))
    (hQ : ∀ le' m', Mem m' L G (dropAt t (RefineSt.position L.level t))
        { S with w2 := upd S.w2 (RefineSt.position L.level t) (S.w2 (t.queue.size - 1)) } →
      Frame L m m' →
      Tmp le' L (dropAt t (RefineSt.position L.level t)) →
      PTree.get id.«isplit» le' = some (.Vint (ir t.queue[RefineSt.position L.level t]!)) →
      PTree.get id.«trivsplit» le' =
        some (Val.of_bool (decide (t.ptn[t.queue[RefineSt.position L.level t]!]! ≤ L.level))) →
      (∀ x, x ∉ [id.«nactive», id.«isplit», id.«trivsplit», idOf 731, idOf 732, idOf 733] →
        PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F pick Q empty_env le m := by
  have hnl := hok.nlt
  have hqn : t.queue.size ≤ n := queue_size_le hv.queue.set
  have hc2 := hok.c2
  have hdsize : (dropAt t (RefineSt.position L.level t)).queue.size = t.queue.size - 1 := by simp
  wp_step; wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hil, ht.nactive, typeof, cop]
  rw [ir_lt (a := (i : Int)) (b := (t.queue.size : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  by_cases hfound : i < min t.queue.size 10
  · have hpos := position_found L.level t hfound (hsing hfound) hpre
    rw [ite_eq_left (by simpa using (show i < t.queue.size by omega))]
    wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr, hil, typeof, cop, cast_b]
    rw [ir_lt (a := (i : Int)) (b := 10) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩,
      show decide ((i : Int) < 10) = true from decide_eq_true (by omega)]
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop]
    simp (config := {decide := true}) only [ite_true]
    let le2 := PTree.set (idOf 733) (Val.of_bool true) le
    wp_step; wp_step; wp_step
    apply wp_set_eval
    simp only [Exec.evalExpr]
    let le3 := PTree.set id.«trivsplit» (.Vint (Lib.Integers.Int.repr (zOfInt 1))) le2
    have hil3 : PTree.get id.«i» le3 = some (.Vint (ir i)) := by
      simp (config := {decide := true}) only [le3, le2, temps_gso]; exact hil
    wp_step; wp_step; wp_step
    apply wp_set_eval
    rw [eval_gw2 hok hm (show Exec.evalExpr sge empty_env le3 m (tv id.«i») = _ from hil3) rfl
      (by omega), hr.queue i (by omega)]
    dsimp only
    let le4 := PTree.set id.«isplit» (.Vint (ir t.queue[i]!)) le3
    have hna4 : PTree.get id.«nactive» le4 = some (.Vint (ir t.queue.size)) := by
      simp (config := {decide := true}) only [le4, le3, le2, temps_gso]; exact ht.nactive
    wp_step; wp_step; wp_step; wp_step
    apply wp_set_eval
    simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, ht.nactive, typeof, cop, ir_sub]
    rw [show ((t.queue.size : Int) - 1) = ((t.queue.size - 1 : Nat) : Int) by omega]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    simp only [E0_append]
    have hlast := hr.queue (t.queue.size - 1) (by omega)
    have hai : Exec.evalExpr sge empty_env (PTree.set id.«nactive» (.Vint (ir ((t.queue.size - 1 : Nat) : Int)))
        (PTree.set (idOf 731) (.Vint (ir ((t.queue.size - 1 : Nat) : Int)))
        (PTree.set id.«isplit» (.Vint (ir t.queue[i]!))
        (PTree.set id.«trivsplit» (.Vint (Lib.Integers.Int.repr (zOfInt 1)))
        (PTree.set (idOf 733) (Val.of_bool true) le))))) m (tv id.«i») = some (.Vint (ir i)) := by
      simp (config := {decide := true}) only [Exec.evalExpr, temps_gso]; exact hil
    refine wp_storeW2K (c := i) (x := t.queue[t.queue.size - 1]!) hok hm hai rfl (by omega) ?_ rfl ?_
    · rw [eval_gw2 hok hm (c := t.queue.size - 1) (by simp (config := {decide := true}) only
        [Exec.evalExpr, temps_gso, temps_gss]) rfl (by omega), hlast]
    intro m' hm' hu hk hg
    refine hQ _ m' ?_ (Frame.ofOne hu hk hg (by simp [Loc.writes, Loc.wblocks])) ?_ ?_ ?_ ?_
    · rw [hpos, hlast]; exact hm'.congr rfl rfl rfl rfl
    · have h1 := (ht.frame (le' := PTree.set (idOf 731) (.Vint (ir ((t.queue.size - 1 : Nat) : Int)))
        (PTree.set id.«isplit» (.Vint (ir t.queue[i]!))
          (PTree.set id.«trivsplit» (.Vint (Lib.Integers.Int.repr (zOfInt 1)))
            (PTree.set (idOf 733) (Val.of_bool true) le))))
        (ws := [idOf 731, id.«isplit», id.«trivsplit», idOf 733]) (fun x hx => by
          simp only [List.mem_cons, not_or] at hx
          rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.1, temps_gso _ _ hx.2.2.1, temps_gso _ _ hx.2.2.2.1])
        (by decide)).setNactive (dropAt t (RefineSt.position L.level t)) rfl
      rw [hdsize] at h1; exact h1
    · simp (config := {decide := true}) only [temps_gso, temps_gss, hpos]
    · simp (config := {decide := true}) only [temps_gso, temps_gss, hpos]
      rw [show decide (t.ptn[t.queue[i]!]! ≤ L.level) = true from decide_eq_true (hsing hfound)]
      rfl
    · intro x hx
      simp only [List.mem_cons, not_or] at hx
      rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.2.2.1, temps_gso _ _ hx.2.1, temps_gso _ _ hx.2.2.1,
        temps_gso _ _ hx.2.2.2.2.2.1]
  · have hi' : i = min t.queue.size 10 := by omega
    have hpos := position_none L.level t (fun j hj => hpre j (by omega))
    have hlast := hr.queue (t.queue.size - 1) (by omega)
    have hql := queue_lt hv (show t.queue.size - 1 < t.queue.size by omega)
    have hpl := hr.ptnSmall _ hql
    have hll := hok.levlt
    have hrest : ∀ v : val, Wp xi sge F
        (.Ssequence
          (.Ssequence
            (.Ssequence
              (sk (.Sset (idOf 732) (.Ecast (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint) tint)))
              (.Sset id.«nactive» (tv (idOf 732))))
            (.Sset id.«isplit» (gix id.«nausparse:work2» (tv (idOf 732)))))
          (sk (.Sset id.«trivsplit» (.Ebinop .Ole (ix id.«ptn» (tv id.«isplit»)) (tv id.«level») tint))))
        Q empty_env (PTree.set (idOf 733) v le) m := by
      intro v
      wp_step; wp_step; wp_step; wp_step; wp_step
      apply wp_set_eval
      simp (config := {decide := true}) only [Exec.evalExpr, temps_gso, ht.nactive, typeof, cop, ir_sub]
      rw [show ((t.queue.size : Int) - 1) = ((t.queue.size - 1 : Nat) : Int) by omega]
      apply wp_set_eval
      simp only [Exec.evalExpr, temps_gss]
      apply wp_set_eval
      rw [eval_gw2 hok hm (c := t.queue.size - 1) (by simp (config := {decide := true}) only
        [Exec.evalExpr, temps_gso, temps_gss]) rfl (by omega), hlast]
      wp_step; wp_step
      apply wp_set_eval
      have ht1 := (ht.frame (le' := PTree.set (idOf 732) (.Vint (ir ((t.queue.size - 1 : Nat) : Int)))
          (PTree.set (idOf 733) v le)) (ws := [idOf 732, idOf 733]) (fun x hx => by
            simp only [List.mem_cons, not_or] at hx
            rw [temps_gso _ _ hx.1, temps_gso _ _ hx.2.1]) (by decide)).setNactive
          (dropAt t (RefineSt.position L.level t)) rfl
      rw [hdsize] at ht1
      have htl := ht1.set (x := id.«isplit») (.Vint (ir t.queue[t.queue.size - 1]!)) (by decide)
      rw [eval_binop (eval_ptn (t := dropAt t (RefineSt.position L.level t)) hok
          (hm.congr rfl rfl rfl rfl) htl (c := t.queue[t.queue.size - 1]!) (by
          simp only [Exec.evalExpr, temps_gss]) rfl hql)
        (show Exec.evalExpr sge empty_env _ m (tv id.«level») = _ from htl.level)]
      simp only [typeof, cop]
      rw [ir_lt (a := (L.level : Int)) (b := (t.ptn[t.queue[t.queue.size - 1]!]! : Int))
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      have hS : ({ S with w2 := upd S.w2 (RefineSt.position L.level t) (S.w2 (t.queue.size - 1)) } : Scr)
          = S := by
        rw [hpos]
        have : upd S.w2 (t.queue.size - 1) (S.w2 (t.queue.size - 1)) = S.w2 := by
          funext j; by_cases hj : j = t.queue.size - 1
          · subst hj; simp
          · rw [upd_ne _ _ hj]
        rw [this]
      refine hQ _ m ?_ (Frame.refl L m) (htl.set (x := id.«trivsplit») _ (by decide)) ?_ ?_ ?_
      · rw [hS]; exact hm.congr rfl rfl rfl rfl
      · simp (config := {decide := true}) only [temps_gso, temps_gss, hpos]
      · simp (config := {decide := true}) only [temps_gss, hpos]
        congr 2
        by_cases h : t.ptn[t.queue[t.queue.size - 1]!]! ≤ L.level <;> simp [h] <;> omega
      · intro x hx
        simp only [List.mem_cons, not_or] at hx
        rw [temps_gso _ _ hx.2.2.1, temps_gso _ _ hx.2.1, temps_gso _ _ hx.1, temps_gso _ _ hx.2.2.2.2.1,
          temps_gso _ _ hx.2.2.2.2.2.1]
    by_cases hs10 : t.queue.size ≤ 10
    · rw [ite_eq_right (by simp; omega)]
      wp_step
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp (config := {decide := true}) only [ite_false]
      exact hrest _
    · rw [ite_eq_left (by simp; omega)]
      wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hil, typeof, cop, cast_b]
      rw [ir_lt (a := (i : Int)) (b := 10) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩,
        show decide ((i : Int) < 10) = false from decide_eq_false (by omega)]
      apply wp_if_eval
      simp only [Exec.evalExpr, temps_gss, typeof, cop]
      simp (config := {decide := true}) only [ite_false]
      exact hrest _

end NautyVerified.Proofs.Sparse.Refine

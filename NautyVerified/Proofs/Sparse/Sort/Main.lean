import NautyVerified.Proofs.Sparse.Sort.Stack
import NautyVerified.Proofs.Sparse.Sort.Ins
import NautyVerified.Proofs.Sparse.Sort.Pivot
import NautyVerified.Proofs.Sparse.Sort.Finish

/-!
# The work-stack loop of `sortindirect`

`wp_pushes`: the two conditional pushes, smaller fragment on top, append
`pushList`. `wp_mainLoop`: `while (top > 0) {...}` from the stack `l` ends with
HexGraphIso's work-stack loop `iterF (bodyS Y)`, for fuel above the total
length of the pending segments; the stack never exceeds its 40 entries since
the entry at depth `i` has length at most `len / 2^i`.
-/

namespace NautyVerified.Proofs.Sparse.Sort

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Spec.SortC

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {C : Ctx}

/-- `if (x > 1) push(pe, x)`, as a list of pushed entries. -/
def maybe (q x : Nat) : List (Nat × Nat) := if x > 1 then [(q, x)] else []

theorem wp_maybePush {f : function} {Q : Post} {bs : block} {le : temp_env} {m : mem}
    {l : List (Nat × Nat)} (hS : StackAt m C bs l) (hl : l.length < 40)
    (htop : PTree.get id.«top» le = some (.Vint (ir l.length))) (pe : expr) (q : Nat) (x : ident)
    (w : Nat) (hw : w < 2147483648)
    (hp : ∀ m', Exec.evalExpr sge (sEnv bs) le m' pe = some (.Vptr C.bx (pt C.base q)))
    (hpt : typeof pe = tptr tint) (hx : PTree.get x le = some (.Vint (ir w)))
    (hQ : ∀ le' m', StackAt m' C bs (l ++ maybe q w) →
      PTree.get id.«top» le' = some (.Vint (ir (l ++ maybe q w).length)) →
      (∀ z, z ≠ id.«top» → PTree.get z le' = PTree.get z le) → Unch m m' (· = bs) →
      Alloc.KeepA m m' → Q.normal E0 (sEnv bs) le' m') :
    Wp xi sge f (sk (.Sifthenelse (.Ebinop .Ogt (tv x) (ci 1 tint) tint) (push pe (tv x)) .Sskip))
      Q (sEnv bs) le m := by
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hx, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 1) = ir ((1 : Nat) : Int) from rfl,
    key_cmp 1 w (by decide) hw]
  by_cases h1 : 1 < w
  · rw [ite_eq_left (by simpa using h1)]
    refine wp_push hS hl htop pe (tv x) q w hp hpt (fun _ => hx) rfl ?_
    intro m' hS' hu hk
    refine hQ _ m' (by simpa [maybe, h1] using hS') (by simp [maybe, h1]) ?_ hu hk
    intro z hz; rw [temps_gso _ _ hz]
  · rw [ite_eq_right (by simpa using h1)]
    apply wp_skip
    refine hQ le m (by simpa [maybe, h1] using hS) (by simpa [maybe, h1] using htop)
      (fun _ _ => rfl) (Unch.refl _ _) (Alloc.KeepA.refl _)

end NautyVerified.Proofs.Sparse.Sort

namespace NautyVerified.Proofs.Sparse.Sort

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Spec.SortC

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {C : Ctx}

/-- The entries the two pushes add, bottom first. -/
def pushList (p sz ba dc : Nat) : List (Nat × Nat) :=
  if ba > dc then maybe p ba ++ maybe (p + sz - dc) dc else maybe (p + sz - dc) dc ++ maybe p ba

omit binary64_certificate binary32_certificate in
theorem children_eq (p sz ba dc : Nat) (l0 : List (Nat × Nat)) :
    Hex.GraphIso.Nauty.Sparse.Sort.children p sz ba dc l0.reverse = (l0 ++ pushList p sz ba dc).reverse := by
  unfold Hex.GraphIso.Nauty.Sparse.Sort.children pushList maybe
  by_cases h : ba > dc <;> by_cases h1 : ba > 1 <;> by_cases h2 : dc > 1 <;> simp [h, h1, h2]

theorem wp_pushes {f : function} {Q : Post} {bs : block} {le : temp_env} {m : mem}
    {l0 : List (Nat × Nat)} (hS : StackAt m C bs l0) (hl : l0.length + 2 ≤ 40)
    (htop : PTree.get id.«top» le = some (.Vint (ir l0.length))) {p sz ba dc : Nat}
    (hx0 : PTree.get id.«x0» le = some (.Vptr C.bx (pt C.base p)))
    (hnn : PTree.get id.«nn» le = some (.Vint (ir sz)))
    (hba : PTree.get id.«ba» le = some (.Vint (ir ba)))
    (hdc : PTree.get id.«dc» le = some (.Vint (ir dc)))
    (hd : dc ≤ sz) (hsz : sz < 2147483648) (hb : ba < 2147483648)
    (hQ : ∀ le' m', StackAt m' C bs (l0 ++ pushList p sz ba dc) →
      PTree.get id.«top» le' = some (.Vint (ir (l0 ++ pushList p sz ba dc).length)) →
      (∀ z, z ≠ id.«top» → PTree.get z le' = PTree.get z le) → Unch m m' (· = bs) →
      Alloc.KeepA m m' → Q.normal E0 (sEnv bs) le' m') :
    Wp xi sge f (sk pushes) Q (sEnv bs) le m := by
  have hpe : ∀ (le' : temp_env) m', (∀ z, z ≠ id.«top» → PTree.get z le' = PTree.get z le) →
      Exec.evalExpr sge (sEnv bs) le' m'
        (.Ebinop .Oadd (pv id.«x0») (.Ebinop .Osub (tv id.«nn») (tv id.«dc») tint) (tptr tint)) =
        some (.Vptr C.bx (pt C.base (p + sz - dc))) := by
    intro le' m' ho
    rw [eval_padd (by rw [ho _ (by decide)]; exact hx0) _ (sz - dc) (by omega)
      (by simp only [Exec.evalExpr]; rw [ho _ (by decide), hnn, ho _ (by decide), hdc]
          simp only [typeof, cop, ir_sub]; congr 3; omega) rfl]
    congr 3; omega
  have hpb : ∀ (le' : temp_env) m', (∀ z, z ≠ id.«top» → PTree.get z le' = PTree.get z le) →
      Exec.evalExpr sge (sEnv bs) le' m' (pv id.«x0») = some (.Vptr C.bx (pt C.base p)) :=
    fun le' m' ho => by rw [eval_pv]; rw [ho _ (by decide)]; exact hx0
  have hlen : ∀ q x, (l0 ++ maybe q x).length ≤ l0.length + 1 := fun q x => by
    simp only [maybe]; split <;> simp
  simp only [sk, pushes]
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hba, hdc, typeof, cop]
  rw [key_cmp dc ba (by omega) hb]
  by_cases hgt : dc < ba
  · rw [ite_eq_left (by simpa using hgt)]
    apply wp_seq
    refine wp_maybePush hS (by omega) htop _ p id.«ba» ba hb (hpb le · fun _ _ => rfl) rfl hba ?_
    intro le1 m1 hS1 htop1 ho1 hu1 hk1
    simp only [seqPost, Post.after, E0_append]
    refine wp_maybePush hS1 (by have := hlen p ba; omega) htop1 _ (p + sz - dc) id.«dc» dc (by omega)
      (hpe le1 · ho1) rfl (by rw [ho1 _ (by decide)]; exact hdc) ?_
    intro le2 m2 hS2 htop2 ho2 hu2 hk2
    have e : l0 ++ maybe p ba ++ maybe (p + sz - dc) dc = l0 ++ pushList p sz ba dc := by
      simp [pushList, hgt]
    rw [e] at hS2 htop2
    exact hQ le2 m2 hS2 htop2 (fun z hz => by rw [ho2 z hz, ho1 z hz]) (hu1.trans hu2)
      (hk1.trans hk2)
  · rw [ite_eq_right (by simpa using hgt)]
    apply wp_seq
    refine wp_maybePush hS (by omega) htop _ (p + sz - dc) id.«dc» dc (by omega)
      (hpe le · fun _ _ => rfl) rfl hdc ?_
    intro le1 m1 hS1 htop1 ho1 hu1 hk1
    simp only [seqPost, Post.after, E0_append]
    refine wp_maybePush hS1 (by have := hlen (p + sz - dc) dc; omega) htop1 _ p id.«ba» ba hb
      (hpb le1 · ho1) rfl (by rw [ho1 _ (by decide)]; exact hba) ?_
    intro le2 m2 hS2 htop2 ho2 hu2 hk2
    have e : l0 ++ maybe (p + sz - dc) dc ++ maybe p ba = l0 ++ pushList p sz ba dc := by
      simp [pushList, hgt]
    rw [e] at hS2 htop2
    exact hQ le2 m2 hS2 htop2 (fun z hz => by rw [ho2 z hz, ho1 z hz]) (hu1.trans hu2)
      (hk1.trans hk2)

end NautyVerified.Proofs.Sparse.Sort

namespace NautyVerified.Proofs.Sparse.Sort

open NautyVerified.Spec.SortC

/-- The pending segments, bottom first: inside `[lo, hi)`, longer than one, and the entry at
depth `i` at most `len / 2 ^ i` long, as the smaller-side-first order keeps them. -/
structure Pend (lo hi len : Nat) (l : List (Nat × Nat)) : Prop where
  ents : ∀ q ∈ l, lo ≤ q.1 ∧ q.1 + q.2 ≤ hi ∧ 1 < q.2
  depth : ∀ i < l.length, 2 ^ i * l[i]!.2 ≤ len

/-- The total length of the pending segments. -/
def wt (l : List (Nat × Nat)) : Nat := (l.map Prod.snd).sum

theorem wt_append (l l' : List (Nat × Nat)) : wt (l ++ l') = wt l + wt l' := by
  simp [wt, List.sum_append]

theorem wt_maybe (q x : Nat) : wt (maybe q x) ≤ x := by
  simp only [maybe]; split <;> simp [wt]

theorem wt_pushList (p sz ba dc : Nat) : wt (pushList p sz ba dc) ≤ ba + dc := by
  have h1 := wt_maybe p ba
  have h2 := wt_maybe (p + sz - dc) dc
  simp only [pushList]; split <;> rw [wt_append] <;> omega

theorem Pend.len_le {lo hi len : Nat} {l : List (Nat × Nat)} (h : Pend lo hi len l)
    (hlen : len < 2147483648) : l.length ≤ 30 := by
  apply Nat.le_of_not_lt
  intro h31
  have hd := h.depth 30 h31
  have hm : l[30]! ∈ l := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h31]
    exact List.getElem_mem h31
  have he := (h.ents _ hm).2.2
  have : 2 ^ 30 * 2 ≤ 2 ^ 30 * l[30]!.2 := Nat.mul_le_mul_left _ he
  omega

theorem Pend.pop {lo hi len : Nat} {l0 : List (Nat × Nat)} {e : Nat × Nat}
    (h : Pend lo hi len (l0 ++ [e])) :
    Pend lo hi len l0 ∧ lo ≤ e.1 ∧ e.1 + e.2 ≤ hi ∧ 1 < e.2 ∧ 2 ^ l0.length * e.2 ≤ len := by
  have he := h.ents e (by simp)
  refine ⟨⟨fun q hq => h.ents q (by simp [hq]), fun i hi => ?_⟩, he.1, he.2.1, he.2.2, ?_⟩
  · have := h.depth i (by simp; omega)
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi] using this
  · have := h.depth l0.length (by simp)
    simpa [List.getElem!_eq_getElem?_getD] using this

theorem pushList_len (p sz ba dc : Nat) : (pushList p sz ba dc).length ≤ 2 := by
  unfold pushList maybe
  by_cases h : ba > dc <;> by_cases h1 : ba > 1 <;> by_cases h2 : dc > 1 <;> simp [h, h1, h2]

theorem pushList_small (p sz ba dc : Nat) (hbd : ba + dc < sz) :
    ∀ j < (pushList p sz ba dc).length, 2 ^ j * ((pushList p sz ba dc)[j]!).2 < sz := by
  intro j hj
  unfold pushList maybe at hj ⊢
  by_cases h : ba > dc <;> by_cases h1 : ba > 1 <;> by_cases h2 : dc > 1 <;>
    simp [h, h1, h2] at hj ⊢ <;> rcases j with _ | _ | j <;> simp_all <;> omega

theorem pushList_ents (p sz ba dc : Nat) (hbd : ba + dc < sz) :
    ∀ q ∈ pushList p sz ba dc, p ≤ q.1 ∧ q.1 + q.2 ≤ p + sz ∧ 1 < q.2 := by
  intro q hq
  unfold pushList maybe at hq
  by_cases h : ba > dc <;> by_cases h1 : ba > 1 <;> by_cases h2 : dc > 1 <;>
    simp [h, h1, h2] at hq <;> (try rcases hq with rfl | rfl) <;> (try subst hq) <;> simp <;> omega

theorem Pend.push {lo hi len : Nat} {l0 : List (Nat × Nat)} {p sz ba dc : Nat}
    (h : Pend lo hi len l0) (hp : lo ≤ p) (hps : p + sz ≤ hi) (hd : 2 ^ l0.length * sz ≤ len)
    (hbd : ba + dc < sz) : Pend lo hi len (l0 ++ pushList p sz ba dc) := by
  refine ⟨fun q hq => ?_, fun i hi => ?_⟩
  · rcases List.mem_append.1 hq with hq | hq
    · exact h.ents q hq
    · have := pushList_ents p sz ba dc hbd q hq; omega
  · by_cases hi0 : i < l0.length
    · have := h.depth i hi0
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi0] using this
    · have hj : i - l0.length < (pushList p sz ba dc).length := by simp at hi; omega
      have hs := pushList_small p sz ba dc hbd _ hj
      have e : (l0 ++ pushList p sz ba dc)[i]! = (pushList p sz ba dc)[i - l0.length]! := by
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega : l0.length ≤ i)]
      rw [e]
      have h2 : 2 ^ i = 2 ^ l0.length * 2 ^ (i - l0.length) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [h2, Nat.mul_assoc]
      exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_of_lt hs)) hd

end NautyVerified.Proofs.Sparse.Sort

namespace NautyVerified.Proofs.Sparse.Sort

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Common.Values CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs CompCert4Lean.Common.Events CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Integers CompCert4Lean.Lib.Maps
open NautyVerified NautyVerified.Logic NautyVerified.Word NautyVerified.Proofs NautyVerified.Spec.SortC
open Hex.GraphIso.Nauty.Sparse.Sort (insertion partition)

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
variable [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
  (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

variable {xi : ExternalCalls} {C : Ctx}

omit binary64_certificate binary32_certificate in
theorem Arr.unch {m m' : mem} {S : block → Prop} (hu : Unch m m' S) (hx : ¬ S C.bx) (hk : ¬ S C.bk)
    {a : Array Nat} (h : Arr m C a) : Arr m' C a :=
  ⟨h.arr.unch hu hx, h.keys.unch hu hk, h.size, h.bnd⟩

omit binary64_certificate binary32_certificate in
theorem iterF_nil (y : Array Nat) (a : Array Nat) : ∀ n, iterF (bodyS y) n (a, []) = (a, [])
  | 0 => rfl
  | _ + 1 => rfl

theorem wp_mainLoop {f : function} {Q : Post} {bs : block} {le : temp_env} {m : mem}
    (hC : C.Ok) (hbx : bs ≠ C.bx) (hbk : bs ≠ C.bk) {start len : Nat} (h1 : 1 ≤ start)
    (hsl : start + len ≤ C.N) {a : Array Nat} {l : List (Nat × Nat)} {fuel : Nat}
    (h : Arr m C a) (hS : StackAt m C bs l) (hP : Pend start (start + len) len l)
    (hw : l = [] ∨ wt l < fuel)
    (htop : PTree.get id.«top» le = some (.Vint (ir l.length)))
    (hy : PTree.get id.«y» le = some (.Vptr C.bk C.yofs))
    (hQ : ∀ le' m', Arr m' C (iterF (bodyS C.Y) fuel (a, l.reverse)).1 → StackAt m' C bs [] →
      Unch m m' (fun z => z = C.bx ∨ z = bs) → Alloc.KeepA m m' → Q.normal E0 (sEnv bs) le' m') :
    Wp xi sge f mainLoop Q (sEnv bs) le m := by
  have hN := hC.nN
  let R := iterF (bodyS C.Y) fuel (a, l.reverse)
  let I := fun (n : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧
    sEnv bs = e' ∧ ∃ a' l', Arr m' C a' ∧ StackAt m' C bs l' ∧ Pend start (start + len) len l' ∧
      (l' = [] ∨ wt l' < n) ∧ iterF (bodyS C.Y) n (a', l'.reverse) = R ∧
      PTree.get id.«top» le' = some (.Vint (ir l'.length)) ∧
      PTree.get id.«y» le' = some (.Vptr C.bk C.yofs) ∧
      Unch m m' (fun z => z = C.bx ∨ z = bs) ∧ Alloc.KeepA m m'
  refine wp_loop (I := I) (J := fun n t e' le' m' => ∃ n', n' < n ∧ I n' t e' le' m') ?_ ?_
    (n := fuel) ⟨rfl, rfl, a, l, h, hS, hP, hw, rfl, htop, hy, Unch.refl _ _, Alloc.KeepA.refl _⟩
  · rintro n t e' le' m' ⟨rfl, rfl, a', l', h', hS', hP', hw', hR, htop', hy', hu, hk⟩
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, htop', typeof, cop]
    rw [show Lib.Integers.Int.repr (zOfInt 0) = ir ((0 : Nat) : Int) from rfl,
      key_cmp 0 l'.length (by decide) (by have := hP'.len_le (by omega); omega)]
    rcases List.eq_nil_or_concat l' with rfl | ⟨l0, ⟨p, sz⟩, rfl⟩
    · rw [ite_eq_right (by simp)]
      apply wp_break
      simp only [E0_append]
      refine hQ le' m' ?_ hS' hu hk
      show Arr m' C R.1
      rw [← hR, List.reverse_nil, iterF_nil]
      exact h'
    · simp only [List.concat_eq_append] at hS' hP' hw' hR htop' ⊢
      obtain ⟨hP0, hpl, hpe, hsz1, hdep⟩ := hP'.pop
      simp only at hpl hpe hsz1 hdep
      have hwl : wt (l0 ++ [(p, sz)]) = wt l0 + sz := by simp [wt_append, wt]
      have hn1 : 1 ≤ n := by rcases hw' with h0 | h0 <;> simp_all <;> omega
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hlen0 := hP0.len_le (by omega)
      rw [ite_eq_left (by simp)]
      apply wp_skip
      simp only [E0_append]
      have hRev : (l0 ++ [(p, sz)]).reverse = (p, sz) :: l0.reverse := by simp
      rw [hRev] at hR
      -- pop
      wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, htop', typeof, cop, ir_sub]
      simp only [E0_append]
      have htop1 : ir (((l0 ++ [(p, sz)]).length : Nat) - 1 : Int) = ir (l0.length : Int) := by
        congr 1; simp
      rw [htop1]
      have hpop := eval_pop (m := m') (le := PTree.set id.«top» (.Vint (ir (l0.length : Int))) le')
        hS' (k := l0.length) (by simp) (temps_gss _ _ _)
      have he : (l0 ++ [(p, sz)])[l0.length]! = (p, sz) := by
        simp [List.getElem!_eq_getElem?_getD]
      rw [he] at hpop
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [hpop.1]
      simp only [E0_append]
      wp_step; wp_step; wp_step
      apply wp_set_eval
      rw [(eval_pop (m := m') (le := PTree.set id.«x0» (.Vptr C.bx (pt C.base p))
        (PTree.set id.«top» (.Vint (ir (l0.length : Int))) le')) hS' (k := l0.length) (by simp)
        (by rw [temps_gso, temps_gss])).2, he]
      simp only [E0_append]
      have hS0 : StackAt m' C bs l0 := hS'.pop
      have hsN : p + sz ≤ C.N := by omega
      have hwl0 : wt l0 + sz < n' + 1 := by
        rcases hw' with h0 | h0
        · simp at h0
        · omega
      wp_step; wp_step; wp_step
      apply wp_if_eval
      simp (disch := decide) only [Exec.evalExpr, temps_gso, temps_gss, typeof, cop]
      rw [show Lib.Integers.Int.repr (zOfInt 11) = ir ((11 : Nat) : Int) from rfl,
        key_cmp sz 11 (by omega) (by decide)]
      by_cases hsmall : sz < 11
      · rw [ite_eq_left (by simpa using hsmall)]
        apply wp_seq
        refine wp_insertion hC h' (by simp (disch := decide) only [temps_gso, temps_gss]; exact hy')
          (by simp (disch := decide) only [temps_gso, temps_gss])
          (by simp (disch := decide) only [temps_gso, temps_gss]) (by omega) hsN ?_
        intro le2 m2 h2 ho2 hu2 hk2
        simp only [seqPost, Post.after]
        apply wp_continue
        refine ⟨n', by omega, by simp, rfl, insertion a' C.Y p sz, l0, h2, hS0.unch hu2 hbx, hP0,
          .inr (by omega), ?_, ?_, ?_, ?_, hk.trans hk2⟩
        · rw [← hR]; simp [iterF, bodyS, hsmall]
        · rw [ho2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp (disch := decide) only [temps_gso, temps_gss]
        · rw [ho2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp (disch := decide) only [temps_gso, temps_gss]; exact hy'
        · exact hu.trans (hu2.mono fun z hz => .inl hz)
      · rw [ite_eq_right (by simpa using hsmall)]
        apply wp_skip
        simp only [E0_append]
        let lp := PTree.set id.«nn» (.Vint (ir (sz : Int))) (PTree.set id.«x0» (.Vptr C.bx (pt C.base p))
          (PTree.set id.«top» (.Vint (ir (l0.length : Int))) le'))
        have hyp : PTree.get id.«y» lp = some (.Vptr C.bk C.yofs) := by
          simp (disch := decide) only [lp, temps_gso, temps_gss]; exact hy'
        have hx0p : PTree.get id.«x0» lp = some (.Vptr C.bx (pt C.base p)) := by
          simp (disch := decide) only [lp, temps_gso, temps_gss]
        have hnnp : PTree.get id.«nn» lp = some (.Vint (ir (sz : Int))) := by
          simp (disch := decide) only [lp, temps_gso, temps_gss]
        have htopp : PTree.get id.«top» lp = some (.Vint (ir (l0.length : Int))) := by
          simp (disch := decide) only [lp, temps_gso, temps_gss]
        wp_step; wp_step; wp_step
        refine wp_pivot hC h' hyp hx0p hnnp (by omega) hsN ?_
        intro le1 hoV hv1
        simp only [seqPost, Post.after, E0_append]
        let v := Hex.GraphIso.Nauty.Sparse.Sort.pivot a' C.Y p sz
        have hvs : v < 2147483648 := by
          obtain ⟨i, hi, hiv⟩ := Hex.GraphIso.Nauty.Sparse.Sort.pivot_mem a' C.Y p sz (by omega)
          rw [show v = _ from hiv]; exact hC.ysmall _ (h'.bnd _ (by omega))
        have g1 : ∀ z, z ≠ id.«v» → z ≠ id.«v1» → z ≠ id.«v2» → z ≠ id.«v3» → z ≠ idOf 704 →
            z ≠ idOf 705 → z ≠ idOf 706 → z ≠ idOf 707 → z ≠ idOf 708 →
            PTree.get z le1 = PTree.get z lp := hoV
        have hx01 : PTree.get id.«x0» le1 = some (.Vptr C.bx (pt C.base p)) := by
          rw [g1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)]; exact hx0p
        have hnn1 : PTree.get id.«nn» le1 = some (.Vint (ir (sz : Int))) := by
          rw [g1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)]; exact hnnp
        -- xb = xa = x0; xd = xc = x0 + (nn - 1)
        wp_step; wp_step; wp_step; wp_step; wp_step
        apply wp_set_eval
        simp only [Exec.evalExpr, hx01, typeof, cop]
        simp only [E0_append]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss]
        apply wp_set_eval
        simp (disch := decide) only [Exec.evalExpr, temps_gso, temps_gss]
        simp only [E0_append]
        wp_step; wp_step; wp_step; wp_step; wp_step
        apply wp_set_eval
        rw [Exec.evalExpr, eval_padd (by simp (disch := decide) only [temps_gso, temps_gss]; exact hx01)
          _ (sz - 1) (by omega) (by
            simp (disch := decide) only [Exec.evalExpr, temps_gso, temps_gss, hnn1, typeof, cop, ir_sub]
            congr 3; omega) rfl]
        simp only [typeof, cop, E0_append]
        apply wp_set_eval
        simp only [Exec.evalExpr, temps_gss]
        apply wp_set_eval
        simp (disch := decide) only [Exec.evalExpr, temps_gso, temps_gss]
        simp only [E0_append]
        rw [show p + (sz - 1) = p + sz - 1 by omega]
        have hy1 : PTree.get id.«y» le1 = some (.Vptr C.bk C.yofs) := by
          rw [g1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)]; exact hyp
        apply wp_seq
        refine wp_partLoop (len := sz) (fuel := sz + 1) (aa := p) (b := p) (c := p + sz) (d := p + sz)
          (v := v) hC h'
          (by simp (disch := decide) only [temps_gso, temps_gss]; exact hy1)
          (by simp (disch := decide) only [temps_gso, temps_gss]; exact hv1) hvs
          ⟨by simp (disch := decide) only [temps_gso, temps_gss],
           by simp (disch := decide) only [temps_gso, temps_gss],
           by simp (disch := decide) only [temps_gso, temps_gss],
           by simp (disch := decide) only [temps_gso, temps_gss]⟩
          (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _) hsN (by omega) (by omega) ?_
        intro le2 m2
        dsimp only
        intro h2 hcur2 hoP hu2 hk2
        simp only [seqPost, Post.after, E0_append]
        have hB := bodyP_inv C.Y v sz (sz + 1) a' p p (p + sz) (p + sz) (by omega) (Nat.le_refl _)
          (by omega) (by omega) (Nat.le_refl _) (by omega) (by omega)
        generalize hr : iterF (bodyP C.Y v sz) (sz + 1) (a', p, p, p + sz, p + sz) = r at h2 hcur2 hB
        obtain ⟨a2, aa2, b2, c2, d2⟩ := r
        simp only at h2 hcur2 hB
        obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hB
        have gP : ∀ z, z ≠ id.«xa» → z ≠ id.«xb» → z ≠ id.«xc» → z ≠ id.«xd» → z ≠ id.«tmp1» →
            z ≠ idOf 711 → z ≠ idOf 712 → z ≠ idOf 709 → z ≠ idOf 710 → PTree.get z le2 = PTree.get z le1 :=
          fun z q1 q2 q3 q4 q5 q6 q7 q8 q9 => by
            rw [hoP z q1 q2 q3 q4 q5 q6 q7]
            simp (disch := decide) only [temps_gso _ _ q1, temps_gso _ _ q2, temps_gso _ _ q3,
              temps_gso _ _ q4, temps_gso _ _ q8, temps_gso _ _ q9]
        have hx02 : PTree.get id.«x0» le2 = some (.Vptr C.bx (pt C.base p)) := by
          rw [gP _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact hx01
        have hnn2 : PTree.get id.«nn» le2 = some (.Vint (ir (sz : Int))) := by
          rw [gP _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact hnn1
        refine wp_finish hC h2 (sk pushes) hx02 hnn2 hcur2 hb0 hb1 hb2 hb7 hb3 hb4 hb5 hb6 hsN ?_
        intro le3 m3
        dsimp only
        intro h3 hba hdc hoF hu3 hk3
        have hpart : partition a' C.Y p sz = partFinish p sz (a2, aa2, b2, c2, d2) := by
          rw [partition_eq, hr]
        have hprop := (Hex.GraphIso.Nauty.Sparse.Sort.partition_proper a' C.Y p sz
          (by rw [h'.size]; exact hsN) (by omega)).1
        rw [hpart] at hprop
        simp only [partFinish] at hprop hba hdc h3
        have gF : ∀ z, z ≠ id.«a» → z ≠ id.«ba» → z ≠ id.«s» → z ≠ id.«xl» → z ≠ id.«xh» →
            z ≠ id.«d» → z ≠ id.«dc» → z ≠ id.«tmp1» → z ≠ id.«xa» → z ≠ id.«xb» → z ≠ id.«xc» →
            z ≠ id.«xd» → z ≠ idOf 711 → z ≠ idOf 712 → z ≠ idOf 709 → z ≠ idOf 710 →
            PTree.get z le3 = PTree.get z le1 :=
          fun z q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 => by
            rw [hoF z q1 q2 q3 q4 q5 q6 q7 q8, gP z q9 q10 q11 q12 q8 q13 q14 q15 q16]
        have hS3 : StackAt m3 C bs l0 := (hS0.unch hu2 hbx).unch hu3 hbx
        refine wp_pushes (p := p) (sz := sz) hS3 (by omega) ?_ ?_ ?_ hba hdc (by omega) (by omega) (by omega) ?_
        · rw [gF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), g1 _ (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]
          exact htopp
        · rw [gF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact hx01
        · rw [gF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]; exact hnn1
        intro le4 m4 hS4 htop4 ho4 hu4 hk4
        refine ⟨n', by omega, by simp, rfl, (partition a' C.Y p sz).1,
          l0 ++ pushList p sz (b2 - aa2) (d2 - c2), ?_, hS4, ?_, ?_, ?_, htop4, ?_, ?_, ?_⟩
        · rw [hpart]; exact Arr.unch hu4 (Ne.symm hbx) (Ne.symm hbk) h3
        · exact hP0.push hpl hpe hdep hprop
        · have := wt_pushList p sz (b2 - aa2) (d2 - c2)
          rw [wt_append]; right; omega
        · rw [← hR, ← children_eq]
          simp only [iterF, bodyS, hsmall, ite_false]
          rw [hpart]
          rfl
        · rw [ho4 _ (by decide), gF _ (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)]; exact hy1
        · exact hu.trans (((hu2.trans hu3).mono fun z hz => .inl hz).trans
            (hu4.mono fun z hz => .inr hz))
        · exact hk.trans (hk2.trans (hk3.trans hk4))
  · rintro n t e' le' m' ⟨n', hn', hI⟩
    apply wp_skip
    exact ⟨n', hn', by simpa using hI⟩

end NautyVerified.Proofs.Sparse.Sort

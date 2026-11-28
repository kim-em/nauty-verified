import NautyVerified.Proofs.Sparse.Refine.Count.Push

/-!
# The later fragments

`wp_frag`: the loop over the later fragments (`fragG`) computes
`iterF (fragStep level last d)`. One fragment (`fragNext`) is `fragPre`
(the boundary, the cell count, the push and the hashes), the run loop and
`fragPost` (the cell starts, `bigsize` and `bigpos`). The pushes stay inside
`ACTIVE` because the queue only grows along the loop (`frag_mono`) and the
caller bounds it at the end.
-/

namespace NautyVerified.Proofs.Sparse.Refine.Count

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse NautyVerified.Proofs.Sparse.Refine
open NautyVerified.Proofs.Set (sk addElementB)
open NautyVerified.Spec.SortC (iterF)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr}

/-- A later fragment at `k + 1` before its run loop. -/
def fragPre (level : Nat) (d : Bool) (s : RefineSt n) (k : Nat) : RefineSt n :=
  hashIf (!d) ((hashIf d { s with ptn := s.ptn.set! k level, numcells := s.numcells + 1 } k).push (k + 1))
    s.hits[s.lab[k + 1]!]!

/-- A later fragment from `l` after its run loop ended at `r.2`. -/
def fragPost (l : Nat) (bp : Option Nat) (bs : Nat) (r : RefineSt n × Nat) :
    RefineSt n × Option Nat × Nat × Nat :=
  let s := { r.1 with cellend := r.1.cellend.set! l r.2 }
  if r.2 - l + 1 == 1 then ({ s with cellstart := s.cellstart.set! s.lab[l]! n }, bp, bs, r.2)
  else
    let s := { s with cellstart := s.cellstart.set! s.lab[l]! l }
    if r.2 - l + 1 > bs then (s, some (s.queue.size - 1), r.2 - l + 1, r.2)
    else (s, bp, bs, r.2)

theorem fragNext_eq (level last : Nat) (d : Bool) (s : RefineSt n) (bp : Option Nat) (bs k : Nat) :
    fragNext level last d (s, bp, bs, k) =
      fragPost (k + 1) bp bs
        (iterF (runStep (k + 1) s.hits[s.lab[k + 1]!]!) (last - 1 - (k + 1)) (fragPre level d s k, k + 1)) := by
  cases d <;> rfl

/-- The C's `bigpos` for the model's. -/
def bpInt : Option Nat → Int
  | none => -1
  | some p => p

/-- The temporaries the later-fragment loop assigns, besides `longcode` and `nactive`. -/
def fragTemps (tv0 tv1 : ident) : List ident :=
  [id.«k», id.«l», id.«w3», id.«size», id.«bigsize», id.«bigpos», tv0, tv1]

/-- The two temporaries of the loop are none of the others. -/
structure FragT (tv0 tv1 : ident) : Prop where
  a0 : tv0 ∉ args ∧ tv0 ≠ id.longcode ∧ tv0 ≠ id.nactive
  a1 : tv1 ∉ args ∧ tv1 ≠ id.longcode ∧ tv1 ≠ id.nactive
  b0 : tv0 ∉ [id.«k», id.«l», id.«w3», id.«j», id.«size», id.«bigsize», id.«bigpos»]
  b1 : tv1 ∉ [id.«k», id.«l», id.«w3», id.«j», id.«size», id.«bigsize», id.«bigpos»]

/-- One later fragment, after the loop test. -/
abbrev fragBody (d : Bool) (t : Common.AST.ident) (rl : statement) : statement :=
      (.Ssequence
        (sk (.Sassign (ix id.«ptn» (tv id.«k»)) (tv id.«level»)))
        (optSeq d (sk (mash (tv id.«k»)))
          (.Ssequence
            (sk
              (.Sassign
                (.Ederef (pi id.«numcells») tint)
                (.Ebinop .Oadd (.Ederef (pi id.«numcells») tint) (ci 1 tint) tint)))
            (.Ssequence
              (sk (.Sset id.«l» (.Ebinop .Oadd (tv id.«k») (ci 1 tint) tint)))
              (.Ssequence
                (addElementB id.«active» id.«nausparse:bit» (tv id.«l»))
                (.Ssequence
                  (enq t id.«l»)
                  (.Ssequence
                    (sk (.Sset id.«w3» (gix id.«nausparse:work3» (ix id.«lab» (tv id.«l»)))))
                    (optSeq (!d)
                      (sk (mash (tv id.«w3»)))
                      (.Ssequence
                        (.Ssequence (sk (.Sset id.«k» (tv id.«l»))) rl)
                        (.Ssequence
                          (sk
                            (.Sset id.«size»
                              (.Ebinop .Oadd
                                (.Ebinop .Osub (tv id.«k») (tv id.«l») tint)
                                (ci 1 tint)
                                tint)))
                          (sk
                            (.Sifthenelse
                              (.Ebinop .Oeq (tv id.«size») (ci 1 tint) tint)
                              (sk
                                (.Sassign
                                  (gix id.«nausparse:work1» (ix id.«lab» (tv id.«l»)))
                                  (tv id.«n»)))
                              (.Ssequence
                                (sk
                                  (.Sassign
                                    (gix id.«nausparse:work1» (ix id.«lab» (tv id.«l»)))
                                    (tv id.«l»)))
                                (sk
                                  (.Sifthenelse
                                    (.Ebinop .Ogt (tv id.«size») (tv id.«bigsize») tint)
                                    (.Ssequence
                                      (sk (.Sset id.«bigsize» (tv id.«size»)))
                                      (sk
                                        (.Sset id.«bigpos»
                                          (.Ebinop .Osub (tv id.«nactive») (ci 1 tint) tint))))
                                    .Sskip)))))))))))))))

theorem fragG_eq (d : Bool) (t : Common.AST.ident) (rl : statement) : fragG d t rl =
    .Sloop
      (.Ssequence
        (sk
          (.Sifthenelse
            (.Ebinop .Olt (tv id.«k») (.Ebinop .Osub (tv id.«j») (ci 1 tint) tint) tint)
            .Sskip
            .Sbreak))
        (fragBody d t rl))
      .Sskip := rfl

/-- `a + 1` of an `int` temporary. -/
theorem eval_inc {le : temp_env} {m : mem} {x : ident} {a : Nat}
    (h : PTree.get x le = some (.Vint (ir a))) :
    Exec.evalExpr sge empty_env le m (.Ebinop .Oadd (tv x) (ci 1 tint) tint) =
      some (.Vint (ir ((a + 1 : Nat) : Int))) := by
  simp only [Exec.evalExpr, h, typeof, cop, ir_add]; rfl

/-- `a - 1` of an `int` temporary. -/
theorem eval_dec {le : temp_env} {m : mem} {x : ident} {a : Nat} (h0 : 1 ≤ a)
    (h : PTree.get x le = some (.Vint (ir a))) :
    Exec.evalExpr sge empty_env le m (.Ebinop .Osub (tv x) (ci 1 tint) tint) =
      some (.Vint (ir ((a - 1 : Nat) : Int))) := by
  simp only [Exec.evalExpr, h, typeof, cop, ir_sub]
  congr 3; omega

theorem Mem.ce {m : mem} (h : Mem m L G t S) (e : Array Nat) : Mem m L G { t with cellend := e } S :=
  h.congr rfl rfl rfl rfl

theorem Rep.ce (h : Rep L t S) (e : Array Nat) : Rep L { t with cellend := e } S := { h with }

theorem Tmp.ce {le : temp_env} (h : Tmp le L t) (e : Array Nat) : Tmp le L { t with cellend := e } :=
  h.congr rfl rfl

theorem ne_of_not_mem {x y : ident} {l : List ident} (h : x ∉ l) (hy : y ∈ l) : x ≠ y :=
  fun e => h (e ▸ hy)

theorem wp_fragBody {Q : Post} {le : temp_env} {m : mem} {d : Bool} {tv0 tv1 : ident}
    (htv : FragT tv0 tv1) (hok : Ok n L) {s : RefineSt n} {bp : Option Nat} {bs k last : Nat}
    (hm : Mem m L G s S) (hr : Rep L s S) (ht : Tmp le L s)
    (hlab : ∀ q < n, s.lab[q]! < n) (hhits : ∀ v < n, S.w3[v]! = s.hits[v]!)
    (hcs : s.cellstart.size = n) (hps : s.ptn.size = n) (hc : s.longcode < 2 ^ 62)
    (hbs : bs ≤ n) (hk : k + 1 < last) (hlast : last ≤ n) (hq : s.queue.size < n)
    (hkv : PTree.get id.«k» le = some (.Vint (ir k)))
    (hj : PTree.get id.«j» le = some (.Vint (ir last)))
    (hbsv : PTree.get id.«bigsize» le = some (.Vint (ir bs)))
    (hbpv : PTree.get id.«bigpos» le = some (.Vint (ir (bpInt bp))))
    (hQ : ∀ le' m' S', Mem m' L G (fragNext L.level last d (s, bp, bs, k)).1 S' →
      Rep L (fragNext L.level last d (s, bp, bs, k)).1 S' →
      Tmp le' L (fragNext L.level last d (s, bp, bs, k)).1 → Frame L m m' → Keeps S S' →
      PTree.get id.«k» le' = some (.Vint (ir (fragNext L.level last d (s, bp, bs, k)).2.2.2)) →
      PTree.get id.«bigsize» le' = some (.Vint (ir (fragNext L.level last d (s, bp, bs, k)).2.2.1)) →
      PTree.get id.«bigpos» le' = some (.Vint (ir (bpInt (fragNext L.level last d (s, bp, bs, k)).2.1))) →
      (∀ x, x ∉ fragTemps tv0 tv1 → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (fragBody d tv0 (runLoopG tv1)) Q empty_env le m := by
  have hnl := hok.nlt
  have hll := hok.levlt
  wp_step; wp_step; wp_step
  refine wp_ptnF hok hm ht (show Exec.evalExpr sge empty_env le m (tv id.«k») = _ from hkv) rfl (by omega)
    (show Exec.evalExpr sge empty_env le m (tv id.«level») = _ from ht.level) rfl hps ?_
  intro m1 hm1 hf1
  simp only [E0_append]
  have b0 := htv.b0
  have b1 := htv.b1
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at b0 b1
  rw [fragNext_eq] at hQ
  let s1 : RefineSt n := { s with ptn := s.ptn.set! k L.level }
  change Wp xi sge F _ Q empty_env le m1
  refine wp_optMash (t := s1) d (ht.congr rfl rfl) hc (show Exec.evalExpr sge empty_env le m1 (tv id.«k») = _ from hkv)
    rfl (by omega) ?_
  intro le2 ht2 ho2
  have hkv2 : PTree.get id.«k» le2 = some (.Vint (ir k)) := by rw [ho2 _ (by decide)]; exact hkv
  have hm1' := Mem.hashIf (t := s1) hm1 d k
  wp_step; wp_step; wp_step
  have hnce : Exec.evalExpr sge empty_env le2 m1
      (.Ebinop .Oadd (.Ederef (pi id.numcells) tint) (ci 1 tint) tint) =
      some (.Vint (ir ((s.numcells + 1 : Nat) : Int))) := by
    rw [eval_binop (eval_nc hm1' ht2) rfl]
    simp only [typeof, cop, ir_add]
    cases d <;> rfl
  refine wp_ncF hok hm1' ht2 hnce rfl ?_
  intro m2 hm2 hf2
  simp only [E0_append]
  let s2 : RefineSt n := hashIf d { s with ptn := s.ptn.set! k L.level, numcells := s.numcells + 1 } k
  have hm2' : Mem m2 L G s2 S := hm2.congr (by cases d <;> rfl) (by cases d <;> rfl) (by cases d <;> rfl)
    (by cases d <;> rfl)
  have ht2' : Tmp le2 L s2 := ht2.congr (by cases d <;> rfl) (by cases d <;> rfl)
  have hr2 : Rep L s2 S := by
    have := Rep.setPtn hr hll k
    cases d
    · exact { this with }
    · exact { this with }
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [eval_inc hkv2]
  have ht3 := ht2'.set (x := id.«l») (.Vint (ir ((k + 1 : Nat) : Int))) (by decide)
  have hq2 : s2.queue.size < n := by cases d <;> exact hq
  refine wp_pushAR htv.a0 (Ne.symm b0.2.1) (by decide) hok hm2' hr2 ht3 (c := k + 1) (by rw [temps_gss])
    (by omega) hq2 ?_
  rintro le4 m3 S3 ⟨hm3, hr3, ht4, hf3, hk3, hw13, ho4⟩
  let s3 : RefineSt n := s2.push (k + 1)
  have hl3 : s3.lab = s.lab := by cases d <;> rfl
  have hh3 : s3.hits = s.hits := by cases d <;> rfl
  have hlv4 : PTree.get id.«l» le4 = some (.Vint (ir ((k + 1 : Nat) : Int))) := by
    rw [ho4 _ (Ne.symm b0.2.1) (by decide), temps_gss]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  have hlk := hlab (k + 1) (by omega)
  rw [eval_gw3 hok hm3 (eval_lab hok hm3 ht4 (show Exec.evalExpr sge empty_env le4 m3 (tv id.«l») = _ from hlv4)
    rfl (by omega)) rfl (by rw [hl3]; exact hlk), hk3.w3, hl3, hhits _ hlk]
  let w := s.hits[s.lab[k + 1]!]!
  have hwl : w < 2147483648 := by have := hr.w3small _ hlk; rw [hhits _ hlk] at this; exact this
  have ht5 := ht4.set (x := id.«w3») (.Vint (ir w)) (by decide)
  have hc3 : s3.longcode < 2 ^ 62 := by
    show (hashIf d _ k).longcode < _
    exact hashIf_code hc
  refine wp_optMash (t := s3) (!d) ht5 hc3 (show Exec.evalExpr sge empty_env _ m3 (tv id.«w3») = _ by
    simp only [Exec.evalExpr, temps_gss]; rfl) rfl hwl ?_
  intro le6 ht6 ho6
  let s4 : RefineSt n := fragPre L.level d s k
  have hs4 : hashIf (!d) s3 w = s4 := rfl
  rw [hs4] at ht6
  have hm4 : Mem m3 L G s4 S3 := Mem.hashIf hm3 (!d) w
  have hr4 : Rep L s4 S3 := Rep.hashIf hr3 (!d) w
  have hl4 : s4.lab = s.lab := by cases d <;> rfl
  have hh4 : s4.hits = s.hits := by cases d <;> rfl
  have hcs4 : s4.cellstart.size = n := by cases d <;> exact hcs
  apply wp_seq; apply wp_seq
  wp_step; wp_step; wp_step
  have hlv6 : PTree.get id.«l» le6 = some (.Vint (ir ((k + 1 : Nat) : Int))) := by
    rw [ho6 _ (by decide), temps_gso _ _ (by decide)]; exact hlv4
  simp only [hlv6]
  have hhits4 : ∀ v < n, S3.w3[v]! = s4.hits[v]! := fun v hv => by rw [hk3.w3, hh4]; exact hhits v hv
  have hlab4 : ∀ q < n, s4.lab[q]! < n := fun q hq => by rw [hl4]; exact hlab q hq
  have hw6 : PTree.get id.«w3» le6 = some (.Vint (ir w)) := by rw [ho6 _ (by decide), temps_gss]
  have hj6 : PTree.get id.«j» le6 = some (.Vint (ir last)) := by
    rw [ho6 _ (by decide), temps_gso _ _ (by decide), ho4 _ (Ne.symm b0.2.2.2.1) (by decide),
      temps_gso _ _ (by decide), ho2 _ (by decide)]; exact hj
  refine wp_runLoop (t := s4) (l := k + 1) (last := last) (w := w)
    ⟨htv.a1.1, htv.a1.2.1, htv.a1.2.2, b1.1, b1.2.2.2.1, b1.2.2.1, b1.2.1⟩
    hok hm4 hr4 (ht6.set (x := id.«k») _ (by decide)) hlab4 hhits4 hcs4 (by omega) hlast hwl
    (by rw [temps_gss]) (by rw [temps_gso _ _ (by decide)]; exact hj6)
    (by rw [temps_gso _ _ (by decide)]; exact hw6) (by rw [temps_gso _ _ (by decide)]; exact hlv6) ?_
  intro le7 m7 S7 hm7 hr7 h72 h73 h74 h75 h76 h77 h78 h79 hf7 hk7 ho7
  simp only [E0_append]
  have hR := iterF_runStep (n := n) (k + 1) w (last - 1 - (k + 1)) s4 (k + 1)
  have hRf := iterF_runStep_fields (n := n) (k + 1) w (last - 1 - (k + 1)) s4 (k + 1)
  generalize iterF (runStep (k + 1) w) (last - 1 - (k + 1)) (s4, k + 1) = R at hm7 hr7 hk7 hQ hR hRf
  obtain ⟨cs, hR1, hcs7⟩ := hR
  obtain ⟨hRq, -, hR2a, hR2b⟩ := hRf
  have hch : ∀ x, x ∉ [id.«k», id.«l», id.«w3», tv0, tv1] → x ≠ id.longcode → x ≠ id.nactive →
      PTree.get x le7 = PTree.get x le := by
    intro x hx h1 h2
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
    rw [ho7 x (by simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]; exact ⟨hx.1, hx.2.2.2.2⟩),
      temps_gso _ _ hx.1, ho6 x h1, temps_gso _ _ hx.2.2.1, ho4 x hx.2.2.2.1 h2, temps_gso _ _ hx.2.1,
      ho2 x h1]
  have nbs : id.«bigsize» ∉ [id.«k», id.«l», id.«w3», tv0, tv1] := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨by decide, by decide, by decide, fun h => b0.2.2.2.2.2.1 h.symm, fun h => b1.2.2.2.2.2.1 h.symm⟩
  have nbp : id.«bigpos» ∉ [id.«k», id.«l», id.«w3», tv0, tv1] := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨by decide, by decide, by decide, fun h => b0.2.2.2.2.2.2 h.symm, fun h => b1.2.2.2.2.2.2 h.symm⟩
  have ht7 : Tmp le7 L R.1 := by
    refine ((ht6.set (x := id.«k») (.Vint (ir ((k + 1 : Nat) : Int))) (by decide)).frame
      (ws := [id.«k», tv1]) ho7 ?_).congr (by rw [hR1]) (by rw [hRq])
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact htv.a1
  have hl7 : R.1.lab = s.lab := by rw [hR1]; exact hl4
  have hlv7 : PTree.get id.«l» le7 = some (.Vint (ir ((k + 1 : Nat) : Int))) := by
    rw [ho7 _ (by simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]; exact ⟨by decide, Ne.symm b1.2.1⟩),
      temps_gso _ _ (by decide)]; exact hlv6
  have hcs7' : R.1.cellstart.size = n := by rw [hR1]; exact hcs7.trans hcs4
  wp_step; wp_step; wp_step
  have hsz : Exec.evalExpr sge empty_env le7 m7 (.Ebinop .Oadd (.Ebinop .Osub (tv id.«k») (tv id.«l») tint)
      (ci 1 tint) tint) = some (.Vint (ir ((R.2 - (k + 1) + 1 : Nat) : Int))) := by
    simp only [Exec.evalExpr, hk7, hlv7, typeof, cop, ir_sub, ir_add]
    congr 3; omega
  apply wp_set_eval
  obtain ⟨sz, hsz'⟩ : ∃ sz, sz = R.2 - (k + 1) + 1 := ⟨_, rfl⟩
  rw [hsz, ← hsz']
  have ht8 := ht7.set (x := id.«size») (.Vint (ir (sz : Int))) (by decide)
  have hszv : PTree.get id.«size» (PTree.set id.«size» (.Vint (ir (sz : Int))) le7) =
      some (.Vint (ir (sz : Int))) := temps_gss _ _ _
  wp_step; wp_step
  apply wp_if_eval
  simp only [Exec.evalExpr, hszv, typeof, cop]
  rw [show Lib.Integers.Int.repr (zOfInt 1) = ir 1 from rfl,
    ir_eq (a := (sz : Int)) (b := 1) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩]
  have hlk7 : R.1.lab[k + 1]! < n := by rw [hl7]; exact hlk
  have hlab8 : Exec.evalExpr sge empty_env (PTree.set id.«size» (.Vint (ir (sz : Int))) le7) m7
      (ix id.lab (tv id.«l»)) = some (.Vint (ir R.1.lab[k + 1]!)) :=
    eval_lab hok hm7 ht8 (show Exec.evalExpr sge empty_env _ m7 (tv id.«l») = _ by
      simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide)]; exact hlv7) rfl (by omega)
  have hS : ∀ x, Keeps S { S7 with w1 := x } := fun x =>
    ⟨h73.trans hk3.w3, h74.trans hk3.w4, h75.trans hk3.st1, h76.trans hk3.mk1, h77.trans hk3.st2,
      h78.trans hk3.mk2⟩
  have hf8 := hf1.trans (hf2.trans (hf3.trans hf7))
  by_cases h1 : sz = 1
  · rw [show decide ((sz : Int) = 1) = true from decide_eq_true (by omega)]
    simp (config := {decide := true}) only [Val.of_bool, ite_true]
    wp_step; wp_step
    refine wp_w1F hok hm7 hlab8 rfl (by have := hok.c1; omega)
      (show Exec.evalExpr sge empty_env _ m7 (tv id.«n») = _ from ht8.n) rfl ?_
    intro m8 hm8 hf8'
    have hfp : fragPost (k + 1) bp bs R = ({ { R.1 with cellend := R.1.cellend.set! (k + 1) R.2 } with
        cellstart := R.1.cellstart.set! R.1.lab[k + 1]! n }, bp, bs, R.2) := by
      simp only [fragPost, show (R.2 - (k + 1) + 1 == 1) = true from beq_iff_eq.2 (hsz' ▸ h1), ite_true]
    rw [hfp] at hQ
    have hr8 := Rep.setStart hr7 hcs7' hlk7 (x := n)
    refine hQ _ m8 _ (hm8.congr rfl rfl rfl rfl) { hr8 with } (ht8.congr rfl rfl)
      (hf8.trans hf8') (hS _) ?_ ?_ ?_ ?_
    · rw [temps_gso _ _ (by decide)]; exact hk7
    · rw [temps_gso _ _ (by decide), hch _ nbs (by decide) (by decide)]; exact hbsv
    · rw [temps_gso _ _ (by decide), hch _ nbp (by decide) (by decide)]; exact hbpv
    · intro x hx h1 h2
      simp only [fragTemps, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
      have hx' : x ∉ [id.«k», id.«l», id.«w3», tv0, tv1] := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
        exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2⟩
      rw [temps_gso _ _ hx.2.2.2.1, hch x hx' h1 h2]
  · rw [show decide ((sz : Int) = 1) = false from decide_eq_false (by omega)]
    simp (config := {decide := true}) only [ite_false]
    wp_step; wp_step; wp_step
    refine wp_w1F hok hm7 hlab8 rfl (by have := hok.c1; omega)
      (show Exec.evalExpr sge empty_env _ m7 (tv id.«l») = _ by
        simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide)]; exact hlv7) rfl ?_
    intro m8 hm8 hf8'
    simp only [E0_append]
    have hr8 := Rep.setStart hr7 hcs7' hlk7 (x := k + 1)
    have hbs8 : PTree.get id.«bigsize» (PTree.set id.«size» (.Vint (ir (sz : Int))) le7) =
        some (.Vint (ir (bs : Int))) := by
      rw [temps_gso _ _ (by decide), hch _ nbs (by decide) (by decide)]; exact hbsv
    have hbp8 : PTree.get id.«bigpos» (PTree.set id.«size» (.Vint (ir (sz : Int))) le7) =
        some (.Vint (ir (bpInt bp))) := by
      rw [temps_gso _ _ (by decide), hch _ nbp (by decide) (by decide)]; exact hbpv
    have hk8 : PTree.get id.«k» (PTree.set id.«size» (.Vint (ir (sz : Int))) le7) =
        some (.Vint (ir (R.2 : Int))) := by rw [temps_gso _ _ (by decide)]; exact hk7
    have ho8 : ∀ x, x ∉ fragTemps tv0 tv1 → x ≠ id.longcode → x ≠ id.nactive →
        PTree.get x (PTree.set id.«size» (.Vint (ir (sz : Int))) le7) = PTree.get x le := by
      intro x hx h1 h2
      simp only [fragTemps, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
      have hx' : x ∉ [id.«k», id.«l», id.«w3», tv0, tv1] := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
        exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2⟩
      rw [temps_gso _ _ hx.2.2.2.1, hch x hx' h1 h2]
    wp_step; wp_step
    apply wp_if_eval
    rw [eval_cmp hszv hbs8]
    simp only [typeof, cop]
    rw [ir_lt (a := (bs : Int)) (b := (sz : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have hq7 : 1 ≤ R.1.queue.size := by
      rw [hRq]; show 1 ≤ (hashIf (!d) s3 w).queue.size; cases d <;> simp [hashIf, s3, RefineSt.push, RefineSt.hash]
    by_cases h2 : bs < sz
    · rw [show decide ((bs : Int) < (sz : Int)) = true from decide_eq_true (by omega)]
      simp (config := {decide := true}) only [ite_true]
      wp_step; wp_step; wp_step
      apply wp_set_eval
      simp only [Exec.evalExpr, hszv]
      wp_step; wp_step
      apply wp_set_eval
      have hna : PTree.get id.nactive (PTree.set id.«bigsize» (.Vint (ir (sz : Int)))
          (PTree.set id.«size» (.Vint (ir (sz : Int))) le7)) = some (.Vint (ir (R.1.queue.size : Int))) := by
        rw [temps_gso _ _ (by decide)]; exact ht8.nactive
      rw [eval_dec hq7 hna]
      have hfp : fragPost (k + 1) bp bs R = ({ { R.1 with cellend := R.1.cellend.set! (k + 1) R.2 } with
          cellstart := R.1.cellstart.set! R.1.lab[k + 1]! (k + 1) }, some (R.1.queue.size - 1), sz, R.2) := by
        simp only [fragPost, show (R.2 - (k + 1) + 1 == 1) = false from beq_eq_false_iff_ne.2 (hsz' ▸ h1),
          Bool.false_eq_true, ite_false, show R.2 - (k + 1) + 1 > bs from hsz' ▸ h2, ite_true, hsz']
      rw [hfp] at hQ
      refine hQ _ m8 _ (hm8.congr rfl rfl rfl rfl) { hr8 with }
        (((ht8.set (x := id.«bigsize») _ (by decide)).set (x := id.«bigpos») _ (by decide)).congr rfl rfl)
        (hf8.trans hf8') (hS _) ?_ ?_ ?_ ?_
      · rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact hk8
      · rw [temps_gso _ _ (by decide), temps_gss]
      · rw [temps_gss]; rfl
      · intro x hx h1 h3
        have hx2 := hx
        simp only [fragTemps, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx2
        rw [temps_gso _ _ hx2.2.2.2.2.2.1, temps_gso _ _ hx2.2.2.2.2.1, ho8 x hx h1 h3]
    · rw [show decide ((bs : Int) < (sz : Int)) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [ite_false]
      apply wp_skip
      have hfp : fragPost (k + 1) bp bs R = ({ { R.1 with cellend := R.1.cellend.set! (k + 1) R.2 } with
          cellstart := R.1.cellstart.set! R.1.lab[k + 1]! (k + 1) }, bp, bs, R.2) := by
        simp only [fragPost, show (R.2 - (k + 1) + 1 == 1) = false from beq_eq_false_iff_ne.2 (hsz' ▸ h1),
          Bool.false_eq_true, ite_false, show ¬ (R.2 - (k + 1) + 1 > bs) from hsz' ▸ h2]
      rw [hfp] at hQ
      exact hQ _ m8 _ (hm8.congr rfl rfl rfl rfl) { hr8 with } (ht8.congr rfl rfl)
        (hf8.trans hf8') (hS _) hk8 hbs8 hbp8 ho8

/-- The model facts the later-fragment loop keeps, for labels `lab` and keys `hits`. -/
structure FragOk (n : Nat) (lab hits : Array Nat) (st : RefineSt n × Option Nat × Nat × Nat) : Prop where
  lab : st.1.lab = lab
  hits : st.1.hits = hits
  cs : st.1.cellstart.size = n
  ps : st.1.ptn.size = n
  code : st.1.longcode < 2 ^ 62
  bp : ∀ p, st.2.1 = some p → p < st.1.queue.size
  bs : st.2.2.1 ≤ n
  qe : ∀ i < st.1.queue.size, st.1.queue[i]! < n

theorem fragPre_fields (level : Nat) (d : Bool) (s : RefineSt n) (k : Nat) :
    (fragPre level d s k).lab = s.lab ∧ (fragPre level d s k).hits = s.hits ∧
      (fragPre level d s k).cellstart = s.cellstart ∧ (fragPre level d s k).ptn = s.ptn.set! k level ∧
      (fragPre level d s k).queue = s.queue.push (k + 1) ∧
      (fragPre level d s k).longcode < 2 ^ 62 ∨ ((fragPre level d s k).lab = s.lab ∧
        (fragPre level d s k).hits = s.hits ∧ (fragPre level d s k).cellstart = s.cellstart ∧
        (fragPre level d s k).ptn = s.ptn.set! k level ∧ (fragPre level d s k).queue = s.queue.push (k + 1) ∧
        (fragPre level d s k).longcode = s.longcode) := by
  left
  refine ⟨by cases d <;> rfl, by cases d <;> rfl, by cases d <;> rfl, by cases d <;> rfl,
    by cases d <;> rfl, ?_⟩
  cases d <;> simp only [fragPre, hashIf, RefineSt.hash, RefineSt.push, Bool.not_true, Bool.not_false,
    ite_true, Bool.false_eq_true, ite_false] <;>
    exact Nat.lt_of_lt_of_le (NautyVerified.Proofs.Refine.mash_lt _ _) (by decide)

theorem FragOk.next {level last : Nat} {d : Bool} {lab hits : Array Nat} {s : RefineSt n}
    {bp : Option Nat} {bs k : Nat} (h : FragOk n lab hits (s, bp, bs, k)) (hk : k + 1 < last)
    (hlast : last ≤ n) : FragOk n lab hits (fragNext level last d (s, bp, bs, k)) := by
  rw [fragNext_eq]
  have hR := iterF_runStep (n := n) (k + 1) s.hits[s.lab[k + 1]!]! (last - 1 - (k + 1))
    (fragPre level d s k) (k + 1)
  have hRf := iterF_runStep_fields (n := n) (k + 1) s.hits[s.lab[k + 1]!]! (last - 1 - (k + 1))
    (fragPre level d s k) (k + 1)
  generalize iterF (runStep (k + 1) s.hits[s.lab[k + 1]!]!) (last - 1 - (k + 1))
    (fragPre level d s k, k + 1) = R at hR hRf
  obtain ⟨cs, hR1, hcs⟩ := hR
  obtain ⟨hRq, -, hR2a, hR2b⟩ := hRf
  have hpre : (fragPre level d s k).lab = s.lab ∧ (fragPre level d s k).hits = s.hits ∧
      (fragPre level d s k).cellstart = s.cellstart ∧ (fragPre level d s k).ptn = s.ptn.set! k level ∧
      (fragPre level d s k).queue = s.queue.push (k + 1) ∧ (fragPre level d s k).longcode < 2 ^ 62 := by
    rcases fragPre_fields level d s k with h' | ⟨h1, h2, h3, h4, h5, h6⟩
    · exact h'
    · exact ⟨h1, h2, h3, h4, h5, h6 ▸ h.code⟩
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpre
  have hs : (R.1.lab = lab ∧ R.1.hits = hits ∧ R.1.ptn.size = n ∧ R.1.longcode < 2 ^ 62 ∧
      R.1.queue = s.queue.push (k + 1)) ∧ R.1.cellstart.size = n := by
    rw [hR1]
    exact ⟨⟨p1.trans h.lab, p2.trans h.hits, by rw [p4]; simp [h.ps], p6, p5⟩, by rw [hcs, p3]; exact h.cs⟩
  obtain ⟨⟨q1, q2, q3, q4, q5⟩, q6⟩ := hs
  have hqe : ∀ i < R.1.queue.size, R.1.queue[i]! < n := by
    rw [q5]
    intro i hi
    simp only [Array.size_push] at hi
    by_cases he : i = s.queue.size
    · subst he; rw [getElem!_pos (s.queue.push (k + 1)) _ (by simpa using hi), Array.getElem_push_eq]; omega
    · rw [getElem!_pos (s.queue.push (k + 1)) _ (by simpa using hi), Array.getElem_push_lt (by omega),
        ← getElem!_pos s.queue _ (by omega)]
      exact h.qe i (show i < s.queue.size by omega)
  have hbp : ∀ p, bp = some p → p < R.1.queue.size := fun p hp => by
    rw [q5, Array.size_push]; have := h.bp p hp; simp only at this; omega
  unfold fragPost
  split
  · exact ⟨q1, q2, by simp [q6], q3, q4, hbp, h.bs, hqe⟩
  · split
    · refine ⟨q1, q2, by simp [q6], q3, q4, fun p hp => ?_, by show R.2 - (k + 1) + 1 ≤ n; omega, hqe⟩
      cases hp; rw [q5, Array.size_push]; omega
    · exact ⟨q1, q2, by simp [q6], q3, q4, hbp, h.bs, hqe⟩

theorem fragNext_k (level last : Nat) (d : Bool) (s : RefineSt n) (bp : Option Nat) (bs k : Nat)
    (hk : k + 1 < last) :
    k + 1 ≤ (fragNext level last d (s, bp, bs, k)).2.2.2 ∧
      (fragNext level last d (s, bp, bs, k)).2.2.2 ≤ last - 1 := by
  rw [fragNext_eq]
  have hRf := iterF_runStep_fields (n := n) (k + 1) s.hits[s.lab[k + 1]!]! (last - 1 - (k + 1))
    (fragPre level d s k) (k + 1)
  generalize iterF (runStep (k + 1) s.hits[s.lab[k + 1]!]!) (last - 1 - (k + 1))
    (fragPre level d s k, k + 1) = R at hRf
  obtain ⟨-, -, h1, h2⟩ := hRf
  unfold fragPost
  split
  · dsimp only; exact ⟨h1, by omega⟩
  · split
    · dsimp only; exact ⟨h1, by omega⟩
    · dsimp only; exact ⟨h1, by omega⟩

theorem iterF_frag_done {level last : Nat} {d : Bool} {st : RefineSt n × Option Nat × Nat × Nat}
    (h : st.2.2.2 ≥ last - 1) : ∀ F, iterF (fragStep level last d) F st = st
  | 0 => rfl
  | F + 1 => by simp only [iterF, fragStep_eq, h, ↓reduceIte]

theorem iterF_frag_next {level last : Nat} {d : Bool} {st : RefineSt n × Option Nat × Nat × Nat}
    (h : ¬ st.2.2.2 ≥ last - 1) (F : Nat) :
    iterF (fragStep level last d) (F + 1) st = iterF (fragStep level last d) F (fragNext level last d st) := by
  simp only [iterF, fragStep_eq, h, ↓reduceIte]

/-- The later-fragment loop's invariant. -/
def FragInv (L : Loc) (G : Hex.SparseGraph n) (d : Bool) (tv0 tv1 : ident) (lab hits : Array Nat)
    (last : Nat) (R : RefineSt n × Option Nat × Nat × Nat) (S0 : Scr) (m0 : mem) (le0 : temp_env)
    (st : RefineSt n × Option Nat × Nat × Nat) (le : temp_env) (m : mem) : Prop :=
  ∃ F' S', st.2.2.2 < last ∧ last - 1 - st.2.2.2 ≤ F' ∧ R = iterF (fragStep L.level last d) F' st ∧
    FragOk n lab hits st ∧ Mem m L G st.1 S' ∧ Rep L st.1 S' ∧ Tmp le L st.1 ∧ Frame L m0 m ∧
    Keeps S0 S' ∧
    PTree.get id.«k» le = some (.Vint (ir st.2.2.2)) ∧ PTree.get id.«j» le = some (.Vint (ir last)) ∧
    PTree.get id.«bigsize» le = some (.Vint (ir st.2.2.1)) ∧
    PTree.get id.«bigpos» le = some (.Vint (ir (bpInt st.2.1))) ∧
    ∀ x, x ∉ fragTemps tv0 tv1 → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le = PTree.get x le0

theorem wp_frag {Q : Post} {le : temp_env} {m : mem} {d : Bool} {tv0 tv1 : ident}
    (htv : FragT tv0 tv1) (hok : Ok n L) {st : RefineSt n × Option Nat × Nat × Nat}
    {lab hits : Array Nat} {last fu : Nat}
    (hm : Mem m L G st.1 S) (hr : Rep L st.1 S) (ht : Tmp le L st.1) (hst : FragOk n lab hits st)
    (hlab : ∀ q < n, lab[q]! < n) (hhits : ∀ v < n, S.w3[v]! = hits[v]!)
    (hF : last - 1 - st.2.2.2 ≤ fu) (hlast : last ≤ n) (hk0 : st.2.2.2 < last)
    (hfin : (iterF (fragStep L.level last d) fu st).1.queue.size ≤ n)
    (hkv : PTree.get id.«k» le = some (.Vint (ir st.2.2.2)))
    (hj : PTree.get id.«j» le = some (.Vint (ir last)))
    (hbsv : PTree.get id.«bigsize» le = some (.Vint (ir st.2.2.1)))
    (hbpv : PTree.get id.«bigpos» le = some (.Vint (ir (bpInt st.2.1))))
    (hQ : ∀ le' m' S', Mem m' L G (iterF (fragStep L.level last d) fu st).1 S' →
      Rep L (iterF (fragStep L.level last d) fu st).1 S' →
      Tmp le' L (iterF (fragStep L.level last d) fu st).1 → Frame L m m' → Keeps S S' →
      FragOk n lab hits (iterF (fragStep L.level last d) fu st) →
      PTree.get id.«bigpos» le' = some (.Vint (ir (bpInt (iterF (fragStep L.level last d) fu st).2.1))) →
      (∀ x, x ∉ fragTemps tv0 tv1 → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le' = PTree.get x le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge F (fragG d tv0 (runLoopG tv1)) Q empty_env le m := by
  have hnl := hok.nlt
  generalize hRdef : iterF (fragStep L.level last d) fu st = R at hfin hQ
  let I := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ st', v = last - st'.2.2.2 ∧ FragInv L G d tv0 tv1 lab hits last R S m le st' le' m'
  let J := fun (v : Nat) (tr : trace) (e' : env) (le' : temp_env) (m' : mem) => tr = E0 ∧
    e' = empty_env ∧ ∃ st', last - st'.2.2.2 < v ∧ FragInv L G d tv0 tv1 lab hits last R S m le st' le' m'
  rw [fragG_eq]
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := last - st.2.2.2)
    ⟨rfl, rfl, st, rfl, fu, S, hk0, hF, hRdef.symm, hst, hm, hr, ht, Frame.refl _ _, Keeps.refl _, hkv, hj,
      hbsv, hbpv, fun _ _ _ _ => rfl⟩
  · rintro v tr e' le' m' ⟨rfl, rfl, ⟨s, bp, bs, k⟩, rfl, F', S', hk', hF', hR, hok', hm', hr', ht', hf', hks,
      hkv', hj', hbsv', hbpv', ho'⟩
    simp only at hk' hF' hkv' hbsv' hbpv'
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [eval_binop (show Exec.evalExpr sge empty_env le' m' (tv id.«k») = _ from hkv')
      (eval_dec (by omega) hj')]
    simp only [typeof, cop]
    rw [ir_lt (a := (k : Int)) (b := ((last - 1 : Nat) : Int)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    by_cases hkl : k < last - 1
    · rw [show decide ((k : Int) < ((last - 1 : Nat) : Int)) = true from decide_eq_true (by omega)]
      simp (config := {decide := true}) only [ite_true]
      apply wp_skip
      simp only [E0_append]
      obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
      have hnk : ¬ (s, bp, bs, k).2.2.2 ≥ last - 1 := by simp only; omega
      rw [iterF_frag_next hnk] at hR
      have hmono := frag_mono L.level last d F'' (fragNext L.level last d (s, bp, bs, k))
      rw [← hR] at hmono
      have hsz := fragNext_size L.level last d (s, bp, bs, k)
      have hkk := fragNext_k L.level last d s bp bs k (by omega)
      refine wp_fragBody htv hok hm' hr' ht' (fun q hq => by rw [hok'.lab]; exact hlab q hq)
        (fun v hv => by rw [hks.w3, hok'.hits]; exact hhits v hv) hok'.cs hok'.ps hok'.code hok'.bs
        (by omega) hlast (by have h1 := hsz.1; have h2 := hmono.1; simp only at h1; omega)
        hkv' hj' hbsv' hbpv' ?_
      intro le2 m2 S2 hm2 hr2 ht2 hf2 hk2 hkv2 hbs2 hbp2 ho2
      refine ⟨rfl, rfl, fragNext L.level last d (s, bp, bs, k), by omega, F'', S2, by omega, by omega, hR,
        hok'.next (by omega) hlast, hm2, hr2, ht2, hf'.trans hf2, hks.trans hk2, hkv2, ?_, hbs2, hbp2,
        fun x hx h1 h2 => by rw [ho2 x hx h1 h2, ho' x hx h1 h2]⟩
      have hjn : id.«j» ∉ fragTemps tv0 tv1 := by
        simp only [fragTemps, List.mem_cons, List.mem_nil_iff, or_false, not_or]
        exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
          fun h => htv.b0 (by rw [← h]; simp), fun h => htv.b1 (by rw [← h]; simp)⟩
      rw [ho2 _ hjn (by decide) (by decide)]
      exact hj'
    · rw [show decide ((k : Int) < ((last - 1 : Nat) : Int)) = false from decide_eq_false (by omega)]
      simp (config := {decide := true}) only [ite_false]
      apply wp_break
      have hd : (s, bp, bs, k).2.2.2 ≥ last - 1 := by simp only; omega
      rw [iterF_frag_done hd] at hR
      subst hR
      exact hQ le' m' S' hm' hr' ht' hf' hks hok' hbpv' ho'
  · rintro v tr e' le' m' ⟨rfl, rfl, st', hlt, hinv⟩
    apply wp_skip
    exact ⟨last - st'.2.2.2, hlt, by simp, rfl, st', rfl, hinv⟩

end NautyVerified.Proofs.Sparse.Refine.Count

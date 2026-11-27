import NautyVerified.Proofs.Refine.Pop
import NautyVerified.Proofs.Refine.Arr
import NautyVerified.Proofs.Set.Global

/-!
# The neighbour counts of the nontrivial pass

`wp_cntHead`: `set1 = workset; set2 = GRAPHROW(g, lab[i], m); cnt = 0;` and
the `POPCOUNT` loop leave `cnt` holding the number of neighbours of `lab[i]`
in the splitter set, `VSet.cardInter`.
-/

namespace NautyVerified.Proofs.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs
open NautyVerified.Proofs.Init (BytecountTable)
open NautyVerified.Proofs.Set (longs)
open NautyVerified.Proofs.Graph (GraphAt)
open Hex.GraphIso.Nauty

variable {xi : ExternalCalls}

/-- `set1 = workset; set2 = GRAPHROW(g, lab[i], m); cnt = 0;` then the `POPCOUNT`
loop with temporaries `a b c d`, then `rest`. -/
abbrev cntHead (a b c d : Common.AST.ident) (rest : statement) : statement :=
  .Ssequence (Set.sk (.Sset dense.id.set1 (.Evar dense.id.«naugraph:workset» (tptr tulong))))
    (.Ssequence
      (Set.sk (.Sset dense.id.set2
        (.Ebinop .Oadd (.Ecast (Set.pv dense.id.g) (tptr tulong))
          (.Ebinop .Omul (tv dense.id.m) (.Ecast (ix dense.id.lab (tv dense.id.i)) tulong) tulong)
          (tptr tulong))))
      (.Ssequence (Set.sk (.Sset dense.id.cnt (ci 0 tint)))
        (.Ssequence (popLoop a b c d) rest)))

theorem ptrTo_zero0 : ptrTo 0 8 0 = Ptrofs.zero := by
  have := Graph.ptrTo_zero Ptrofs.zero
  exact this

theorem wp_cntHead {Q : Post} {le : temp_env} {m : mem} {a b c d : Common.AST.ident}
    (hd : [dense.id.c1, a, b, c, d, dense.id.x, dense.id.set1, dense.id.set2, dense.id.cnt,
      dense.id.m].Pairwise (· ≠ ·)) {rest : statement}
    {n : Nat} {L : Loc} {ctx : Ctx n} {st : RefineSt n} {ws : VSet n} {wsw : Nat → Lib.Integers.int64}
    {i : Nat} (hok : Ok n L) (ht : Tmp le L st)
    (hg : GraphAt m L.bg L.gofs L.gw ctx.g L.M)
    (hlab : ArrayAt m .Mint32 L.bl L.lb (ints st.lab) n)
    (hwsA : ArrayAt m .Mint64 L.bS 0 (longs wsw) L.M)
    (hwsR : SetRep (fun w => bv64 (wsw w)) L.M ws)
    (hwp : Mem.load .Mint64 m Block.naugraphWorkset (zOfInt 0) = some (.Vptr L.bS Ptrofs.zero))
    (hi : PTree.get dense.id.i le = some (.Vint (ir i))) (hin : i < n) (hli : st.lab[i]! < n)
    (hbt : BytecountTable m)
    (hQ : ∀ le', PTree.get dense.id.cnt le' = some (.Vint (ir (ws.cardInter ctx.g[st.lab[i]!]! : Nat))) →
      (∀ z, z ≠ dense.id.c1 → z ≠ a → z ≠ b → z ≠ c → z ≠ d → z ≠ dense.id.x →
        z ≠ dense.id.set1 → z ≠ dense.id.set2 → z ≠ dense.id.cnt →
        PTree.get z le' = PTree.get z le) →
      Wp xi ge Source.dense.fn.refine rest Q empty_env le' m) :
    Wp xi ge Source.dense.fn.refine (cntHead a b c d rest) Q empty_env le m := by
  have hM := hok.Mlt
  have hnM := hok.nM
  have hn := hok.nlt
  have n06 := pwNe hd 6 7 (by decide) (by simp)
  have n68 := pwNe hd 6 8 (by decide) (by simp)
  have n78 := pwNe hd 7 8 (by decide) (by simp)
  have n69 := pwNe hd 6 9 (by decide) (by simp)
  have n79 := pwNe hd 7 9 (by decide) (by simp)
  have n89 := pwNe hd 8 9 (by decide) (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at n06 n68 n78 n69 n79 n89
  simp only [cntHead, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Set.eval_gptr rfl find_naugraphWorkset hwp]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  have hle := eval_at (ge := ge) (e := empty_env) (le := PTree.set dense.id.set1
    (.Vptr L.bS Ptrofs.zero) le) (m := m) hlab (by omega) dense.id.lab
    (by rw [temps_gso _ _ (by decide)]; exact ht.lab) (tv dense.id.i) i hin
    (by show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact hi) rfl
  have e3 : Exec.evalExpr ge empty_env (PTree.set dense.id.set1 (.Vptr L.bS Ptrofs.zero) le) m
      (.Ecast (ix dense.id.lab (tv dense.id.i)) tulong) = some (.Vlong (lr (st.lab[i]! : Int))) := by
    rw [Exec.evalExpr, hle]
    simp only [ints, typeof, cop, cast_int_long_ir (a := (st.lab[i]! : Int)) ⟨by omega, by omega⟩]
  rw [Exec.evalExpr, show Exec.evalExpr ge empty_env _ m (.Ecast (Set.pv dense.id.g) (tptr tulong)) =
    some (.Vptr L.bg L.gofs) by
      simp only [Exec.evalExpr]; rw [temps_gso _ _ (by decide), ht.g]; simp only [typeof, cop],
    Exec.evalExpr, show Exec.evalExpr ge empty_env _ m (tv dense.id.m) = some (.Vint (ir L.M)) from by
      show PTree.get _ _ = _; rw [temps_gso _ _ (by decide)]; exact ht.m, e3]
  simp only [typeof, cop, Graph.mul_lr (show L.M < 2147483648 by omega)]
  rw [show ((L.M : Int) * (st.lab[i]! : Int)) = ((L.M * st.lab[i]! : Nat) : Int) by push_cast; rfl,
    Graph.add_ptrTo_long]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr]
  wp_step
  have hrow := hg.row hli
  refine wp_popLoop hd (bA := L.bS) (baseA := 0) (bB := L.bg)
    (baseB := intOfZ (Ptrofs.unsigned (ptrTo (intOfZ (Ptrofs.unsigned L.gofs)) 8 (L.M * st.lab[i]!))))
    hwsA hrow ?_ ?_ ?_ (k := 0) (temps_gss _ _ _) (by show 0 + 64 * L.M < 2147483648; omega) hbt ?_
  · rw [ptrTo_zero0]; simp (disch := decide) only [temps_gso, temps_gss]
  · rw [Graph.ptrTo_zero]; simp (disch := decide) only [temps_gso, temps_gss]
  · simp (disch := decide) only [temps_gso, temps_gss]; exact ht.m
  · intro le' hc ho
    apply hQ le'
    · rw [hc, Nat.zero_add, pops, cardInter_words hwsR (hg.rep _ hli)]
    · intro z h0 h1 h2 h3 h4 h5 h6 h7 h8
      rw [ho z h0 h1 h2 h3 h4 h5 h6 h7 h8, temps_gso _ _ h8, temps_gso _ _ h7, temps_gso _ _ h6]

end NautyVerified.Proofs.Refine

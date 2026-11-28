import NautyVerified.Proofs.Search.Node.Breakout
import NautyVerified.Proofs.Search.Node.Child
import NautyVerified.Proofs.Search.Node.Long
import NautyVerified.Proofs.Search.Node.LoopSteps
import NautyVerified.Proofs.Search.Node.Process
import NautyVerified.Proofs.Set.GlobalDel

/-!
# The shape of `othernode0`'s child loop

`childLoop_eq`: the loop over the target cell is, statement for statement,
the pieces proved separately (`breakCall`, `ADDELEMENT(fixedpts, tv)`,
`childCall`, `DELELEMENT(fixedpts, tv)`, `earlyRet`, `prune0`, `longIf`,
`recCall`, and `nextStep` as the increment). `child_false_eq`: HexGraphIso's
`child false` is `brokenSt` with `tv` added to `fixedpts`.
-/

namespace NautyVerified.Proofs.Search

open CompCert4Lean CompCert4Lean.Cfrontend.Clight
open NautyVerified NautyVerified.Source
open Hex.GraphIso.Nauty

theorem childLoop_eq : Othernode.childLoop =
    .Sloop
      (.Ssequence
        (Set.sk (.Sifthenelse (.Ebinop .Oge (Refine.tv dense.id.«tv») (ci 0 tint) tint) .Sskip .Sbreak))
        (.Ssequence breakCall
          (.Ssequence (Set.addElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
            (.Ssequence childCall
              (.Ssequence (Set.delElementG dense.id.«nauty:fixedpts» dense.id.«nauty:bit» (Refine.tv dense.id.«tv»))
                (.Ssequence (Set.sk earlyRet)
                  (.Ssequence (Set.sk Othernode.prune0)
                    (.Ssequence (Set.sk longIf) recCall))))))))
      nextStep := rfl

theorem child_false_eq {n : Nat} (level tc tv : Nat) (st : Search n) :
    child false level tc tv st = { brokenSt level tc tv st with fixedpts := st.fixedpts.insert tv } := by
  simp [child]

end NautyVerified.Proofs.Search

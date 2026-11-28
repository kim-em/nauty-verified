import NautyVerified.Spec.NodeExit
import HexGraphIso.Nauty.Policy.ReturnOrigin

namespace NautyVerified.Spec.SearchInf

open Hex.GraphIso Hex.GraphIso.Nauty

variable {n k : Nat}

/-- An off-path node in `NodeOk` unwinds strictly above itself. -/
theorem nodeOk_unwind_lt {G : Colored n k} {level nc : Nat} {st : Search n}
    (h : NodeOk G false level nc st) (ctx : Ctx n) (inf tl fuel : Nat) :
    ∀ tg s, (node false ctx inf tl fuel level nc st).1 = .unwind tg s → tg < level := by
  have hl : 1 ≤ level := by obtain ⟨⟨_, _, _, h1, _⟩, _⟩ := h; exact h1
  rw [node_eq_generic]
  cases fuel with
  | zero => simp [Generic.node]
  | succ fuel =>
    rw [Generic.node]
    apply Generic.bound_node (fuel := fuel) ?_ ctx tl false level nc st hl
    · intro _
      dsimp only
      intro target short he
      exact node_hlt h ctx tl target short he
    · intro first level numcells tc tv1 cursor cell index st _
      exact Generic.sweep_bound first ctx inf tl fuel (n + 1)
        level numcells tc tv1 cursor cell index st

end NautyVerified.Spec.SearchInf

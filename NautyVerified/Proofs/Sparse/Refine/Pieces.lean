import NautyVerified.Proofs.Sparse.Refine.Access

/-!
# The splitting passes of `refine_sg`, as specifications

`refine_sg` splits cells in three places: the distance pass (`dist`), the
singleton splitter (`trivial`) and the nontrivial splitter (`nontrivial`),
the last two inside the main loop. The count split of one cell, HexGraphIso's
`splitCounts level first d` (`d` the distance flag), is the same C in the
distance pass (`cellD`) and in the nontrivial pass (`cellN`), up to its
temporaries, the hashes and the `continue` after a one-fragment cell.

This file states what each pass does, as propositions proved elsewhere:

- `CountPass`: `cellD` / `cellN` compute `splitCounts`;
- `TrivialPass`: `trivial` computes `splitSingleton`;
- `NontrivialPass`: `nontrivial` computes `splitNontrivial`.

Each runs from memory holding a state `s` exactly (`Mem`, `Rep`, and for
`HITS` the hit counts `s.hits` below `n`), with the scratch the C finds: the
splitter passes start from a state whose marks and stamp are 0, which is
how the C's marks look after `RESETMARKS` (every entry below the stamp).
Every step's memory change is a `Frame`: only `refine_sg`'s written blocks
and new blocks change, every old block keeps its permissions and header.
`Budget s`: `numcells` is at most `n` plus the number of boundaries, which
keeps every `++*numcells` in `int` range.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk)
open NautyVerified.Proofs.Alloc (DynAt Keep)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph splitCounts splitSingleton splitNontrivial)
open Hex.GraphIso.Nauty (IsCell bcount)

attribute [local instance] NautyEnv.sparse

/-- `refine_sg`'s function. -/
abbrev F : function := sparse.fn.refine_sg

/-! ## The count split of one cell -/

/-- One count split of the distance pass, from `v2 = v1 + 1` (after `MASH(v1)`
and `w1 = HITS[lab[v1]]`) to `v1 = j`. -/
abbrev cellD : statement :=
  .Ssequence (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint)))
    (.Ssequence runD
      (.Ssequence
        (sk (.Sifthenelse
          (.Ebinop .Ole (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint)) (tv id.«level») tint)
          (.Ssequence (sk (.Sset id.«v1» (tv id.«v2»))) .Scontinue)
          .Sskip))
        (.Ssequence (sk (.Sset id.«w2» (ci 2000000002 tint)))
          (.Ssequence
            (.Ssequence
              (.Ssequence (sk (.Sset (idOf 717) (.Ecast (tv id.«v2») tint))) (.Sset id.«j» (tv (idOf 717))))
              (.Sset id.«v3» (tv (idOf 717))))
            (.Ssequence minD installD)))))

/-- One count split of the nontrivial pass, from `v2 = v1 + 1` (after
`v1 = HITCELL[i]`, `w1 = HITS[lab[v1]]` and `MASH(v1)`). -/
abbrev cellN : statement :=
  .Ssequence (sk (.Sset id.«v2» (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint)))
    (.Ssequence runN
      (.Ssequence
        (sk (.Sifthenelse
          (.Ebinop .Ole (ix id.«ptn» (.Ebinop .Osub (tv id.«v2») (ci 1 tint) tint)) (tv id.«level») tint)
          .Scontinue
          .Sskip))
        (.Ssequence (sk (.Sset id.«w2» (ci 2000000002 tint)))
          (.Ssequence
            (.Ssequence
              (.Ssequence (sk (.Sset (idOf 754) (.Ecast (tv id.«v2») tint))) (.Sset id.«j» (tv (idOf 754))))
              (.Sset id.«v3» (tv (idOf 754))))
            (.Ssequence minN installN)))))

/-- The cell split of the distance (`true`) or nontrivial (`false`) pass. -/
abbrev cell : Bool → statement
  | true => cellD
  | false => cellN

theorem distLoop_eq : distLoop =
    .Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tv id.«v1») (tv id.«n») tint) .Sskip .Sbreak))
        (.Ssequence
          (sk (.Sifthenelse (.Ebinop .Ole (ix id.«ptn» (tv id.«v1»)) (tv id.«level») tint)
            (.Ssequence (sk (.Sset id.«v1» (.Ebinop .Oadd (tv id.«v1») (ci 1 tint) tint))) .Scontinue)
            .Sskip))
          (.Ssequence (sk (mash (tv id.«v1»)))
            (.Ssequence (sk (.Sset id.«w1» (gix id.«nausparse:work3» (ix id.«lab» (tv id.«v1»)))))
              cellD))))
      .Sskip := rfl

theorem cellLoopN_eq : cellLoopN =
    .Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tv id.«i») (tv id.«hitcells») tint) .Sskip .Sbreak))
        (.Ssequence (sk (.Sset id.«v1» (gix id.«nausparse:work4» (tv id.«i»))))
          (.Ssequence (sk (.Sset id.«w1» (gix id.«nausparse:work3» (ix id.«lab» (tv id.«v1»)))))
            (.Ssequence (sk (mash (tv id.«v1»))) cellN))))
      (sk (.Sset id.«i» (.Ebinop .Oadd (tv id.«i») (ci 1 tint) tint))) := rfl

/-- The temporaries a cell split may assign, besides `longcode` and `nactive`. -/
def cellTemps : List ident :=
  [id.«v1», id.«v2», id.«v3», id.«w1», id.«w2», id.«w3», id.«j», id.«k», id.«l», id.«lj»,
   id.«size», id.«bigpos», id.«bigsize»] ++ (List.range 10).map (fun i => idOf (716 + i)) ++
  (List.range 12).map (fun i => idOf (750 + i))

/-! ## Memory changes -/

/-- A memory change of `refine_sg`: only its written blocks and new blocks
change, every old block keeps its permissions and header and stays valid. -/
structure Frame (L : Loc) (m m' : mem) : Prop where
  unch : Unch m m' (fun z => L.writes z ∨ ¬ Mem.valid_block m z)
  keep : ∀ z, Mem.valid_block m z → Keep m m' z
  valid : ∀ z, Mem.valid_block m z → Mem.valid_block m' z

theorem Frame.refl (L : Loc) (m : mem) : Frame L m m :=
  ⟨Unch.refl _ _, fun z _ => Keep.refl m z, fun _ h => h⟩

theorem Frame.trans {L : Loc} {m₁ m₂ m₃ : mem} (h₁ : Frame L m₁ m₂) (h₂ : Frame L m₂ m₃) :
    Frame L m₁ m₃ :=
  ⟨h₁.unch.trans (h₂.unch.mono fun z hz => hz.imp_right fun h hv => h (h₁.valid z hv)),
    fun z hz => (h₁.keep z hz).trans (h₂.keep z (h₁.valid z hz)),
    fun z hz => h₂.valid z (h₁.valid z hz)⟩

/-- `numcells` is at most `n` plus the boundaries below `n`. -/
def Budget {n : Nat} (level : Nat) (s : RefineSt n) : Prop :=
  s.numcells + n ≤ 2 * n + bcount s.ptn level n

variable {xi : ExternalCalls}

/-! ## The passes -/

/-- What a pass leaves: memory holding `t` exactly, a `Frame`, the temporaries with `t`'s code and queue length,
and the temporaries outside `temps` (and the arguments) unchanged. -/
structure After {n : Nat} (L : Loc) (G : Hex.SparseGraph n) (t : RefineSt n)
    (temps : List ident) (le : temp_env) (m : mem) (le' : temp_env) (m' : mem) (S' : Scr) : Prop where
  mem : Mem m' L G t S'
  rep : Rep L t S'
  frame : Frame L m m'
  tmp : Tmp le' L t
  temps : ∀ x, x ∉ temps → x ∉ args → x ≠ id.longcode → x ≠ id.nactive →
    PTree.get x le' = PTree.get x le

/-- The count split of one nontrivial cell starting at `first`, the code
already hashed with `first` (`MASH(v1)`), `v1 = first` and
`w1 = HITS[lab[first]]`, computes `splitCounts L.level first d s`; `HITS`
and the marks are unchanged. When the cell's first run is the whole cell,
the C leaves by `continue` (in the distance pass with `v1` at the cell's
end), and otherwise normally; in the distance pass `v1` ends at the cell's
end. -/
def CountPass : Prop :=
  ∀ (d : Bool) {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {Q : Post} {le : temp_env} {m : mem}
    {s : RefineSt n} {S : Scr} {first : Nat},
    Ok n L → Mem m L G s S → Rep L s S → Tmp le L (s.hash first) → s.Valid L.level →
    Budget L.level s → s.longcode < 2 ^ 62 →
    (∀ v < n, S.w3[v]! = s.hits[v]!) →
    IsCell s.ptn L.level first (s.cellend[first]! + 1 - first) → first < s.cellend[first]! →
    s.cellend[first]! < n →
    (∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) →
    PTree.get id.«v1» le = some (.Vint (ir first)) →
    PTree.get id.«w1» le = some (.Vint (ir s.hits[s.lab[first]!]!)) →
    (∀ le' m' S', After L G (splitCounts L.level first d s) cellTemps le m le' m' S' →
      S'.w3 = S.w3 → S'.st1 = S.st1 → S'.mk1 = S.mk1 → S'.st2 = S.st2 → S'.mk2 = S.mk2 →
      (d = true → PTree.get id.«v1» le' = some (.Vint (ir (s.cellend[first]! + 1)))) →
      (if Hex.GraphIso.Nauty.Sparse.CountSort.firstRun s.lab s.hits first (s.cellend[first]! + 1) =
          s.cellend[first]! + 1 then Q.cont else Q.normal) E0 empty_env le' m') →
    Wp xi sge F (cell d) Q empty_env le m

/-- The marks and stamp a splitter pass starts from. -/
def Fresh {n : Nat} (s : RefineSt n) : Prop :=
  s.marks = Array.replicate n 0 ∧ s.vmarks = Array.replicate n 0 ∧ s.stamp = 0

/-- The temporaries a splitter pass may assign. -/
def passTemps : List ident :=
  cellTemps ++ [id.«i», id.«ii», id.«ij», id.«ij__1», id.«ij__2», id.«hitcells», id.«splitv»,
    id.«vi», id.«di», id.«isplit»] ++ (List.range 30).map (fun i => idOf (733 + i))

/-- `trivial`, the singleton splitter at `split` (in `isplit`), computes
`splitSingleton`. `s` is the state after the splitter's removal and hash. -/
def TrivialPass : Prop :=
  ∀ {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {Q : Post} {le : temp_env} {m : mem}
    {s : RefineSt n} {S : Scr} {split : Nat},
    Ok n L → Mem m L G s S → Rep L s S → Tmp le L s → s.Valid L.level → Fresh s →
    Budget L.level s → s.longcode < 2 ^ 62 →
    split < n → s.ptn[split]! ≤ L.level → (split = 0 ∨ s.ptn[split - 1]! ≤ L.level) →
    PTree.get id.«isplit» le = some (.Vint (ir split)) →
    (∀ le' m' S', After L G (splitSingleton (.ofGraph G) L.level split s) passTemps le m le' m' S' →
      Q.normal E0 empty_env le' m') →
    Wp xi sge F trivial Q empty_env le m

/-- `nontrivial`, the splitter cell at `split` (in `isplit`), computes
`splitNontrivial`. `s` is the state after the splitter's removal and hash,
its hit counts `HITS` below `n`. -/
def NontrivialPass : Prop :=
  ∀ {n : Nat} {L : Loc} {G : Hex.SparseGraph n} {Q : Post} {le : temp_env} {m : mem}
    {s : RefineSt n} {S : Scr} {split len : Nat},
    Ok n L → Mem m L G s S → Rep L s S → Tmp le L s → s.Valid L.level → Fresh s →
    Budget L.level s → s.longcode < 2 ^ 62 → (∀ v < n, S.w3[v]! = s.hits[v]!) →
    IsCell s.ptn L.level split len → split + len ≤ n → 1 < len →
    PTree.get id.«isplit» le = some (.Vint (ir split)) →
    (∀ le' m' S', After L G (splitNontrivial (.ofGraph G) L.level split s) passTemps le m le' m' S' →
      Q.normal E0 empty_env le' m') →
    Wp xi sge F nontrivial Q empty_env le m

end NautyVerified.Proofs.Sparse.Refine

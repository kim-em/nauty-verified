import NautyVerified.Proofs.Syntax
import NautyVerified.Source.Dense

/-!
# `nextelement`, factored

The Clight of nauty's `nextelement` (nautil.c), as produced by CompCert4Lean's
SimplExpr and SimplLocals, written in named pieces; `body_eq` pins it to the
linked program's `dense.body.nextelement`.

`FIRSTBITNZ(setwd)` is inlined twice (results in temporaries 703 and 704) as a
three-level decision tree whose leaves look up nauty's `leftbit` table.
-/

namespace NautyVerified.Proofs.Nextelement

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open NautyVerified.Source (dense.id.setwd dense.id.set1 dense.id.m dense.id.pos dense.id.w)

namespace id
abbrev setwd : Common.AST.ident := dense.id.setwd
abbrev set1 : Common.AST.ident := dense.id.set1
abbrev m : Common.AST.ident := dense.id.m
abbrev pos : Common.AST.ident := dense.id.pos
abbrev w : Common.AST.ident := dense.id.w
abbrev leftbit : Common.AST.ident := NautyVerified.Source.dense.id.«nautil:leftbit»
end id

/-- The word temporary `FIRSTBITNZ` reads (`setwd` here; `permset` uses `setw`). -/
abbrev sw (x : Common.AST.ident := id.setwd) : expr := .Etempvar x tulong

/-- `x & C`. -/
abbrev tst (c : Int) (x : Common.AST.ident := id.setwd) : expr :=
  .Ebinop .Oand (sw x) (cl c tulong) tulong

/-- `x >> s`. -/
abbrev shr (s : Int) (x : Common.AST.ident := id.setwd) : expr :=
  .Ebinop .Oshr (sw x) (ci s tint) tulong

/-- One leaf of `FIRSTBITNZ`: `r = c + leftbit[idx]`, with SimplExpr's two casts. -/
abbrev leaf (r : Common.AST.ident) (c : Int) (idx : expr) : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence .Sskip
        (.Sset r (.Ecast (.Ebinop .Oadd (ci c tint)
          (.Ederef (.Ebinop .Oadd (.Evar id.leftbit (tarray tint 256)) idx (tptr tint)) tint)
          tint) tint)))
      (.Sset r (.Ecast (.Etempvar r tint) tint)))
    (.Sset r (.Ecast (.Etempvar r tint) tint))

/-- `.Ssequence .Sskip (if a then s1 else s2)`, SimplExpr's shape for `if`. -/
abbrev sif (a : expr) (s1 s2 : statement) : statement := .Ssequence .Sskip (.Sifthenelse a s1 s2)

/-- The inlined `FIRSTBITNZ(x)`, writing its result to `r`. -/
abbrev fbTree (r : Common.AST.ident) (x : Common.AST.ident := id.setwd) : statement :=
  sif (tst 18446744069414584320 x)
    (sif (tst 18446462598732840960 x)
      (sif (tst 18374686479671623680 x)
        (leaf r 0 (.Ebinop .Oand (shr 56 x) (cl 255 tulong) tulong))
        (leaf r 8 (shr 48 x)))
      (sif (tst 280375465082880 x)
        (leaf r 16 (shr 40 x))
        (leaf r 24 (shr 32 x))))
    (sif (tst 4294901760 x)
      (sif (tst 4278190080 x)
        (leaf r 32 (shr 24 x))
        (leaf r 40 (shr 16 x)))
      (sif (tst 65280 x)
        (leaf r 48 (shr 8 x))
        (leaf r 56 (sw x))))

/-- `*(set1 + i)`. -/
abbrev word (i : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.set1 (tptr tulong)) i (tptr tulong)) tulong

/-- `0x7FFFFFFFFFFFFFFF >> s`, nauty's `BITMASK(s)`. -/
abbrev bitmask (s : expr) : expr := .Ebinop .Oshr (cl 9223372036854775807 tulong) s tulong

abbrev retNeg1 : statement := .Ssequence .Sskip (.Sreturn (some (.Eunop .Oneg (ci 1 tint) tint)))

/-- The `m == 1` case. -/
abbrev oneWord : statement :=
  .Ssequence
    (sif (.Ebinop .Olt (.Etempvar id.pos tint) (ci 0 tint) tint)
      (.Ssequence .Sskip (.Sset id.setwd (word (ci 0 tint))))
      (.Ssequence .Sskip (.Sset id.setwd
        (.Ebinop .Oand (word (ci 0 tint)) (bitmask (.Etempvar id.pos tint)) tulong))))
    (sif (.Ebinop .Oeq sw (ci 0 tint) tint)
      retNeg1
      (.Ssequence (fbTree (idOf 703)) (.Sreturn (some (.Etempvar (idOf 703) tint)))))

/-- Initialisation of `w` and `setwd` for the general case. -/
abbrev initW : statement :=
  sif (.Ebinop .Olt (.Etempvar id.pos tint) (ci 0 tint) tint)
    (.Ssequence
      (.Ssequence .Sskip (.Sset id.w (ci 0 tint)))
      (.Ssequence .Sskip (.Sset id.setwd (word (ci 0 tint)))))
    (.Ssequence
      (.Ssequence .Sskip
        (.Sset id.w (.Ebinop .Oshr (.Etempvar id.pos tint) (ci 6 tint) tint)))
      (.Ssequence .Sskip (.Sset id.setwd
        (.Ebinop .Oand (word (.Etempvar id.w tint))
          (bitmask (.Ebinop .Oand (.Etempvar id.pos tint) (ci 63 tint) tint)) tulong))))

/-- Moving to the next word, or returning `-1` past the last. -/
abbrev advance : statement :=
  .Ssequence
    (.Ssequence
      (.Ssequence
        (.Ssequence .Sskip
          (.Sset (idOf 705) (.Ecast (.Ebinop .Oadd (.Etempvar id.w tint) (ci 1 tint) tint) tint)))
        (.Sset id.w (.Etempvar (idOf 705) tint)))
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar (idOf 705) tint) (.Etempvar id.m tint) tint)
        retNeg1 .Sskip))
    (.Ssequence .Sskip (.Sset id.setwd (word (.Etempvar id.w tint))))

/-- The body of the `while` loop. -/
abbrev loopBody : statement :=
  .Ssequence
    (.Ssequence .Sskip .Sskip)
    (.Ssequence
      (sif (.Ebinop .One sw (ci 0 tint) tint)
        (.Ssequence (fbTree (idOf 704))
          (.Sreturn (some (.Ebinop .Oadd (.Ebinop .Oshl (.Etempvar id.w tint) (ci 6 tint) tint)
            (.Etempvar (idOf 704) tint) tint))))
        .Sskip)
      advance)

abbrev body : statement :=
  .Ssequence
    (sif (.Ebinop .Oeq (.Etempvar id.m tint) (ci 1 tint) tint) oneWord .Sskip)
    (.Ssequence initW (.Sloop loopBody .Sskip))

kernel_rfl body_eq : NautyVerified.Source.dense.body.nextelement = body

end NautyVerified.Proofs.Nextelement

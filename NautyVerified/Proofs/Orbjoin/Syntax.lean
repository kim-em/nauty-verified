import NautyVerified.Proofs.Syntax
import NautyVerified.Source.Dense

/-!
# `orbjoin`, factored

The Clight of nauty's `orbjoin` (nautil.c), in named pieces; `body_eq` pins it
to `dense.body.orbjoin`.
-/

namespace NautyVerified.Proofs.Orbjoin

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open NautyVerified.Source

namespace id
abbrev orbits : Common.AST.ident := dense.id.orbits
abbrev map : Common.AST.ident := dense.id.map
abbrev n : Common.AST.ident := dense.id.n
abbrev i : Common.AST.ident := dense.id.i
abbrev j1 : Common.AST.ident := dense.id.j1
abbrev j2 : Common.AST.ident := dense.id.j2
abbrev t : Common.AST.ident := idOf 703
end id

/-- `.Ssequence .Sskip s`, SimplExpr's shape for a statement. -/
abbrev sk (s : statement) : statement := .Ssequence .Sskip s

abbrev tv (x : Common.AST.ident) : expr := .Etempvar x tint

/-- `orbits[e]`. -/
abbrev orb (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.orbits (tptr tint)) e (tptr tint)) tint

/-- `map[e]`. -/
abbrev mapAt (e : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar id.map (tptr tint)) e (tptr tint)) tint

/-- `while (orbits[j] != j) j = orbits[j];` -/
abbrev chase (j : Common.AST.ident) : statement :=
  .Sloop
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .One (orb (tv j)) (tv j) tint) .Sskip .Sbreak))
      (sk (.Sset j (orb (tv j)))))
    .Sskip

/-- Link the roots `j1` and `j2`. -/
abbrev link : statement :=
  sk (.Sifthenelse (.Ebinop .Olt (tv id.j1) (tv id.j2) tint)
    (sk (.Sassign (orb (tv id.j2)) (tv id.j1)))
    (sk (.Sifthenelse (.Ebinop .Ogt (tv id.j1) (tv id.j2) tint)
      (sk (.Sassign (orb (tv id.j1)) (tv id.j2)))
      .Sskip)))

/-- The body of the first loop, for `i < n`. -/
abbrev joinStep : statement :=
  sk (.Sifthenelse (.Ebinop .One (mapAt (tv id.i)) (tv id.i) tint)
    (.Ssequence
      (sk (.Sset id.j1 (orb (tv id.i))))
      (.Ssequence (chase id.j1)
        (.Ssequence
          (sk (.Sset id.j2 (orb (mapAt (tv id.i)))))
          (.Ssequence (chase id.j2) link))))
    .Sskip)

/-- `for (i = 0; i < n; ++i) body` as SimplExpr writes it. -/
abbrev forI (body : statement) : statement :=
  .Ssequence
    (sk (.Sset id.i (ci 0 tint)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (tv id.i) (tv id.n) tint) .Sskip .Sbreak))
        body)
      (sk (.Sset id.i (.Ebinop .Oadd (tv id.i) (ci 1 tint) tint))))

/-- The body of the second loop: compress `i`, counting roots in `j1`. -/
abbrev compressStep : statement :=
  .Ssequence
    (.Ssequence
      (sk (.Sset id.t (.Ecast (orb (orb (tv id.i))) tint)))
      (.Sassign (orb (tv id.i)) (tv id.t)))
    (.Sifthenelse (.Ebinop .Oeq (tv id.t) (tv id.i) tint)
      (sk (.Sset id.j1 (.Ebinop .Oadd (tv id.j1) (ci 1 tint) tint)))
      .Sskip)

abbrev body : statement :=
  .Ssequence
    (forI joinStep)
    (.Ssequence
      (sk (.Sset id.j1 (ci 0 tint)))
      (.Ssequence
        (forI compressStep)
        (sk (.Sreturn (some (tv id.j1))))))

kernel_rfl body_eq : NautyVerified.Source.dense.body.orbjoin = body

end NautyVerified.Proofs.Orbjoin

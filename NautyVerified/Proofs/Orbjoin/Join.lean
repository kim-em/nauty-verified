import NautyVerified.Proofs.Orbjoin.Chase

/-!
# The first loop of `orbjoin`

`wp_joinStep`: one iteration of nauty's first `orbjoin` loop, for vertex `i`,
turns the `orbits` array from `o` into `join map n o i`, HexGraphIso's step.
-/

namespace NautyVerified.Proofs.Orbjoin

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open Hex.GraphIso.Nauty.Orbit

variable {xi : ExternalCalls}

/-- The state `orbjoin` works in: its pointer and length arguments in
temporaries, the `orbits` array (holding a descending forest `o`) and the
`map` array (holding `mp`) in different blocks. -/
structure Frame (m : mem) (le : temp_env) (bo : block) (ofs : ptrofs) (bm : block)
    (mofs : ptrofs) (o mp : Array Nat) (n : Nat) : Prop where
  horb : PTree.get id.orbits le = some (.Vptr bo ofs)
  hmap : PTree.get id.map le = some (.Vptr bm mofs)
  hn : PTree.get id.n le = some (.Vint (ir n))
  arr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n
  marr : ArrayAt m .Mint32 bm (intOfZ (Ptrofs.unsigned mofs)) (ints mp) n
  hne : bo ≠ bm
  nlt : n < 2147483648
  mlt : ∀ i < n, mp[i]! < n
  desc : Descending o n

/-- `p[a] = x;` for an `int *` temporary `p` and an index `a` holding `c < n`:
the array gets `x` at `c`, and every other block is unchanged. -/
theorem wp_store {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {bo : block}
    {ofs : ptrofs} {o : Array Nat} {n : Nat}
    (harr : ArrayAt m .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (ints o) n)
    (hn : n < 2147483648) (p : Common.AST.ident) (hp : PTree.get p le = some (.Vptr bo ofs))
    (a : expr) (c : Nat) (hc : c < n)
    (ha : Exec.evalExpr ge e le m a = some (.Vint (ir c))) (hty : typeof a = tint)
    (rhs : expr) (x : Int) (hrhs : Exec.evalExpr ge e le m rhs = some (.Vint (ir x)))
    (hrty : typeof rhs = tint)
    (hQ : ∀ m', ArrayAt m' .Mint32 bo (intOfZ (Ptrofs.unsigned ofs)) (upd (ints o) c (.Vint (ir x))) n →
      (∀ chunk b' ofs', b' ≠ bo → Mem.load chunk m' b' ofs' = Mem.load chunk m b' ofs') →
      (∀ {chunk' b' base' vals' n'}, ArrayAt m chunk' b' base' vals' n' → b' ≠ bo →
        ArrayAt m' chunk' b' base' vals' n') →
      Q.normal E0 e le m') :
    Wp xi ge f (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar p (tptr tint)) a (tptr tint)) tint) rhs)
      Q e le m := by
  have haddr : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr
      (Cfrontend.Ctypes.sizeof ge.genv_cenv tint)) (Ptrofs.of_ints (ir c)))) =
      elemOfs .Mint32 (intOfZ (Ptrofs.unsigned ofs)) c := by
    apply addr_elem ofs _ .Mint32 rfl rfl (by omega)
    have hf := harr.fits
    have h4 : csize .Mint32 = 4 := rfl
    rw [h4] at hf ⊢
    omega
  obtain ⟨m', hst, harr', hfar⟩ := store_array harr hc (.Vint (ir x)) rfl
  apply wp_assign_eval
  simp only [Exec.evalLvalue, Exec.evalExpr, hp, ha, hty, hrhs, hrty]
  simp only [typeof, cop, Exec.assignLoc, Cfrontend.Ctypes.access_mode]
  show match Mem.store .Mint32 m bo (Ptrofs.unsigned _) _ with
    | some m' => Q.normal E0 e le m' | none => False
  rw [haddr, hst]
  refine hQ m' harr' (fun chunk b' ofs' hb => hfar chunk b' ofs' (.inl hb)) ?_
  intro chunk' b' base' vals' n' h hb
  exact h.store_away hst (.inl hb)

end NautyVerified.Proofs.Orbjoin

import NautyVerified.Proofs.Sparse.Refine.Syntax
import NautyVerified.Proofs.Sparse.Refine.Marks2
import NautyVerified.Proofs.Sparse.Refine.Model
import NautyVerified.Proofs.Sparse.Arr
import NautyVerified.Proofs.Set.Add
import NautyVerified.Proofs.Nextelement.Leftbit

/-!
# The state `refine_sg` works in

`Loc`: where `refine_sg`'s arguments, the graph's arrays, its four work
arrays (`work1` = `CELLSTART`, `work2` = `ACTIVE`, `work3` = `HITS`,
`work4` = `HITCELL`) and its two mark arrays live, once allocated. `Ok`: the
facts about them no step changes. `Scr`: the contents of the scratch
arrays (`work1`, `work2`, `work4` as values, `work3` as naturals, both mark
arrays with their stamps) and the active set's words. `Mem m L G t S`:
memory holds the graph `G`, HexGraphIso's `lab`, `ptn`, `numcells` of `t`,
the active words of `S` (representing `t.active`), the scratch `S`, the
tables `refine_sg` reads. `Rep L t S`: the scratch represents `t`'s
`CELLSTART` and queue. `Tmp le L t`: the temporaries hold the arguments,
`t`'s `longcode` and the queue length `nactive`.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Alloc (DynAt Keep)
open NautyVerified.Proofs.Set (longs BitTable)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph)

attribute [local instance] NautyEnv.sparse

/-- `refine_sg`'s argument pointers, the graph's arrays, its work and mark
arrays (blocks and capacities) and its scalar arguments. -/
structure Loc where
  bsg : block
  sofs : ptrofs
  bv : block
  vo : ptrofs
  bd : block
  dofs : ptrofs
  be : block
  eo : ptrofs
  bl : block
  lofs : ptrofs
  bp : block
  pofs : ptrofs
  bn : block
  nofs : ptrofs
  bc : block
  cofs : ptrofs
  ba : block
  aofs : ptrofs
  bk : block
  kofs : ptrofs
  b1 : block
  c1 : Nat
  b2 : block
  c2 : Nat
  b3 : block
  c3 : Nat
  b4 : block
  c4 : Nat
  mb1 : block
  mc1 : Nat
  mb2 : block
  mc2 : Nat
  level : Nat
  M : Nat

namespace Loc

variable (L : Loc)

abbrev lb : Int := intOfZ (Ptrofs.unsigned L.lofs)
abbrev pb : Int := intOfZ (Ptrofs.unsigned L.pofs)
abbrev nb : Int := intOfZ (Ptrofs.unsigned L.nofs)
abbrev ab : Int := intOfZ (Ptrofs.unsigned L.aofs)
abbrev kb : Int := intOfZ (Ptrofs.unsigned L.kofs)

/-- The blocks `refine_sg` writes once its arrays are allocated, in order. -/
def wblocks : List block :=
  [L.bl, L.bp, L.bn, L.ba, L.bk, L.b1, L.b2, L.b3, L.b4, L.mb1, L.mb2,
   Sparse.Block.vmark1Val, Block.vmark2Val]

/-- The blocks it reads and does not write. -/
def rblocks : List block :=
  [L.bsg, L.bv, L.bd, L.be,
   Sparse.Block.work1, Sparse.Block.work1Sz, Block.work2, Block.work2Sz, Block.work3,
   Block.work3Sz, Block.work4, Block.work4Sz, Sparse.Block.vmark1, Sparse.Block.vmark1Sz,
   Block.vmark2, Block.vmark2Sz, Block.bit, (NautyEnv.leftbit : block)]

/-- The blocks a step of `refine_sg` may write. -/
def writes (z : block) : Prop := z ∈ L.wblocks

end Loc

/-- Entries `i < j` of a list of pairwise distinct blocks differ. -/
theorem pw_ne {l : List block} (h : l.Pairwise (· ≠ ·)) (i j : Nat) (hij : i < j)
    (hj : j < l.length) : l[i]'(Nat.lt_trans hij hj) ≠ l[j] := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => exact h.1 _ (List.getElem_mem _)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih h.2 i j (by omega) (by simpa using hj)

/-- The facts about `refine_sg`'s locations that no step changes. -/
structure Ok (n : Nat) (L : Loc) : Prop where
  wdistinct : L.wblocks.Pairwise (· ≠ ·)
  rw : ∀ z ∈ L.rblocks, ¬ L.writes z
  n0 : 0 < n
  nlt : n < 1073741824
  nM : n ≤ 64 * L.M
  M1 : 0 < L.M
  Mlt : L.M < 33554432
  levlt : L.level < 2147483648
  c1 : n ≤ L.c1
  c2 : n ≤ L.c2
  c3 : n ≤ L.c3
  c4 : n ≤ L.c4
  mc1 : n ≤ L.mc1
  mc2 : n ≤ L.mc2

/-- The contents of `refine_sg`'s scratch arrays and of the active set. -/
structure Scr where
  w1 : Nat → val
  w2 : Nat → val
  w3 : Array Nat
  w4 : Nat → val
  st1 : Nat
  mk1 : Nat → Int
  st2 : Nat
  mk2 : Nat → Int
  aw : Nat → Lib.Integers.int64

/-- Memory holds the graph, `t`'s labelling, partition, cell count and active
set (through `S.aw`), the scratch `S` and the tables. -/
structure Mem {n : Nat} (m : mem) (L : Loc) (G : Hex.SparseGraph n) (t : RefineSt n) (S : Scr) :
    Prop where
  graph : SparseGraphAt m L.bsg L.sofs G L.bv L.vo L.bd L.dofs L.be L.eo
  lab : ArrayAt m .Mint32 L.bl L.lb (ints t.lab) n
  ptn : ArrayAt m .Mint32 L.bp L.pb (ints t.ptn) n
  nc : ArrayAt m .Mint32 L.bn L.nb (fun _ => .Vint (ir t.numcells)) 1
  act : ArrayAt m .Mint64 L.ba L.ab (longs S.aw) L.M
  actRep : SetRep (fun w => bv64 (S.aw w)) L.M t.active
  code : ∃ kv, ArrayAt m .Mint32 L.bk L.kb kv 1
  d1 : DynAt m Sparse.Block.work1 Sparse.Block.work1Sz 4 L.c1 L.b1
  d2 : DynAt m Block.work2 Block.work2Sz 4 L.c2 L.b2
  d3 : DynAt m Block.work3 Block.work3Sz 4 L.c3 L.b3
  d4 : DynAt m Block.work4 Block.work4Sz 4 L.c4 L.b4
  w1 : ArrayAt m .Mint32 L.b1 0 S.w1 L.c1
  w2 : ArrayAt m .Mint32 L.b2 0 S.w2 L.c2
  w3 : ArrayAt m .Mint32 L.b3 0 (ints S.w3) n
  w4 : ArrayAt m .Mint32 L.b4 0 S.w4 L.c4
  k1 : MarksAt m L.mc1 L.mb1 S.st1 S.mk1
  k2 : Marks2.MarksAt m L.mc2 L.mb2 S.st2 S.mk2
  bit : BitTable m Block.bit
  left : LeftbitTable m

/-- The scratch holds `t`'s cell starts at every vertex and its queue, and
`HITS` holds naturals of `int` range below `n`. -/
structure Rep {n : Nat} (L : Loc) (t : RefineSt n) (S : Scr) : Prop where
  starts : ∀ v < n, S.w1 v = .Vint (ir t.cellstart[v]!)
  queue : ∀ i < t.queue.size, S.w2 i = .Vint (ir t.queue[i]!)
  w3size : S.w3.size = n
  w3small : ∀ i < n, S.w3[i]! < 2147483648

/-- The temporaries hold `refine_sg`'s arguments, the graph's arrays and `t`'s
code and queue length. -/
structure Tmp {n : Nat} (le : temp_env) (L : Loc) (t : RefineSt n) : Prop where
  g : PTree.get id.g le = some (.Vptr L.bsg L.sofs)
  lab : PTree.get id.lab le = some (.Vptr L.bl L.lofs)
  ptn : PTree.get id.ptn le = some (.Vptr L.bp L.pofs)
  level : PTree.get id.level le = some (.Vint (ir L.level))
  numcells : PTree.get id.numcells le = some (.Vptr L.bn L.nofs)
  active : PTree.get id.active le = some (.Vptr L.ba L.aofs)
  code : PTree.get id.code le = some (.Vptr L.bk L.kofs)
  m : PTree.get id.m le = some (.Vint (ir L.M))
  n : PTree.get id.n le = some (.Vint (ir n))
  v : PTree.get id.v le = some (.Vptr L.bv L.vo)
  d : PTree.get id.d le = some (.Vptr L.bd L.dofs)
  e : PTree.get id.e le = some (.Vptr L.be L.eo)
  longcode : PTree.get id.longcode le = some (.Vlong (lr t.longcode))
  nactive : PTree.get id.nactive le = some (.Vint (ir t.queue.size))

/-- The temporaries no statement of `refine_sg` assigns after its entry. -/
def args : List Common.AST.ident :=
  [id.g, id.lab, id.ptn, id.level, id.numcells, id.active, id.code, id.m, id.n, id.v, id.d, id.e]

/-- `Tmp` survives assignments to temporaries other than the arguments,
`longcode` and `nactive`. -/
theorem Tmp.temps {n : Nat} {le le' : temp_env} {L : Loc} {t : RefineSt n} (h : Tmp le L t)
    (hle : ∀ x, x ∈ args ∨ x = id.longcode ∨ x = id.nactive →
      PTree.get x le' = PTree.get x le) : Tmp le' L t where
  g := by rw [hle _ (.inl (by simp [args]))]; exact h.g
  lab := by rw [hle _ (.inl (by simp [args]))]; exact h.lab
  ptn := by rw [hle _ (.inl (by simp [args]))]; exact h.ptn
  level := by rw [hle _ (.inl (by simp [args]))]; exact h.level
  numcells := by rw [hle _ (.inl (by simp [args]))]; exact h.numcells
  active := by rw [hle _ (.inl (by simp [args]))]; exact h.active
  code := by rw [hle _ (.inl (by simp [args]))]; exact h.code
  m := by rw [hle _ (.inl (by simp [args]))]; exact h.m
  n := by rw [hle _ (.inl (by simp [args]))]; exact h.n
  v := by rw [hle _ (.inl (by simp [args]))]; exact h.v
  d := by rw [hle _ (.inl (by simp [args]))]; exact h.d
  e := by rw [hle _ (.inl (by simp [args]))]; exact h.e
  longcode := by rw [hle _ (.inr (.inl rfl))]; exact h.longcode
  nactive := by rw [hle _ (.inr (.inr rfl))]; exact h.nactive

/-- Assigning a temporary other than the arguments, `longcode` and `nactive`
keeps `Tmp`; the side condition closes by `decide` for concrete names. -/
theorem Tmp.set {n : Nat} {le : temp_env} {L : Loc} {t : RefineSt n} (h : Tmp le L t)
    {x : Common.AST.ident} (v : val)
    (hx : x ∉ args ∧ x ≠ id.longcode ∧ x ≠ id.nactive) :
    Tmp (PTree.set x v le) L t :=
  h.temps fun y hy => by
    apply temps_gso
    rintro rfl
    rcases hy with hy | hy | hy
    · exact hx.1 hy
    · exact hx.2.1 hy
    · exact hx.2.2 hy

/-- `Tmp` survives a change of temporaries outside `ws`, none of which is an
argument, `longcode` or `nactive` (closed by `decide` for concrete lists). -/
theorem Tmp.frame {n : Nat} {le le' : temp_env} {L : Loc} {t : RefineSt n} (h : Tmp le L t)
    {ws : List Common.AST.ident} (ho : ∀ x, x ∉ ws → PTree.get x le' = PTree.get x le)
    (hws : ∀ x ∈ ws, x ∉ args ∧ x ≠ id.longcode ∧ x ≠ id.nactive) : Tmp le' L t :=
  h.temps fun x hx => ho x fun hm => by
    have := hws x hm
    rcases hx with hx | hx | hx
    · exact this.1 hx
    · exact this.2.1 hx
    · exact this.2.2 hx

/-- An exact queue has at most `n` entries. -/
theorem queue_size_le {n : Nat} {active : Hex.GraphIso.Nauty.VSet n} {queue : Array Nat}
    (h : Hex.GraphIso.Nauty.Sparse.ActiveQueue active queue) : queue.size ≤ n := by
  have hs := List.Nodup.length_le_of_subset h.nodup (l₂ := List.range n)
    fun x hx => List.mem_range.2 (h.bound hx)
  simpa using hs

/-- `Tmp` depends only on `t`'s `longcode` and queue length. -/
theorem Tmp.congr {n : Nat} {le : temp_env} {L : Loc} {t t' : RefineSt n} (h : Tmp le L t)
    (hc : t'.longcode = t.longcode) (hq : t'.queue.size = t.queue.size) : Tmp le L t' :=
  { h with
    longcode := by rw [hc]; exact h.longcode
    nactive := by rw [hq]; exact h.nactive }

/-- `Mem` depends only on `t`'s `lab`, `ptn`, `numcells` and `active`. -/
theorem Mem.congr {n : Nat} {m : mem} {L : Loc} {G : Hex.SparseGraph n} {t t' : RefineSt n}
    {S : Scr} (h : Mem m L G t S) (hl : t'.lab = t.lab) (hp : t'.ptn = t.ptn)
    (hn : t'.numcells = t.numcells) (ha : t'.active = t.active) : Mem m L G t' S :=
  { h with
    lab := by rw [hl]; exact h.lab
    ptn := by rw [hp]; exact h.ptn
    nc := by rw [hn]; exact h.nc
    actRep := by rw [ha]; exact h.actRep }

/-- Writing `lab`. -/
theorem Mem.setLab {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.bl)) (t' : RefineSt n) (harr : ArrayAt m' .Mint32 L.bl L.lb (ints t'.lab) n)
    (hp : t'.ptn = t.ptn) (hn : t'.numcells = t.numcells) (ha : t'.active = t.active) :
    Mem m' L G t' S where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := harr
  ptn := hp ▸ h.ptn.unch hu (Ne.symm (pw_ne hok.wdistinct 0 1 (by decide) (by simp [Loc.wblocks])))
  nc := hn ▸ h.nc.unch hu (Ne.symm (pw_ne hok.wdistinct 0 2 (by decide) (by simp [Loc.wblocks])))
  act := h.act.unch hu (Ne.symm (pw_ne hok.wdistinct 0 3 (by decide) (by simp [Loc.wblocks])))
  actRep := ha ▸ h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (Ne.symm (pw_ne hok.wdistinct 0 4 (by decide) (by simp [Loc.wblocks])))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 0 5 (by decide) (by simp [Loc.wblocks]))))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 0 6 (by decide) (by simp [Loc.wblocks]))))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 0 7 (by decide) (by simp [Loc.wblocks]))))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 0 8 (by decide) (by simp [Loc.wblocks]))))
  w1 := h.w1.unch hu (Ne.symm (pw_ne hok.wdistinct 0 5 (by decide) (by simp [Loc.wblocks])))
  w2 := h.w2.unch hu (Ne.symm (pw_ne hok.wdistinct 0 6 (by decide) (by simp [Loc.wblocks])))
  w3 := h.w3.unch hu (Ne.symm (pw_ne hok.wdistinct 0 7 (by decide) (by simp [Loc.wblocks])))
  w4 := h.w4.unch hu (Ne.symm (pw_ne hok.wdistinct 0 8 (by decide) (by simp [Loc.wblocks])))
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 0 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 0 9 (by decide) (by simp [Loc.wblocks]))))
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 0 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 0 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing `ptn`. -/
theorem Mem.setPtn {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.bp)) (t' : RefineSt n) (harr : ArrayAt m' .Mint32 L.bp L.pb (ints t'.ptn) n)
    (hl : t'.lab = t.lab) (hn : t'.numcells = t.numcells) (ha : t'.active = t.active) :
    Mem m' L G t' S where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := hl ▸ h.lab.unch hu (pw_ne hok.wdistinct 0 1 (by decide) (by simp [Loc.wblocks]))
  ptn := harr
  nc := hn ▸ h.nc.unch hu (Ne.symm (pw_ne hok.wdistinct 1 2 (by decide) (by simp [Loc.wblocks])))
  act := h.act.unch hu (Ne.symm (pw_ne hok.wdistinct 1 3 (by decide) (by simp [Loc.wblocks])))
  actRep := ha ▸ h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (Ne.symm (pw_ne hok.wdistinct 1 4 (by decide) (by simp [Loc.wblocks])))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 1 5 (by decide) (by simp [Loc.wblocks]))))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 1 6 (by decide) (by simp [Loc.wblocks]))))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 1 7 (by decide) (by simp [Loc.wblocks]))))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 1 8 (by decide) (by simp [Loc.wblocks]))))
  w1 := h.w1.unch hu (Ne.symm (pw_ne hok.wdistinct 1 5 (by decide) (by simp [Loc.wblocks])))
  w2 := h.w2.unch hu (Ne.symm (pw_ne hok.wdistinct 1 6 (by decide) (by simp [Loc.wblocks])))
  w3 := h.w3.unch hu (Ne.symm (pw_ne hok.wdistinct 1 7 (by decide) (by simp [Loc.wblocks])))
  w4 := h.w4.unch hu (Ne.symm (pw_ne hok.wdistinct 1 8 (by decide) (by simp [Loc.wblocks])))
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 1 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 1 9 (by decide) (by simp [Loc.wblocks]))))
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 1 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 1 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing `*numcells`. -/
theorem Mem.setNc {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.bn)) (t' : RefineSt n) (harr : ArrayAt m' .Mint32 L.bn L.nb (fun _ => .Vint (ir t'.numcells)) 1)
    (hl : t'.lab = t.lab) (hp : t'.ptn = t.ptn) (ha : t'.active = t.active) :
    Mem m' L G t' S where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := hl ▸ h.lab.unch hu (pw_ne hok.wdistinct 0 2 (by decide) (by simp [Loc.wblocks]))
  ptn := hp ▸ h.ptn.unch hu (pw_ne hok.wdistinct 1 2 (by decide) (by simp [Loc.wblocks]))
  nc := harr
  act := h.act.unch hu (Ne.symm (pw_ne hok.wdistinct 2 3 (by decide) (by simp [Loc.wblocks])))
  actRep := ha ▸ h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (Ne.symm (pw_ne hok.wdistinct 2 4 (by decide) (by simp [Loc.wblocks])))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 2 5 (by decide) (by simp [Loc.wblocks]))))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 2 6 (by decide) (by simp [Loc.wblocks]))))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 2 7 (by decide) (by simp [Loc.wblocks]))))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 2 8 (by decide) (by simp [Loc.wblocks]))))
  w1 := h.w1.unch hu (Ne.symm (pw_ne hok.wdistinct 2 5 (by decide) (by simp [Loc.wblocks])))
  w2 := h.w2.unch hu (Ne.symm (pw_ne hok.wdistinct 2 6 (by decide) (by simp [Loc.wblocks])))
  w3 := h.w3.unch hu (Ne.symm (pw_ne hok.wdistinct 2 7 (by decide) (by simp [Loc.wblocks])))
  w4 := h.w4.unch hu (Ne.symm (pw_ne hok.wdistinct 2 8 (by decide) (by simp [Loc.wblocks])))
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 2 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 2 9 (by decide) (by simp [Loc.wblocks]))))
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 2 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 2 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing the active set's words. -/
theorem Mem.setAct {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.ba)) (t' : RefineSt n) (aw : Nat → Lib.Integers.int64)
    (harr : ArrayAt m' .Mint64 L.ba L.ab (longs aw) L.M) (hrep : SetRep (fun w => bv64 (aw w)) L.M t'.active)
    (hl : t'.lab = t.lab) (hp : t'.ptn = t.ptn) (hn : t'.numcells = t.numcells) :
    Mem m' L G t' { S with aw } where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := hl ▸ h.lab.unch hu (pw_ne hok.wdistinct 0 3 (by decide) (by simp [Loc.wblocks]))
  ptn := hp ▸ h.ptn.unch hu (pw_ne hok.wdistinct 1 3 (by decide) (by simp [Loc.wblocks]))
  nc := hn ▸ h.nc.unch hu (pw_ne hok.wdistinct 2 3 (by decide) (by simp [Loc.wblocks]))
  act := harr
  actRep := hrep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (Ne.symm (pw_ne hok.wdistinct 3 4 (by decide) (by simp [Loc.wblocks])))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 3 5 (by decide) (by simp [Loc.wblocks]))))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 3 6 (by decide) (by simp [Loc.wblocks]))))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 3 7 (by decide) (by simp [Loc.wblocks]))))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 3 8 (by decide) (by simp [Loc.wblocks]))))
  w1 := h.w1.unch hu (Ne.symm (pw_ne hok.wdistinct 3 5 (by decide) (by simp [Loc.wblocks])))
  w2 := h.w2.unch hu (Ne.symm (pw_ne hok.wdistinct 3 6 (by decide) (by simp [Loc.wblocks])))
  w3 := h.w3.unch hu (Ne.symm (pw_ne hok.wdistinct 3 7 (by decide) (by simp [Loc.wblocks])))
  w4 := h.w4.unch hu (Ne.symm (pw_ne hok.wdistinct 3 8 (by decide) (by simp [Loc.wblocks])))
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 3 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 3 9 (by decide) (by simp [Loc.wblocks]))))
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 3 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 3 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing `*code`. -/
theorem Mem.setCode {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.bk)) (kv : Nat → val) (harr : ArrayAt m' .Mint32 L.bk L.kb kv 1) :
    Mem m' L G t S where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := h.lab.unch hu (pw_ne hok.wdistinct 0 4 (by decide) (by simp [Loc.wblocks]))
  ptn := h.ptn.unch hu (pw_ne hok.wdistinct 1 4 (by decide) (by simp [Loc.wblocks]))
  nc := h.nc.unch hu (pw_ne hok.wdistinct 2 4 (by decide) (by simp [Loc.wblocks]))
  act := h.act.unch hu (pw_ne hok.wdistinct 3 4 (by decide) (by simp [Loc.wblocks]))
  actRep := h.actRep
  code := ⟨kv, harr⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 4 5 (by decide) (by simp [Loc.wblocks]))))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 4 6 (by decide) (by simp [Loc.wblocks]))))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 4 7 (by decide) (by simp [Loc.wblocks]))))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 4 8 (by decide) (by simp [Loc.wblocks]))))
  w1 := h.w1.unch hu (Ne.symm (pw_ne hok.wdistinct 4 5 (by decide) (by simp [Loc.wblocks])))
  w2 := h.w2.unch hu (Ne.symm (pw_ne hok.wdistinct 4 6 (by decide) (by simp [Loc.wblocks])))
  w3 := h.w3.unch hu (Ne.symm (pw_ne hok.wdistinct 4 7 (by decide) (by simp [Loc.wblocks])))
  w4 := h.w4.unch hu (Ne.symm (pw_ne hok.wdistinct 4 8 (by decide) (by simp [Loc.wblocks])))
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 4 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 4 9 (by decide) (by simp [Loc.wblocks]))))
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 4 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 4 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing `work1`. -/
theorem Mem.setW1 {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.b1)) (hk : Keep m m' L.b1) (w : Nat → val)
    (harr : ArrayAt m' .Mint32 L.b1 0 w L.c1) :
    Mem m' L G t { S with w1 := w } where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := h.lab.unch hu (pw_ne hok.wdistinct 0 5 (by decide) (by simp [Loc.wblocks]))
  ptn := h.ptn.unch hu (pw_ne hok.wdistinct 1 5 (by decide) (by simp [Loc.wblocks]))
  nc := h.nc.unch hu (pw_ne hok.wdistinct 2 5 (by decide) (by simp [Loc.wblocks]))
  act := h.act.unch hu (pw_ne hok.wdistinct 3 5 (by decide) (by simp [Loc.wblocks]))
  actRep := h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (pw_ne hok.wdistinct 4 5 (by decide) (by simp [Loc.wblocks]))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => hk)
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 5 6 (by decide) (by simp [Loc.wblocks]))))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 5 7 (by decide) (by simp [Loc.wblocks]))))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 5 8 (by decide) (by simp [Loc.wblocks]))))
  w1 := harr
  w2 := h.w2.unch hu (Ne.symm (pw_ne hok.wdistinct 5 6 (by decide) (by simp [Loc.wblocks])))
  w3 := h.w3.unch hu (Ne.symm (pw_ne hok.wdistinct 5 7 (by decide) (by simp [Loc.wblocks])))
  w4 := h.w4.unch hu (Ne.symm (pw_ne hok.wdistinct 5 8 (by decide) (by simp [Loc.wblocks])))
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 5 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 5 9 (by decide) (by simp [Loc.wblocks]))))
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 5 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 5 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing `work2`. -/
theorem Mem.setW2 {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.b2)) (hk : Keep m m' L.b2) (w : Nat → val)
    (harr : ArrayAt m' .Mint32 L.b2 0 w L.c2) :
    Mem m' L G t { S with w2 := w } where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := h.lab.unch hu (pw_ne hok.wdistinct 0 6 (by decide) (by simp [Loc.wblocks]))
  ptn := h.ptn.unch hu (pw_ne hok.wdistinct 1 6 (by decide) (by simp [Loc.wblocks]))
  nc := h.nc.unch hu (pw_ne hok.wdistinct 2 6 (by decide) (by simp [Loc.wblocks]))
  act := h.act.unch hu (pw_ne hok.wdistinct 3 6 (by decide) (by simp [Loc.wblocks]))
  actRep := h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (pw_ne hok.wdistinct 4 6 (by decide) (by simp [Loc.wblocks]))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 5 6 (by decide) (by simp [Loc.wblocks])))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => hk)
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 6 7 (by decide) (by simp [Loc.wblocks]))))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 6 8 (by decide) (by simp [Loc.wblocks]))))
  w1 := h.w1.unch hu (pw_ne hok.wdistinct 5 6 (by decide) (by simp [Loc.wblocks]))
  w2 := harr
  w3 := h.w3.unch hu (Ne.symm (pw_ne hok.wdistinct 6 7 (by decide) (by simp [Loc.wblocks])))
  w4 := h.w4.unch hu (Ne.symm (pw_ne hok.wdistinct 6 8 (by decide) (by simp [Loc.wblocks])))
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 6 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 6 9 (by decide) (by simp [Loc.wblocks]))))
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 6 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 6 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing `work3`. -/
theorem Mem.setW3 {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.b3)) (hk : Keep m m' L.b3) (w : Array Nat)
    (harr : ArrayAt m' .Mint32 L.b3 0 (ints w) n) :
    Mem m' L G t { S with w3 := w } where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := h.lab.unch hu (pw_ne hok.wdistinct 0 7 (by decide) (by simp [Loc.wblocks]))
  ptn := h.ptn.unch hu (pw_ne hok.wdistinct 1 7 (by decide) (by simp [Loc.wblocks]))
  nc := h.nc.unch hu (pw_ne hok.wdistinct 2 7 (by decide) (by simp [Loc.wblocks]))
  act := h.act.unch hu (pw_ne hok.wdistinct 3 7 (by decide) (by simp [Loc.wblocks]))
  actRep := h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (pw_ne hok.wdistinct 4 7 (by decide) (by simp [Loc.wblocks]))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 5 7 (by decide) (by simp [Loc.wblocks])))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 6 7 (by decide) (by simp [Loc.wblocks])))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => hk)
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (Ne.symm (pw_ne hok.wdistinct 7 8 (by decide) (by simp [Loc.wblocks]))))
  w1 := h.w1.unch hu (pw_ne hok.wdistinct 5 7 (by decide) (by simp [Loc.wblocks]))
  w2 := h.w2.unch hu (pw_ne hok.wdistinct 6 7 (by decide) (by simp [Loc.wblocks]))
  w3 := harr
  w4 := h.w4.unch hu (Ne.symm (pw_ne hok.wdistinct 7 8 (by decide) (by simp [Loc.wblocks])))
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 7 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 7 9 (by decide) (by simp [Loc.wblocks]))))
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 7 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 7 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing `work4`. -/
theorem Mem.setW4 {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.b4)) (hk : Keep m m' L.b4) (w : Nat → val)
    (harr : ArrayAt m' .Mint32 L.b4 0 w L.c4) :
    Mem m' L G t { S with w4 := w } where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := h.lab.unch hu (pw_ne hok.wdistinct 0 8 (by decide) (by simp [Loc.wblocks]))
  ptn := h.ptn.unch hu (pw_ne hok.wdistinct 1 8 (by decide) (by simp [Loc.wblocks]))
  nc := h.nc.unch hu (pw_ne hok.wdistinct 2 8 (by decide) (by simp [Loc.wblocks]))
  act := h.act.unch hu (pw_ne hok.wdistinct 3 8 (by decide) (by simp [Loc.wblocks]))
  actRep := h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (pw_ne hok.wdistinct 4 8 (by decide) (by simp [Loc.wblocks]))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 5 8 (by decide) (by simp [Loc.wblocks])))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 6 8 (by decide) (by simp [Loc.wblocks])))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 7 8 (by decide) (by simp [Loc.wblocks])))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => hk)
  w1 := h.w1.unch hu (pw_ne hok.wdistinct 5 8 (by decide) (by simp [Loc.wblocks]))
  w2 := h.w2.unch hu (pw_ne hok.wdistinct 6 8 (by decide) (by simp [Loc.wblocks]))
  w3 := h.w3.unch hu (pw_ne hok.wdistinct 7 8 (by decide) (by simp [Loc.wblocks]))
  w4 := harr
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 8 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 8 9 (by decide) (by simp [Loc.wblocks]))))
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 8 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 8 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing mark array 1. -/
theorem Mem.setMk1 {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.mb1)) (hk : Keep m m' L.mb1) (mk : Nat → Int)
    (harr : ArrayAt m' .Mint16signed L.mb1 0 (markVals mk) L.mc1)
    (hb : ∀ q < L.mc1, 0 ≤ mk q ∧ mk q ≤ S.st1) (hc : 0 < L.mc1) :
    Mem m' L G t { S with mk1 := mk } where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := h.lab.unch hu (pw_ne hok.wdistinct 0 9 (by decide) (by simp [Loc.wblocks]))
  ptn := h.ptn.unch hu (pw_ne hok.wdistinct 1 9 (by decide) (by simp [Loc.wblocks]))
  nc := h.nc.unch hu (pw_ne hok.wdistinct 2 9 (by decide) (by simp [Loc.wblocks]))
  act := h.act.unch hu (pw_ne hok.wdistinct 3 9 (by decide) (by simp [Loc.wblocks]))
  actRep := h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (pw_ne hok.wdistinct 4 9 (by decide) (by simp [Loc.wblocks]))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 5 9 (by decide) (by simp [Loc.wblocks])))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 6 9 (by decide) (by simp [Loc.wblocks])))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 7 9 (by decide) (by simp [Loc.wblocks])))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 8 9 (by decide) (by simp [Loc.wblocks])))
  w1 := h.w1.unch hu (pw_ne hok.wdistinct 5 9 (by decide) (by simp [Loc.wblocks]))
  w2 := h.w2.unch hu (pw_ne hok.wdistinct 6 9 (by decide) (by simp [Loc.wblocks]))
  w3 := h.w3.unch hu (pw_ne hok.wdistinct 7 9 (by decide) (by simp [Loc.wblocks]))
  w4 := h.w4.unch hu (pw_ne hok.wdistinct 8 9 (by decide) (by simp [Loc.wblocks]))
  k1 := h.k1.update hc hu hk harr hb
  k2 := h.k2.unch hu (fun e => hok.rw Block.vmark2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.vmark2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 9 12 (by decide) (by simp [Loc.wblocks]))) (fun _ => (Ne.symm (pw_ne hok.wdistinct 9 10 (by decide) (by simp [Loc.wblocks]))))
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq

/-- Writing mark array 2. -/
theorem Mem.setMk2 {n : Nat} {m m' : mem} {L : Loc} {G : Hex.SparseGraph n}
    {t : RefineSt n} {S : Scr} (hok : Ok n L) (h : Mem m L G t S)
    (hu : Unch m m' (· = L.mb2)) (hk : Keep m m' L.mb2) (mk : Nat → Int)
    (harr : ArrayAt m' .Mint16signed L.mb2 0 (markVals mk) L.mc2)
    (hb : ∀ q < L.mc2, 0 ≤ mk q ∧ mk q ≤ S.st2) (hc : 0 < L.mc2) :
    Mem m' L G t { S with mk2 := mk } where
  graph := h.graph.unch hu (fun e => hok.rw L.bsg (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bv (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.bd (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw L.be (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))
  lab := h.lab.unch hu (pw_ne hok.wdistinct 0 10 (by decide) (by simp [Loc.wblocks]))
  ptn := h.ptn.unch hu (pw_ne hok.wdistinct 1 10 (by decide) (by simp [Loc.wblocks]))
  nc := h.nc.unch hu (pw_ne hok.wdistinct 2 10 (by decide) (by simp [Loc.wblocks]))
  act := h.act.unch hu (pw_ne hok.wdistinct 3 10 (by decide) (by simp [Loc.wblocks]))
  actRep := h.actRep
  code := let ⟨kv, hkv⟩ := h.code; ⟨kv, hkv.unch hu (pw_ne hok.wdistinct 4 10 (by decide) (by simp [Loc.wblocks]))⟩
  d1 := h.d1.keep hu (fun e => hok.rw Sparse.Block.work1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.work1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 5 10 (by decide) (by simp [Loc.wblocks])))
  d2 := h.d2.keep hu (fun e => hok.rw Block.work2 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work2Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 6 10 (by decide) (by simp [Loc.wblocks])))
  d3 := h.d3.keep hu (fun e => hok.rw Block.work3 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work3Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 7 10 (by decide) (by simp [Loc.wblocks])))
  d4 := h.d4.keep hu (fun e => hok.rw Block.work4 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Block.work4Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun _ => Keep.unch hu (pw_ne hok.wdistinct 8 10 (by decide) (by simp [Loc.wblocks])))
  w1 := h.w1.unch hu (pw_ne hok.wdistinct 5 10 (by decide) (by simp [Loc.wblocks]))
  w2 := h.w2.unch hu (pw_ne hok.wdistinct 6 10 (by decide) (by simp [Loc.wblocks]))
  w3 := h.w3.unch hu (pw_ne hok.wdistinct 7 10 (by decide) (by simp [Loc.wblocks]))
  w4 := h.w4.unch hu (pw_ne hok.wdistinct 8 10 (by decide) (by simp [Loc.wblocks]))
  k1 := h.k1.unch hu (fun e => hok.rw Sparse.Block.vmark1 (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (fun e => hok.rw Sparse.Block.vmark1Sz (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks])) (Ne.symm (pw_ne hok.wdistinct 10 11 (by decide) (by simp [Loc.wblocks]))) (fun _ => (pw_ne hok.wdistinct 9 10 (by decide) (by simp [Loc.wblocks])))
  k2 := h.k2.update hc hu hk harr hb
  bit := fun q hq => by rw [hu.load _ _ _ (fun e => hok.rw Block.bit (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.bit q hq
  left := fun q hq => by erw [hu.load _ _ _ (fun e => hok.rw (NautyEnv.leftbit : block) (by simp [Loc.rblocks]) (by rw [e]; simp [Loc.writes, Loc.wblocks]))]; exact h.left q hq


end NautyVerified.Proofs.Sparse.Refine

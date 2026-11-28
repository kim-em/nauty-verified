import NautyVerified.Proofs.Sparse.Refine.Spec
import NautyVerified.Proofs.Sparse.Refine.Queue
import NautyVerified.Proofs.Sparse.Testcanlab.Satisfies

/-!
# The prologue of `refine_sg`

`SG_VDE`, `DYNALLOC1` of the four work arrays to `n`, `preparemarks1(n)`,
`preparemarks2(n)`, `longcode = *numcells`, `nactive = 0`: `wp_prologue`
leaves the locations `Ok` (each array the old one or a block new to memory),
memory holding the initial state `start0` with any scratch, `HITS` holding
`int`-range naturals (the old ones, or zeros when `work3` was reallocated),
and the temporaries `Tmp`. Only the scratch globals, the old scratch blocks
in use and blocks new to memory change.
-/

namespace NautyVerified.Proofs.Sparse.Refine

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source NautyVerified.Proofs.Sparse
open NautyVerified.Proofs.Set (sk longs BitTable)
open NautyVerified.Proofs.Nextelement (LeftbitTable)
open NautyVerified.Proofs.Alloc (DynAt Keep dynalloc1)
open Hex.GraphIso.Nauty (VSet)
open Hex.GraphIso.Nauty.Sparse (RefineSt Graph Scratch)

attribute [local instance] NautyEnv.sparse

variable {xi : ExternalCalls} {n : Nat}

/-- The state the queue scan starts from. -/
abbrev start0 (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) : RefineSt n :=
  withQ (Hex.GraphIso.Nauty.Sparse.Refinement.start lab ptn active numcells (Scratch.fresh n)) #[]

/-- `refine_sg`'s prologue, followed by `rest`. -/
abbrev pro (rest : statement) : statement :=
  .Ssequence (Testcanlab.vde id.«g» id.«v» id.«d» id.«e»)
    (.Ssequence (dynalloc1 id.«nausparse:work1_sz» id.«nausparse:work1» tint (tv id.«n») (idOf 703)
        (idOf 704) id.«nausparse:__stringlit_6» 10)
      (.Ssequence (dynalloc1 id.«nausparse:work2_sz» id.«nausparse:work2» tint (tv id.«n») (idOf 705)
          (idOf 706) id.«nausparse:__stringlit_6» 10)
        (.Ssequence (dynalloc1 id.«nausparse:work3_sz» id.«nausparse:work3» tint (tv id.«n») (idOf 707)
            (idOf 708) id.«nausparse:__stringlit_6» 10)
          (.Ssequence (dynalloc1 id.«nausparse:work4_sz» id.«nausparse:work4» tint (tv id.«n»)
              (idOf 709) (idOf 710) id.«nausparse:__stringlit_6» 10)
            (.Ssequence
              (sk (.Scall none (.Evar id.«nausparse:preparemarks1» (tfun [tulong] Tvoid)) [(tv id.«n»)]))
              (.Ssequence
                (sk (.Scall none (.Evar id.«nausparse:preparemarks2» (tfun [tulong] Tvoid))
                  [(tv id.«n»)]))
                (.Ssequence
                  (sk (.Sset id.«longcode» (.Ecast (.Ederef (pi id.«numcells») tint) tlong)))
                  (.Ssequence (sk (.Sset id.«nactive» (ci 0 tint))) rest))))))))

/-- What follows the prologue. -/
abbrev restS : statement :=
  .Ssequence (.Ssequence (sk (.Sset id.«i» (.Eunop .Oneg (ci 1 tint) tint))) queueLoop)
    (.Ssequence
      (sk (.Sifthenelse (.Ebinop .Oeq (tv id.«nactive») (ci 0 tint) tint)
        (.Ssequence
          (sk (.Sassign (.Ederef (pi id.«code») tint)
            (.Ecast (.Ebinop .Omod (.Etempvar id.«longcode» tlong) (ci 32767 tint) tlong) tint)))
          (.Sreturn none))
        .Sskip))
      (.Ssequence (.Ssequence (sk (.Sset id.«i» (ci 0 tint))) startLoop)
        (.Ssequence dist (.Ssequence mainLoop finish))))

theorem body_pro : body = pro restS := rfl

/-- `DYNALLOC1` of an `int` array to `n` held in an `int` temporary: either
nothing happens, or the array moves to a zero-filled block new to memory. -/
theorem wp_dynZ {f : function} {Q : Post} {le : temp_env} {m : mem}
    {gs gp x t1 t2 msg : ident} {msgLen : Int} {bs bp b : block} {cap k : Nat}
    (hgs : Genv.find_symbol sge.genv_genv gs = some bs)
    (hgp : Genv.find_symbol sge.genv_genv gp = some bp)
    (hD : DynAt m bp bs 4 cap b) (hx : PTree.get x le = some (.Vint (ir k)))
    (hk : k < 2147483648) (hck : 4 * k < 2 ^ 62)
    (hQ : ∀ le' m' cap' b', DynAt m' bp bs 4 cap' b' → k ≤ cap' →
      Unch m m' (fun z => z = bs ∨ z = bp ∨ (0 < cap ∧ z = b) ∨ (¬ Mem.valid_block m b' ∧ z = b')) →
      ((cap' = cap ∧ b' = b ∧ m' = m) ∨ (¬ Mem.valid_block m b' ∧ Alloc.Zeros m' b' (4 * cap'))) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ y, y ≠ t1 → y ≠ t2 → PTree.get y le' = PTree.get y le) →
      Q.normal E0 empty_env le' m') :
    Wp xi sge f (dynalloc1 gs gp tint (.Etempvar x tint) t1 t2 msg msgLen) Q empty_env le m := by
  by_cases hc : k ≤ cap
  · have hnil1 := NautyVerified.Proofs.Alloc.noShadow_empty _ _ hgs
    have hcap := hD.capLt
    wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, hx]
    simp only [Exec.lvalOfVar, hnil1, hgs, Exec.derefLoc,
      Cfrontend.Ctypes.access_mode, typeof, cop, Mem.loadv,
      show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, hD.capLd,
      cast_int_long_ir (a := k) ⟨by omega, by omega⟩]
    rw [Alloc.ltu_lr (a := cap) (b := k) (by omega) (by omega)]
    rw [ite_eq_right (by simpa using hc)]
    apply wp_skip
    exact hQ le m cap b hD hc (Unch.refl _ _) (.inl ⟨rfl, rfl, rfl⟩) (fun _ h => h) (fun _ _ _ => rfl)
  · refine Alloc.wp_dynalloc1Z hgs hgp rfl hD (fun _ _ => hx) rfl hk hck ?_
    intro le' m' cap' b' hD' hk' hu hor hg ho
    rcases hor with ⟨rfl, rfl⟩ | hz
    · omega
    · exact hQ le' m' cap' b' hD' hk' hu (.inr hz) hg ho

/-- The argument temporaries on entry. -/
structure Args (le : temp_env) (L : Loc) (n : Nat) : Prop where
  g : PTree.get id.g le = some (.Vptr L.bsg L.sofs)
  lab : PTree.get id.lab le = some (.Vptr L.bl L.lofs)
  ptn : PTree.get id.ptn le = some (.Vptr L.bp L.pofs)
  level : PTree.get id.level le = some (.Vint (ir L.level))
  numcells : PTree.get id.numcells le = some (.Vptr L.bn L.nofs)
  active : PTree.get id.active le = some (.Vptr L.ba L.aofs)
  code : PTree.get id.code le = some (.Vptr L.bk L.kofs)
  m : PTree.get id.m le = some (.Vint (ir L.M))
  n : PTree.get id.n le = some (.Vint (ir n))

/-- The temporaries the prologue assigns besides `longcode` and `nactive`. -/
def proTemps : List ident := [id.v, id.d, id.e] ++ (List.range 8).map (fun i => idOf (703 + i))

/-- A slot after the prologue: the old array, or a block new to `m`. -/
def Slot (m : mem) (c : Nat) (b : block) (c' : Nat) (b' : block) : Prop :=
  (c' = c ∧ b' = b) ∨ ¬ Mem.valid_block m b'

/-- What the prologue changes. -/
def proSet (L : Loc) (m : mem) (z : block) : Prop :=
  z ∈ scrGlobals ∨ z = Sparse.Block.vmark1Val ∨ z = Block.vmark2Val ∨ L.scrUsed z ∨
    ¬ Mem.valid_block m z

theorem SgSep.glob_ne {m : mem} {L : Loc} (hs : SgSep n m L) {z : block}
    (hz : z ∈ scrGlobals ++ tblGlobals) {b : block} (hb : L.scrUsed b) : z ≠ b := fun e =>
  (hs.scrValid b hb).2 (e ▸ hz)

theorem SgSep.used_ne {m : mem} {L : Loc} (hs : SgSep n m L) (i j : Nat) (hi : i < 6) (hj : j < 6)
    (hij : i ≠ j) (h1 : 0 < (L.slots.getD i (0, L.b1)).1) (h2 : 0 < (L.slots.getD j (0, L.b1)).1) :
    (L.slots.getD i (0, L.b1)).2 ≠ (L.slots.getD j (0, L.b1)).2 :=
  hs.scrDistinct i hi j hj hij h1 h2

theorem not_marks2S {m : mem} {cap : Nat} {b b' z : block} (hv : Mem.valid_block m z)
    (h1 : z ≠ Block.vmark2) (h2 : z ≠ Block.vmark2Sz) (h3 : z ≠ Block.vmark2Val) (h4 : 0 < cap → z ≠ b) :
    ¬ Marks2.MarksS m cap b b' z := by
  rintro (h | h | h | ⟨hc, h⟩ | ⟨hb, rfl⟩)
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 hc h
  · exact hb hv

theorem Prov.of_dyn {m m' : mem} {bp bs : block} {c cap cap' : Nat} {b b' : block}
    (hD : DynAt m' bp bs c cap' b') (hc : 0 < cap') (h : (cap' = cap ∧ b' = b) ∨ ¬ Mem.valid_block m b') :
    Prov m m' cap b b' := by
  rcases h with ⟨rfl, rfl⟩ | hnv
  · exact .inl ⟨rfl, hc⟩
  · exact .inr ⟨hnv, Alloc.Malloced.valid (hD.mal hc)⟩

/-- A block that is valid, no global and not the old array is untouched by a `DYNALLOC1`. -/
theorem eval_nc' {L : Loc} {G : Hex.SparseGraph n} {t : RefineSt n} {S : Scr} {le : temp_env} {m : mem}
    (hm : Mem m L G t S) (hnum : PTree.get id.numcells le = some (.Vptr L.bn L.nofs)) :
    Exec.evalExpr sge empty_env le m (.Ederef (pi id.numcells) tint) =
      some (.Vint (ir t.numcells)) := by
  simp only [Exec.evalExpr, hnum, Exec.derefLoc, Cfrontend.Ctypes.access_mode]
  apply load_array hm.nc (show 0 < 1 by decide)
  unfold elemOfs
  rw [show csize .Mint32 * ((0 : Nat) : Int) = 0 by simp, Int.add_zero, zOfInt_intOfZ]

theorem nd {m : mem} {z gs gp b b' : block} {c : Nat} (hv : Mem.valid_block m z)
    (hg : ∀ g ∈ scrGlobals ++ tblGlobals, z ≠ g) (hgs : gs ∈ scrGlobals ++ tblGlobals)
    (hgp : gp ∈ scrGlobals ++ tblGlobals) (h3 : 0 < c → z ≠ b) :
    ¬ (z = gs ∨ z = gp ∨ (0 < c ∧ z = b) ∨ (¬ Mem.valid_block m b' ∧ z = b')) :=
  Alloc.not_dynSet hv (hg _ hgs) (hg _ hgp) h3

theorem nm1 {m : mem} {z b b' : block} {c : Nat} (hv : Mem.valid_block m z)
    (hg : ∀ g ∈ scrGlobals ++ tblGlobals, z ≠ g) (h4 : 0 < c → z ≠ b) : ¬ MarksS m c b b' z :=
  Testcanlab.not_marksS hv (hg _ (by decide)) (hg _ (by decide)) (hg _ (by decide)) h4

theorem nm2 {m : mem} {z b b' : block} {c : Nat} (hv : Mem.valid_block m z)
    (hg : ∀ g ∈ scrGlobals ++ tblGlobals, z ≠ g) (h4 : 0 < c → z ≠ b) : ¬ Marks2.MarksS m c b b' z :=
  not_marks2S hv (hg _ (by decide)) (hg _ (by decide)) (hg _ (by decide)) h4

theorem wp_prologue {Q : Post} {rest : statement} {L : Loc} {G : Hex.SparseGraph n} {le : temp_env}
    {m : mem} {lab ptn : Array Nat} {active : VSet n} {numcells : Nat} {aw : Nat → Lib.Integers.int64}
    (hs : SgSep n m L) (hbv : ∀ z ∈ L.base, Mem.valid_block m z)
    (hov : ∀ z, L.scrUsed z → Mem.valid_block m z)
    (hgr : SparseGraphAt m L.bsg L.sofs G L.bv L.vo L.bd L.dofs L.be L.eo)
    (hlab : ArrayAt m .Mint32 L.bl L.lb (ints lab) n) (hptn : ArrayAt m .Mint32 L.bp L.pb (ints ptn) n)
    (hnc : ArrayAt m .Mint32 L.bn L.nb (fun _ => .Vint (ir numcells)) 1) (hncn : numcells < 2147483648)
    (hact : ArrayAt m .Mint64 L.ba L.ab (longs aw) L.M) (hrep : SetRep (fun w => bv64 (aw w)) L.M active)
    (hcode : ∃ kv, ArrayAt m .Mint32 L.bk L.kb kv 1) (hscr : ScrAt n m L) (hbit : BitTable m Block.bit)
    (hleft : LeftbitTable m) (ha : Args le L n)
    (hQ : ∀ c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2 le1 m1 S1,
      Ok n (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2) →
      Mem m1 (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2) G (start0 lab ptn active numcells) S1 →
      Tmp le1 (L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2) (start0 lab ptn active numcells) →
      S1.w3.size = n → (∀ i < n, S1.w3[i]! < 2147483648) →
      Slot m L.c1 L.b1 c1 b1 → Slot m L.c2 L.b2 c2 b2 → Slot m L.c3 L.b3 c3 b3 →
      Slot m L.c4 L.b4 c4 b4 → Slot m L.mc1 L.mb1 mc1 mb1 → Slot m L.mc2 L.mb2 mc2 mb2 →
      Unch m m1 (proSet L m) → (∀ z, Mem.valid_block m z → Mem.valid_block m1 z) →
      (∀ x, x ∉ proTemps → x ≠ id.longcode → x ≠ id.nactive → PTree.get x le1 = PTree.get x le) →
      Wp xi sge F rest Q empty_env le1 m1) :
    Wp xi sge F (pro rest) Q empty_env le m := by
  have hn0 := hs.n0
  have hnl := hs.nlt
  have gv : ∀ z ∈ scrGlobals ++ tblGlobals, Mem.valid_block m z := fun z hz => hbv z (by
    simp only [Loc.base, List.mem_append] at hz ⊢
    rcases hz with h | h
    · exact .inl (.inr h)
    · exact .inr h)
  have gne := fun {z : block} (hz : z ∈ scrGlobals ++ tblGlobals) {b : block} (hb : L.scrUsed b) =>
    hs.glob_ne hz hb
  wp_step
  refine Testcanlab.wp_vde (bsg := L.bsg) (sofs := L.sofs) ha.g (by decide) (by decide) hgr.v hgr.d
    hgr.e ?_
  let le0 := PTree.set id.e (.Vptr L.be L.eo) (PTree.set id.d (.Vptr L.bd L.dofs)
    (PTree.set id.v (.Vptr L.bv L.vo) le))
  have hn0' : PTree.get id.n le0 = some (.Vint (ir n)) := by
    simp (config := {decide := true}) only [le0, temps_gso]; exact ha.n
  -- work1
  wp_step
  refine Alloc.wp_dynalloc1 (E := NautyEnv.sparse) find_work1Sz find_work1 rfl hscr.d1 hn0' (by omega)
    (show 4 * n < 2 ^ 62 by omega) ?_
  intro le1 m1 c1 b1 hD1 hn1 hu1 hor1 hg1 ho1
  have p1 : Prov m m1 L.c1 L.b1 b1 := Prov.of_dyn hD1 (by omega) hor1
  have u1 : 0 < L.c1 → L.scrUsed L.b1 := fun h => .inl ⟨h, rfl⟩
  have u2 : 0 < L.c2 → L.scrUsed L.b2 := fun h => .inr (.inl ⟨h, rfl⟩)
  have u3 : 0 < L.c3 → L.scrUsed L.b3 := fun h => .inr (.inr (.inl ⟨h, rfl⟩))
  have u4 : 0 < L.c4 → L.scrUsed L.b4 := fun h => .inr (.inr (.inr (.inl ⟨h, rfl⟩)))
  have u5 : 0 < L.mc1 → L.scrUsed L.mb1 := fun h => .inr (.inr (.inr (.inr (.inl ⟨h, rfl⟩))))
  have u6 : 0 < L.mc2 → L.scrUsed L.mb2 := fun h => .inr (.inr (.inr (.inr (.inr ⟨h, rfl⟩))))
  -- a global is no old scratch block in use
  have gb : ∀ {g : block}, g ∈ scrGlobals ++ tblGlobals → ∀ {c : Nat} {b : block}, (0 < c → L.scrUsed b) →
      0 < c → g ≠ b := fun hg _ _ hu hc => gne hg (hu hc)
  -- two old scratch blocks in use differ
  have od : ∀ i j, i < 6 → j < 6 → i ≠ j → 0 < (L.slots.getD i (0, L.b1)).1 →
      0 < (L.slots.getD j (0, L.b1)).1 → (L.slots.getD i (0, L.b1)).2 ≠ (L.slots.getD j (0, L.b1)).2 :=
    fun i j hi hj hij => hs.scrDistinct i hi j hj hij
  -- a new array is no block valid before, other than its own old one
  have nb : ∀ {m₁ m₂ : mem} {c : Nat} {b b' : block}, Prov m₁ m₂ c b b' →
      (∀ y, Mem.valid_block m y → Mem.valid_block m₁ y) → ∀ z, Mem.valid_block m z →
      (0 < c → z ≠ b) → b' ≠ z := fun hp hmono z hz hu => hp.ne_base hmono hz hu
  have hn1' : PTree.get id.n le1 = some (.Vint (ir n)) := by
    rw [ho1 _ (by decide) (by decide)]; exact hn0'
  have o21 : 0 < L.c2 → 0 < L.c1 → L.b2 ≠ L.b1 := fun h2 h1 => od 1 0 (by decide) (by decide) (by decide) h2 h1
  have o31 : 0 < L.c3 → 0 < L.c1 → L.b3 ≠ L.b1 := fun h2 h1 => od 2 0 (by decide) (by decide) (by decide) h2 h1
  have o32 : 0 < L.c3 → 0 < L.c2 → L.b3 ≠ L.b2 := fun h2 h1 => od 2 1 (by decide) (by decide) (by decide) h2 h1
  have o41 : 0 < L.c4 → 0 < L.c1 → L.b4 ≠ L.b1 := fun h2 h1 => od 3 0 (by decide) (by decide) (by decide) h2 h1
  have o42 : 0 < L.c4 → 0 < L.c2 → L.b4 ≠ L.b2 := fun h2 h1 => od 3 1 (by decide) (by decide) (by decide) h2 h1
  have o43 : 0 < L.c4 → 0 < L.c3 → L.b4 ≠ L.b3 := fun h2 h1 => od 3 2 (by decide) (by decide) (by decide) h2 h1
  have o51 : 0 < L.mc1 → 0 < L.c1 → L.mb1 ≠ L.b1 := fun h2 h1 => od 4 0 (by decide) (by decide) (by decide) h2 h1
  have o52 : 0 < L.mc1 → 0 < L.c2 → L.mb1 ≠ L.b2 := fun h2 h1 => od 4 1 (by decide) (by decide) (by decide) h2 h1
  have o53 : 0 < L.mc1 → 0 < L.c3 → L.mb1 ≠ L.b3 := fun h2 h1 => od 4 2 (by decide) (by decide) (by decide) h2 h1
  have o54 : 0 < L.mc1 → 0 < L.c4 → L.mb1 ≠ L.b4 := fun h2 h1 => od 4 3 (by decide) (by decide) (by decide) h2 h1
  have o61 : 0 < L.mc2 → 0 < L.c1 → L.mb2 ≠ L.b1 := fun h2 h1 => od 5 0 (by decide) (by decide) (by decide) h2 h1
  have o62 : 0 < L.mc2 → 0 < L.c2 → L.mb2 ≠ L.b2 := fun h2 h1 => od 5 1 (by decide) (by decide) (by decide) h2 h1
  have o63 : 0 < L.mc2 → 0 < L.c3 → L.mb2 ≠ L.b3 := fun h2 h1 => od 5 2 (by decide) (by decide) (by decide) h2 h1
  have o64 : 0 < L.mc2 → 0 < L.c4 → L.mb2 ≠ L.b4 := fun h2 h1 => od 5 3 (by decide) (by decide) (by decide) h2 h1
  have o65 : 0 < L.mc2 → 0 < L.mc1 → L.mb2 ≠ L.mb1 := fun h2 h1 => od 5 4 (by decide) (by decide) (by decide) h2 h1
  -- work2
  have hD2 : DynAt m1 Block.work2 Block.work2Sz 4 L.c2 L.b2 :=
    hscr.d2.keep hu1
      (Alloc.not_dynSet (gv _ (by decide)) (by decide) (by decide) (gb (by decide) u1))
      (Alloc.not_dynSet (gv _ (by decide)) (by decide) (by decide) (gb (by decide) u1))
      (fun hc => Keep.unch hu1 (Alloc.not_dynSet (hov _ (u2 hc)) (gb (by decide) u2 hc).symm
        (gb (by decide) u2 hc).symm (o21 hc)))
  wp_step
  refine Alloc.wp_dynalloc1 (E := NautyEnv.sparse) find_work2Sz find_work2 rfl hD2 hn1' (by omega)
    (show 4 * n < 2 ^ 62 by omega) ?_
  intro le2 m2 c2 b2 hD2' hn2 hu2 hor2 hg2 ho2
  have p2 : Prov m1 m2 L.c2 L.b2 b2 := Prov.of_dyn hD2' (by omega) hor2
  have hn2' : PTree.get id.n le2 = some (.Vint (ir n)) := by
    rw [ho2 _ (by decide) (by decide)]; exact hn1'
  have v1 : Mem.valid_block m1 b1 := Alloc.Malloced.valid (hD1.mal (by omega))
  have x1 : ∀ z, Mem.valid_block m z → (0 < L.c1 → z ≠ L.b1) → b1 ≠ z :=
    fun z hz hu => nb p1 (fun _ h => h) z hz hu
  have hD1' : DynAt m2 Sparse.Block.work1 Sparse.Block.work1Sz 4 c1 b1 :=
    hD1.keep hu2
      (Alloc.not_dynSet (hg1 _ (gv _ (by decide))) (by decide) (by decide) (gb (by decide) u2))
      (Alloc.not_dynSet (hg1 _ (gv _ (by decide))) (by decide) (by decide) (gb (by decide) u2))
      (fun _ => Keep.unch hu2 (Alloc.not_dynSet v1 (x1 _ (gv _ (by decide)) (gb (by decide) u1))
        (x1 _ (gv _ (by decide)) (gb (by decide) u1))
        (fun hc => x1 _ (hov _ (u2 hc)) (fun h1 => o21 hc h1))))
  have v2 : Mem.valid_block m2 b2 := Alloc.Malloced.valid (hD2'.mal (by omega))
  have x2 : ∀ z, Mem.valid_block m z → (0 < L.c2 → z ≠ L.b2) → b2 ≠ z :=
    fun z hz hu => nb p2 hg1 z hz hu
  have g12 : ∀ z, Mem.valid_block m z → Mem.valid_block m2 z := fun z h => hg2 _ (hg1 _ h)
  have y12 : b1 ≠ b2 := p1.ne p2 (fun _ h => h) (fun h => hov _ (u1 h) |> hg1 _) (fun h => hov _ (u2 h))
    (fun h1 h2 => (o21 h2 h1).symm)
  -- work3, with its contents
  have hD3a : DynAt m1 Block.work3 Block.work3Sz 4 L.c3 L.b3 :=
    hscr.d3.keep hu1
      (Alloc.not_dynSet (gv _ (by decide)) (by decide) (by decide) (gb (by decide) u1))
      (Alloc.not_dynSet (gv _ (by decide)) (by decide) (by decide) (gb (by decide) u1))
      (fun hc => Keep.unch hu1 (Alloc.not_dynSet (hov _ (u3 hc)) (gb (by decide) u3 hc).symm
        (gb (by decide) u3 hc).symm (o31 hc)))
  have nb3a : 0 < L.c3 → ¬ (L.b3 = Sparse.Block.work1Sz ∨ L.b3 = Sparse.Block.work1 ∨
      (0 < L.c1 ∧ L.b3 = L.b1) ∨ (¬ Mem.valid_block m b1 ∧ L.b3 = b1)) := fun hc =>
    Alloc.not_dynSet (hov _ (u3 hc)) (gb (by decide) u3 hc).symm (gb (by decide) u3 hc).symm (o31 hc)
  have nb3b : 0 < L.c3 → ¬ (L.b3 = Block.work2Sz ∨ L.b3 = Block.work2 ∨
      (0 < L.c2 ∧ L.b3 = L.b2) ∨ (¬ Mem.valid_block m1 b2 ∧ L.b3 = b2)) := fun hc =>
    Alloc.not_dynSet (hg1 _ (hov _ (u3 hc))) (gb (by decide) u3 hc).symm (gb (by decide) u3 hc).symm
      (o32 hc)
  have hD3b : DynAt m2 Block.work3 Block.work3Sz 4 L.c3 L.b3 :=
    hD3a.keep hu2
      (Alloc.not_dynSet (hg1 _ (gv _ (by decide))) (by decide) (by decide) (gb (by decide) u2))
      (Alloc.not_dynSet (hg1 _ (gv _ (by decide))) (by decide) (by decide) (gb (by decide) u2))
      (fun hc => Keep.unch hu2 (nb3b hc))
  have hW3 : n ≤ L.c3 → ∃ H : Array Nat, H.size = n ∧ ArrayAt m2 .Mint32 L.b3 0 (ints H) n ∧
      ∀ i < n, H[i]! < 2147483648 := fun hc => by
    obtain ⟨H, h1, h2, h3⟩ := hscr.w3 hc
    exact ⟨H, h1, (h2.unch hu1 (nb3a (by omega))).unch hu2 (nb3b (by omega)), h3⟩
  wp_step
  refine wp_dynZ find_work3Sz find_work3 hD3b hn2' (by omega) (show 4 * n < 2 ^ 62 by omega) ?_
  intro le3 m3 c3 b3 hD3 hn3 hu3 hor3 hg3 ho3
  have hW3' : ∃ H : Array Nat, H.size = n ∧ ArrayAt m3 .Mint32 b3 0 (ints H) n ∧
      ∀ i < n, H[i]! < 2147483648 := by
    rcases hor3 with ⟨rfl, rfl, rfl⟩ | ⟨-, hz⟩
    · exact hW3 hn3
    · have hmal := hD3.mal (by omega)
      have ha := Alloc.Zeros.array hz (fun o h1 h2 => hmal.perm o (by omega) h2) (by have := hmal.small; omega)
        .Mint32 4 rfl rfl (.Vint (ir 0)) rfl n (by omega)
      refine ⟨Array.replicate n 0, by simp, ha.congr fun i hi => ?_, fun i hi => ?_⟩
      · simp [ints, hi]
      · simp [hi]
  have p3 : Prov m2 m3 L.c3 L.b3 b3 := by
    rcases hor3 with ⟨rfl, rfl, -⟩ | ⟨hnv, -⟩
    · exact .inl ⟨rfl, by omega⟩
    · exact .inr ⟨hnv, Alloc.Malloced.valid (hD3.mal (by omega))⟩
  have g3 : ∀ z, Mem.valid_block m z → Mem.valid_block m3 z := fun z h => hg3 _ (g12 _ h)
  have v3 : Mem.valid_block m3 b3 := Alloc.Malloced.valid (hD3.mal (by omega))
  have x3 : ∀ z, Mem.valid_block m z → (0 < L.c3 → z ≠ L.b3) → b3 ≠ z :=
    fun z hz hu => nb p3 g12 z hz hu
  have G1 : ∀ g ∈ scrGlobals ++ tblGlobals, b1 ≠ g := fun g hg => x1 g (gv g hg) (gb hg u1)
  have G2 : ∀ g ∈ scrGlobals ++ tblGlobals, b2 ≠ g := fun g hg => x2 g (gv g hg) (gb hg u2)
  have G3 : ∀ g ∈ scrGlobals ++ tblGlobals, b3 ≠ g := fun g hg => x3 g (gv g hg) (gb hg u3)
  have hn3' : PTree.get id.n le3 = some (.Vint (ir n)) := by
    rw [ho3 _ (by decide) (by decide)]; exact hn2'
  -- globals of later slots and old arrays through a step
  have gl : ∀ {m' : mem} {g : block}, Mem.valid_block m' g → g ∈ scrGlobals ++ tblGlobals →
      ∀ {gs gp b b' : block} {c : Nat}, g ≠ gs → g ≠ gp → (0 < c → L.scrUsed b) →
      ¬ (g = gs ∨ g = gp ∨ (0 < c ∧ g = b) ∨ (¬ Mem.valid_block m' b' ∧ g = b')) :=
    fun hv hg _ _ _ _ _ h1 h2 hu => Alloc.not_dynSet hv h1 h2 (gb hg hu)
  -- work4
  have hD4 : DynAt m3 Block.work4 Block.work4Sz 4 L.c4 L.b4 :=
    ((hscr.d4.keep hu1 (gl (gv _ (by decide)) (by decide) (by decide) (by decide) u1)
      (gl (gv _ (by decide)) (by decide) (by decide) (by decide) u1)
      (fun hc => Keep.unch hu1 (Alloc.not_dynSet (hov _ (u4 hc)) (gb (by decide) u4 hc).symm
        (gb (by decide) u4 hc).symm (o41 hc)))).keep hu2
      (gl (hg1 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u2)
      (gl (hg1 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u2)
      (fun hc => Keep.unch hu2 (Alloc.not_dynSet (hg1 _ (hov _ (u4 hc))) (gb (by decide) u4 hc).symm
        (gb (by decide) u4 hc).symm (o42 hc)))).keep hu3
      (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (fun hc => Keep.unch hu3 (Alloc.not_dynSet (g12 _ (hov _ (u4 hc))) (gb (by decide) u4 hc).symm
        (gb (by decide) u4 hc).symm (o43 hc)))
  wp_step
  refine Alloc.wp_dynalloc1 (E := NautyEnv.sparse) find_work4Sz find_work4 rfl hD4 hn3' (by omega)
    (show 4 * n < 2 ^ 62 by omega) ?_
  intro le4 m4 c4 b4 hD4' hn4 hu4 hor4 hg4 ho4
  have p4 : Prov m3 m4 L.c4 L.b4 b4 := Prov.of_dyn hD4' (by omega) hor4
  have g4 : ∀ z, Mem.valid_block m z → Mem.valid_block m4 z := fun z h => hg4 _ (g3 _ h)
  have v4 : Mem.valid_block m4 b4 := Alloc.Malloced.valid (hD4'.mal (by omega))
  have x4 : ∀ z, Mem.valid_block m z → (0 < L.c4 → z ≠ L.b4) → b4 ≠ z :=
    fun z hz hu => nb p4 g3 z hz hu
  have G4 : ∀ g ∈ scrGlobals ++ tblGlobals, b4 ≠ g := fun g hg => x4 g (gv g hg) (gb hg u4)
  have hn4' : PTree.get id.n le4 = some (.Vint (ir n)) := by
    rw [ho4 _ (by decide) (by decide)]; exact hn3'
  -- preparemarks1
  obtain ⟨st1, mk1, hK1⟩ := hscr.k1
  have hK1' : MarksAt m4 L.mc1 L.mb1 st1 mk1 :=
    (((hK1.unch hu1 (gl (gv _ (by decide)) (by decide) (by decide) (by decide) u1)
      (gl (gv _ (by decide)) (by decide) (by decide) (by decide) u1)
      (gl (gv _ (by decide)) (by decide) (by decide) (by decide) u1)
      (fun hc => Alloc.not_dynSet (hov _ (u5 hc)) (gb (by decide) u5 hc).symm
        (gb (by decide) u5 hc).symm (o51 hc))).unch hu2
      (gl (hg1 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u2)
      (gl (hg1 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u2)
      (gl (hg1 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u2)
      (fun hc => Alloc.not_dynSet (hg1 _ (hov _ (u5 hc))) (gb (by decide) u5 hc).symm
        (gb (by decide) u5 hc).symm (o52 hc))).unch hu3
      (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (fun hc => Alloc.not_dynSet (g12 _ (hov _ (u5 hc))) (gb (by decide) u5 hc).symm
        (gb (by decide) u5 hc).symm (o53 hc))).unch hu4
      (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4)
      (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4)
      (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4)
      (fun hc => Alloc.not_dynSet (g3 _ (hov _ (u5 hc))) (gb (by decide) u5 hc).symm
        (gb (by decide) u5 hc).symm (o54 hc))
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Sparse.Block.preparemarks1 Ptrofs.zero) (targs := [tulong]) (tres := .Tvoid)
    (cc := Common.AST.cc_default) _ (Sparse.prepSpec n L.mc1 L.mb1 st1 mk1) (prep_satisfies _ _ _ _ _) rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get sparse.id.«nausparse:preparemarks1» (empty_env : env) = none from rfl,
      find_preparemarks1, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
    (by simp only [Exec.evalExprlist, Exec.evalExpr, hn4', typeof, cop,
          cast_int_long_ir (a := n) ⟨by omega, by omega⟩])
    (by simp [Common.Globalenvs.Genv.find_funct, funct_preparemarks1]) Testcanlab.type_preparemarks1
    ⟨rfl, hK1', by omega⟩ ?_
  rintro tr - m5 ⟨rfl, mc1, mb1, st1', mk1', hK5, hn5, hor5, hu5, hg5⟩
  simp only [set_opttemp, E0_append]
  have g5 : ∀ z, Mem.valid_block m z → Mem.valid_block m5 z := fun z h => hg5 _ (g4 _ h)
  have hc5 : 0 < mc1 := by omega
  have p5 : Prov m4 m5 L.mc1 L.mb1 mb1 := by
    rcases hor5 with ⟨rfl, rfl⟩ | hnv
    · exact .inl ⟨rfl, hc5⟩
    · exact .inr ⟨hnv, Alloc.Malloced.valid (hK5.dyn.mal hc5)⟩
  have x5 : ∀ z, Mem.valid_block m z → (0 < L.mc1 → z ≠ L.mb1) → mb1 ≠ z :=
    fun z hz hu => nb p5 g4 z hz hu
  have G5 : ∀ g ∈ scrGlobals ++ tblGlobals, mb1 ≠ g := fun g hg => x5 g (gv g hg) (gb hg u5)
  have glm : ∀ {g : block}, Mem.valid_block m4 g → g ∈ scrGlobals ++ tblGlobals → g ≠ Sparse.Block.vmark1 →
      g ≠ Sparse.Block.vmark1Sz → g ≠ Sparse.Block.vmark1Val → ¬ MarksS m4 L.mc1 L.mb1 mb1 g :=
    fun hv hg h1 h2 h3 => Testcanlab.not_marksS hv h1 h2 h3 (gb hg u5)
  -- preparemarks2
  obtain ⟨st2, mk2, hK2⟩ := hscr.k2
  have hK2' : Marks2.MarksAt m5 L.mc2 L.mb2 st2 mk2 :=
    ((((hK2.unch hu1 (gl (gv _ (by decide)) (by decide) (by decide) (by decide) u1)
      (gl (gv _ (by decide)) (by decide) (by decide) (by decide) u1)
      (gl (gv _ (by decide)) (by decide) (by decide) (by decide) u1)
      (fun hc => Alloc.not_dynSet (hov _ (u6 hc)) (gb (by decide) u6 hc).symm
        (gb (by decide) u6 hc).symm (o61 hc))).unch hu2
      (gl (hg1 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u2)
      (gl (hg1 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u2)
      (gl (hg1 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u2)
      (fun hc => Alloc.not_dynSet (hg1 _ (hov _ (u6 hc))) (gb (by decide) u6 hc).symm
        (gb (by decide) u6 hc).symm (o62 hc))).unch hu3
      (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (fun hc => Alloc.not_dynSet (g12 _ (hov _ (u6 hc))) (gb (by decide) u6 hc).symm
        (gb (by decide) u6 hc).symm (o63 hc))).unch hu4
      (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4)
      (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4)
      (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4)
      (fun hc => Alloc.not_dynSet (g3 _ (hov _ (u6 hc))) (gb (by decide) u6 hc).symm
        (gb (by decide) u6 hc).symm (o64 hc))).unch hu5
      (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide))
      (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide))
      (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide))
      (fun hc => Testcanlab.not_marksS (g4 _ (hov _ (u6 hc))) (gb (by decide) u6 hc).symm
        (gb (by decide) u6 hc).symm (gb (by decide) u6 hc).symm (o65 hc))
  have hn5' : PTree.get id.n le4 = some (.Vint (ir n)) := hn4'
  wp_step; wp_step; wp_step
  refine wp_call (vf := .Vptr Block.preparemarks2 Ptrofs.zero) (targs := [tulong]) (tres := .Tvoid)
    (cc := Common.AST.cc_default) _ (Marks2.prepSpec n L.mc2 L.mb2 st2 mk2)
    (Marks2.prep_satisfies _ _ _ _ _) rfl
    (by simp only [Exec.evalExpr, Exec.lvalOfVar,
      show PTree.get sparse.id.«nausparse:preparemarks2» (empty_env : env) = none from rfl,
      find_preparemarks2, Exec.derefLoc, Cfrontend.Ctypes.access_mode])
    (by simp only [Exec.evalExprlist, Exec.evalExpr, hn4', typeof, cop,
          cast_int_long_ir (a := n) ⟨by omega, by omega⟩])
    (by simp [Common.Globalenvs.Genv.find_funct, funct_preparemarks2]) rfl
    ⟨rfl, hK2', by omega⟩ ?_
  rintro tr - m6 ⟨rfl, mc2, mb2, st2', mk2', hK6, hn6, hor6, hu6, hg6⟩
  simp only [set_opttemp, E0_append]
  have hc6 : 0 < mc2 := by omega
  have p6 : Prov m5 m6 L.mc2 L.mb2 mb2 := by
    rcases hor6 with ⟨rfl, rfl⟩ | hnv
    · exact .inl ⟨rfl, hc6⟩
    · exact .inr ⟨hnv, Alloc.Malloced.valid (hK6.dyn.mal hc6)⟩
  have glm2 : ∀ {g : block}, Mem.valid_block m5 g → g ∈ scrGlobals ++ tblGlobals → g ≠ Block.vmark2 →
      g ≠ Block.vmark2Sz → g ≠ Block.vmark2Val → ¬ Marks2.MarksS m5 L.mc2 L.mb2 mb2 g :=
    fun hv hg h1 h2 h3 => not_marks2S hv h1 h2 h3 (gb hg u6)
  -- the arrays, through the later steps
  have hD1f : DynAt m6 Sparse.Block.work1 Sparse.Block.work1Sz 4 c1 b1 :=
    (((hD1'.keep hu3 (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3)
      (fun _ => Keep.unch hu3 (nd (hg2 _ v1) G1 (by decide) (by decide)
        (fun hc => x1 _ (hov _ (u3 hc)) (fun h => o31 hc h))))).keep hu4
      (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4)
      (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4)
      (fun _ => Keep.unch hu4 (nd (hg3 _ (hg2 _ v1)) G1 (by decide) (by decide)
        (fun hc => x1 _ (hov _ (u4 hc)) (fun h => o41 hc h))))).keep hu5
      (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide))
      (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide))
      (fun _ => Keep.unch hu5 (nm1 (hg4 _ (hg3 _ (hg2 _ v1))) G1
        (fun hc => x1 _ (hov _ (u5 hc)) (fun h => o51 hc h))))).keep hu6
      (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide))
      (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide))
      (fun _ => Keep.unch hu6 (nm2 (hg5 _ (hg4 _ (hg3 _ (hg2 _ v1)))) G1
        (fun hc => x1 _ (hov _ (u6 hc)) (fun h => o61 hc h))))
  have hD2f : DynAt m6 Block.work2 Block.work2Sz 4 c2 b2 :=
    ((((hD2').keep hu3 (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3) (gl (g12 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u3) (fun _ => Keep.unch hu3 (nd v2 G2 (by decide) (by decide) (fun hc => x2 _ (hov _ (u3 hc)) (fun h => o32 hc h))))).keep hu4 (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4) (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4) (fun _ => Keep.unch hu4 (nd (hg3 _ v2) G2 (by decide) (by decide) (fun hc => x2 _ (hov _ (u4 hc)) (fun h => o42 hc h))))).keep hu5 (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (fun _ => Keep.unch hu5 (nm1 (hg4 _ (hg3 _ v2)) G2 (fun hc => x2 _ (hov _ (u5 hc)) (fun h => o52 hc h))))).keep hu6 (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (fun _ => Keep.unch hu6 (nm2 (hg5 _ (hg4 _ (hg3 _ v2))) G2 (fun hc => x2 _ (hov _ (u6 hc)) (fun h => o62 hc h))))
  have hD3f : DynAt m6 Block.work3 Block.work3Sz 4 c3 b3 :=
    (((hD3).keep hu4 (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4) (gl (g3 _ (gv _ (by decide))) (by decide) (by decide) (by decide) u4) (fun _ => Keep.unch hu4 (nd v3 G3 (by decide) (by decide) (fun hc => x3 _ (hov _ (u4 hc)) (fun h => o43 hc h))))).keep hu5 (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (fun _ => Keep.unch hu5 (nm1 (hg4 _ v3) G3 (fun hc => x3 _ (hov _ (u5 hc)) (fun h => o53 hc h))))).keep hu6 (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (fun _ => Keep.unch hu6 (nm2 (hg5 _ (hg4 _ v3)) G3 (fun hc => x3 _ (hov _ (u6 hc)) (fun h => o63 hc h))))
  obtain ⟨H, hHs, hHa, hHl⟩ := hW3'
  have hHf : ArrayAt m6 .Mint32 b3 0 (ints H) n :=
    (((hHa).unch hu4 (nd v3 G3 (by decide) (by decide) (fun hc => x3 _ (hov _ (u4 hc)) (fun h => o43 hc h)))).unch hu5 (nm1 (hg4 _ v3) G3 (fun hc => x3 _ (hov _ (u5 hc)) (fun h => o53 hc h)))).unch hu6 (nm2 (hg5 _ (hg4 _ v3)) G3 (fun hc => x3 _ (hov _ (u6 hc)) (fun h => o63 hc h)))
  have hD4f : DynAt m6 Block.work4 Block.work4Sz 4 c4 b4 :=
    ((hD4').keep hu5 (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (glm (g4 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (fun _ => Keep.unch hu5 (nm1 v4 G4 (fun hc => x4 _ (hov _ (u5 hc)) (fun h => o54 hc h))))).keep hu6 (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (fun _ => Keep.unch hu6 (nm2 (hg5 _ v4) G4 (fun hc => x4 _ (hov _ (u6 hc)) (fun h => o64 hc h))))
  have hK5f : MarksAt m6 mc1 mb1 st1' mk1' :=
    (hK5).unch hu6 (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (glm2 (g5 _ (gv _ (by decide))) (by decide) (by decide) (by decide) (by decide)) (fun _ => nm2 (Alloc.Malloced.valid (hK5.dyn.mal hc5)) G5 (fun hc => x5 _ (hov _ (u6 hc)) (fun h => o65 hc h)))
  -- the total change
  have hsc : ∀ {z : block}, z ∈ scrGlobals → proSet L m z := fun h => .inl h
  have hun : Unch m m6 (proSet L m) := by
    refine (((((hu1.mono fun z hz => ?_).trans (hu2.mono fun z hz => ?_)).trans (hu3.mono fun z hz => ?_)).trans
      (hu4.mono fun z hz => ?_)).trans (hu5.mono fun z hz => ?_)).trans (hu6.mono fun z hz => ?_)
    · rcases hz with rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩
      · exact hsc (by decide)
      · exact hsc (by decide)
      · exact .inr (.inr (.inr (.inl (u1 hc))))
      · exact .inr (.inr (.inr (.inr hnv)))
    · rcases hz with rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩
      · exact hsc (by decide)
      · exact hsc (by decide)
      · exact .inr (.inr (.inr (.inl (u2 hc))))
      · exact .inr (.inr (.inr (.inr fun h => hnv (hg1 _ h))))
    · rcases hz with rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩
      · exact hsc (by decide)
      · exact hsc (by decide)
      · exact .inr (.inr (.inr (.inl (u3 hc))))
      · exact .inr (.inr (.inr (.inr fun h => hnv (g12 _ h))))
    · rcases hz with rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩
      · exact hsc (by decide)
      · exact hsc (by decide)
      · exact .inr (.inr (.inr (.inl (u4 hc))))
      · exact .inr (.inr (.inr (.inr fun h => hnv (g3 _ h))))
    · rcases hz with rfl | rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩
      · exact hsc (by decide)
      · exact hsc (by decide)
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inr (.inl (u5 hc))))
      · exact .inr (.inr (.inr (.inr fun h => hnv (g4 _ h))))
    · rcases hz with rfl | rfl | rfl | ⟨hc, rfl⟩ | ⟨hnv, rfl⟩
      · exact hsc (by decide)
      · exact hsc (by decide)
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr (.inl (u6 hc))))
      · exact .inr (.inr (.inr (.inr fun h => hnv (g5 _ h))))
  have g6 : ∀ z, Mem.valid_block m z → Mem.valid_block m6 z := fun z h => hg6 _ (g5 _ h)
  have nbase : ∀ z, z ∈ L.cblocks ++ L.gblocks → ¬ proSet L m z := fun z hz h => by
    have hg := hs.glob z hz
    rcases h with h | h | h | h | h
    · exact hg (List.mem_append_left _ h)
    · exact hg (List.mem_append_right _ (h ▸ by decide))
    · exact hg (List.mem_append_right _ (h ▸ by decide))
    · exact (hs.scrValid z h).1 hz
    · exact h (hs.valid z hz)
  have ntbl : ∀ z, z = Block.bit ∨ z = (NautyEnv.leftbit : block) → ¬ proSet L m z := fun z hz h => by
    rcases hz with rfl | rfl <;> rcases h with h | h | h | h | h
    all_goals first
      | exact absurd h (by decide)
      | exact (hs.scrValid _ h).2 (by decide)
      | exact h (gv _ (by decide))
  obtain ⟨w1v, hw1⟩ := Alloc.malloced_array (hD1f.mal (by omega)) .Mint32 4 rfl rfl c1 (by omega)
  obtain ⟨w2v, hw2⟩ := Alloc.malloced_array (hD2f.mal (by omega)) .Mint32 4 rfl rfl c2 (by omega)
  obtain ⟨w4v, hw4⟩ := Alloc.malloced_array (hD4f.mal (by omega)) .Mint32 4 rfl rfl c4 (by omega)
  let L1 := L.withScr c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2
  let S1 : Scr := ⟨w1v, w2v, H, w4v, st1', mk1', st2', mk2', aw⟩
  have cb : ∀ {z : block}, z ∈ L.cblocks ++ L.gblocks → ¬ proSet L m z := fun hz => nbase _ hz
  have hm6 : Mem m6 L1 G (start0 lab ptn active numcells) S1 :=
    { graph := hgr.unch hun (cb (by simp [Loc.gblocks])) (cb (by simp [Loc.gblocks]))
        (cb (by simp [Loc.gblocks])) (cb (by simp [Loc.gblocks]))
      lab := hlab.unch hun (cb (by simp [Loc.cblocks]))
      ptn := hptn.unch hun (cb (by simp [Loc.cblocks]))
      nc := hnc.unch hun (cb (by simp [Loc.cblocks]))
      act := hact.unch hun (cb (by simp [Loc.cblocks]))
      actRep := hrep
      code := let ⟨kv, hkv⟩ := hcode; ⟨kv, hkv.unch hun (cb (by simp [Loc.cblocks]))⟩
      d1 := hD1f, d2 := hD2f, d3 := hD3f, d4 := hD4f
      w1 := hw1, w2 := hw2, w3 := hHf, w4 := hw4
      k1 := hK5f, k2 := hK6
      bit := fun q hq => by rw [hun.load _ _ _ (ntbl _ (.inl rfl))]; exact hbit q hq
      left := fun q hq => by
        erw [hun.load _ _ _ (ntbl _ (.inr rfl))]; exact hleft q hq }
  have hok1 : Ok n L1 := Ok.withScr hs hbv hov hg1 hg2 hg3 hg4 hg5 hg6 p1 p2 p3 p4 p5 p6 hn1 hn2 hn3 hn4
    hn5 hn6
  have e4 : ∀ y, y ∉ proTemps → PTree.get y le4 = PTree.get y le := fun y hy => by
    simp only [proTemps, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.mem_nil_iff, or_false, not_or, not_exists, not_and] at hy
    have h := fun i (hi : i < 8) (e : y = idOf (703 + i)) => hy.2 i hi e.symm
    rw [ho4 _ (fun e => h 6 (by decide) e) (fun e => h 7 (by decide) e),
      ho3 _ (fun e => h 4 (by decide) e) (fun e => h 5 (by decide) e),
      ho2 _ (fun e => h 2 (by decide) e) (fun e => h 3 (by decide) e),
      ho1 _ (fun e => h 0 (by decide) e) (fun e => h 1 (by decide) e)]
    rw [temps_gso _ _ hy.1.2.2, temps_gso _ _ hy.1.2.1, temps_gso _ _ hy.1.1]
  have ea : ∀ y, y ∈ [id.g, id.lab, id.ptn, id.level, id.numcells, id.active, id.code, id.m, id.n] →
      PTree.get y le4 = PTree.get y le := fun y hy => e4 y (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have ev : PTree.get id.v le4 = some (.Vptr L.bv L.vo) ∧ PTree.get id.d le4 = some (.Vptr L.bd L.dofs) ∧
      PTree.get id.e le4 = some (.Vptr L.be L.eo) := by
    have h := fun y (hy : y ∈ [id.v, id.d, id.e]) => show PTree.get y le4 = PTree.get y le0 by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rw [ho4 _ (by rcases hy with rfl | rfl | rfl <;> decide) (by rcases hy with rfl | rfl | rfl <;> decide),
        ho3 _ (by rcases hy with rfl | rfl | rfl <;> decide) (by rcases hy with rfl | rfl | rfl <;> decide),
        ho2 _ (by rcases hy with rfl | rfl | rfl <;> decide) (by rcases hy with rfl | rfl | rfl <;> decide),
        ho1 _ (by rcases hy with rfl | rfl | rfl <;> decide) (by rcases hy with rfl | rfl | rfl <;> decide)]
    refine ⟨?_, ?_, ?_⟩
    · rw [h _ (by simp)]; simp (config := {decide := true}) only [le0, temps_gso, temps_gss]
    · rw [h _ (by simp)]; simp (config := {decide := true}) only [le0, temps_gso, temps_gss]
    · rw [h _ (by simp)]; simp (config := {decide := true}) only [le0, temps_gso, temps_gss]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  rw [Exec.evalExpr, eval_nc' hm6 (by rw [ea _ (by simp)]; exact ha.numcells)]
  simp only [typeof, cop, cast_int_long_ir (a := numcells) ⟨by omega, by omega⟩]
  simp only [E0_append]
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, E0_append]
  have hcl : Cfrontend.Cop.cast_int_long .Signed (ir (numcells : Int)) = lr numcells :=
    cast_int_long_ir ⟨by omega, by omega⟩
  have hx : ∀ y, y ∈ [id.g, id.lab, id.ptn, id.level, id.numcells, id.active, id.code, id.m, id.n] →
      PTree.get y (PTree.set id.nactive (.Vint (Lib.Integers.Int.repr (zOfInt 0)))
        (PTree.set id.longcode (.Vlong (lr numcells)) le4)) = PTree.get y le := fun y hy => by
    have hne : y ≠ id.nactive ∧ y ≠ id.longcode := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
    rw [temps_gso _ _ hne.1, temps_gso _ _ hne.2, ea y hy]
  have ht6 : Tmp (PTree.set id.nactive (.Vint (Lib.Integers.Int.repr (zOfInt 0)))
      (PTree.set id.longcode (.Vlong (lr numcells)) le4)) L1 (start0 lab ptn active numcells) :=
    { g := by rw [hx _ (by simp)]; exact ha.g
      lab := by rw [hx _ (by simp)]; exact ha.lab
      ptn := by rw [hx _ (by simp)]; exact ha.ptn
      level := by rw [hx _ (by simp)]; exact ha.level
      numcells := by rw [hx _ (by simp)]; exact ha.numcells
      active := by rw [hx _ (by simp)]; exact ha.active
      code := by rw [hx _ (by simp)]; exact ha.code
      m := by rw [hx _ (by simp)]; exact ha.m
      n := by rw [hx _ (by simp)]; exact ha.n
      v := by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact ev.1
      d := by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact ev.2.1
      e := by rw [temps_gso _ _ (by decide), temps_gso _ _ (by decide)]; exact ev.2.2
      longcode := by rw [temps_gso _ _ (by decide), temps_gss]; rfl
      nactive := by rw [temps_gss]; rfl }
  rw [show Cfrontend.Cop.cast_int_long .Signed
    (ir ((Hex.GraphIso.Nauty.Sparse.Refinement.start lab ptn active numcells (Scratch.fresh n)).numcells : Int))
    = lr numcells from hcl]
  exact hQ c1 b1 c2 b2 c3 b3 c4 b4 mc1 mb1 mc2 mb2 _ m6 S1 hok1 hm6 ht6 hHs hHl hor1
    (hor2.imp_right fun h hv => h (hg1 _ hv))
    (by rcases hor3 with ⟨h1, h2, -⟩ | ⟨hnv, -⟩
        · exact .inl ⟨h1, h2⟩
        · exact .inr fun hv => hnv (g12 _ hv))
    (hor4.imp_right fun h hv => h (g3 _ hv)) (hor5.imp_right fun h hv => h (g4 _ hv))
    (hor6.imp_right fun h hv => h (g5 _ hv)) hun g6 fun y hy h1 h2 => by
      rw [temps_gso _ _ h2, temps_gso _ _ h1, e4 y hy]

end NautyVerified.Proofs.Sparse.Refine

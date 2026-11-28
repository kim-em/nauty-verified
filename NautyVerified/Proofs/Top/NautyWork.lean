import NautyVerified.Proofs.Top.NautyStats

/-!
# `nauty()`'s workspace and search flags (`tWork`)

`worksize = 2 * 500 * m >= 2 * m`, so `workspace = ws_arg`, `worktop` is
`worksize` setwords on, `fmptr = workspace`; then `stats->errstatus = 0`,
`needshortprune = 0`, `invarsuclevel = NAUTY_INFINITY` and the invariant
counters are zeroed.
-/

namespace NautyVerified.Proofs.Top

variable {bI : CompCert4Lean.Common.Values.block}

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.AST
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Spec
open NautyVerified.Source
open NautyVerified.Proofs.Search (FieldAt IntAt PtrAt SLoc)

set_option linter.unusedSimpArgs false

/-- `a % b` for `b` dividing `a`. -/
theorem ir_mods_dvd {a b : _root_.Int} (ha : InInt a) (hb : InInt b) (hd : b ∣ a) :
    Lib.Integers.Int.mods (ir a) (ir b) = ir 0 := by
  have hs : ∀ x, InInt x → Lib.Integers.WordCore.signed (ir x) = zOfInt x := fun x hx => by
    apply intOfZ_injective
    rw [show Lib.Integers.WordCore.signed (ir x) = Lib.Integers.Int.signed (ir x) from rfl,
      intOfZ_Int_signed, toInt_ir hx, intOfZ_zOfInt]
  show Lib.Integers.WordCore.repr _ (ZArith.BinInt.Z.sub (Lib.Integers.WordCore.signed (ir a))
    (ZArith.BinInt.Z.mul (ZArith.BinInt.Z.quot (Lib.Integers.WordCore.signed (ir a))
      (Lib.Integers.WordCore.signed (ir b))) (Lib.Integers.WordCore.signed (ir b)))) = _
  rw [hs a ha, hs b hb]
  show Lib.Integers.Int.repr _ = Lib.Integers.Int.repr (zOfInt 0)
  congr 1
  apply intOfZ_injective
  simp [intOfZ_sub, intOfZ_mul, ZArith.BinInt.Z.quot, intOfZ_zOfInt, Int.tdiv_mul_cancel hd]

variable {xi : ExternalCalls}

/-- The workspace pointers and search flags (`tWork`). -/
theorem wp_tWork {Q : Post} {le : temp_env} {m : mem} {S : SLoc} {M : Nat} {bD : block}
    (hso : S.sofs = Ptrofs.zero)
    (hws : PTree.get dense.id.«worksize» le = some (.Vint (ir ((2 * 500 * M : Nat) : _root_.Int))))
    (hwa : PTree.get dense.id.«ws_arg» le = some (.Vptr bD Ptrofs.zero))
    (hM0 : 0 < M) (hM : 2 * 500 * M < 2147483648)
    (hMm : IntAt m Search.Block.m M)
    (hst : PtrAt m Search.Block.stats (.Vptr S.bst S.sofs))
    (hwE : Mem.valid_access m .Mint32 S.bst (zOfInt (S.sb + 20)) .Writable)
    (hW : ∀ x ∈ [(Mint64, Search.Block.workspace), (Mint64, Search.Block.worktop),
      (Mint64, Search.Block.fmptr), (Mint32, Search.Block.needshortprune),
      (Mint32, Search.Block.invarsuclevel), (Mint64, Search.Block.invsuccesses),
      (Mint64, Search.Block.invapplics)], Mem.valid_access m x.1 x.2 (zOfInt 0) .Writable)
    (hsep : S.bst ≠ Search.Block.workspace ∧
      S.bst ≠ Search.Block.worktop ∧ S.bst ≠ Search.Block.fmptr ∧
      S.bst ≠ Search.Block.needshortprune ∧ S.bst ≠ Search.Block.invarsuclevel ∧
      S.bst ≠ Search.Block.invsuccesses ∧ S.bst ≠ Search.Block.invapplics ∧
      S.bst ≠ Search.Block.m ∧ S.bst ≠ Search.Block.stats)
    (hQ : ∀ le' m', PtrAt m' Search.Block.workspace (.Vptr bD Ptrofs.zero) →
      PtrAt m' Search.Block.worktop (.Vptr bD (Ptrofs.repr (zOfInt (0 + 8 * (2 * 500 * M))))) →
      PtrAt m' Search.Block.fmptr (.Vptr bD (Ptrofs.repr (zOfInt (0 + 8 * (2 * M * 0))))) →
      FieldAt m' .Mint32 S.bst (S.sb + 20) (.Vint (ir 0)) →
      IntAt m' Search.Block.needshortprune 0 → IntAt m' Search.Block.invarsuclevel 2000000002 →
      FieldAt m' .Mint64 Search.Block.invsuccesses 0 (.Vlong (lr 0)) →
      FieldAt m' .Mint64 Search.Block.invapplics 0 (.Vlong (lr 0)) →
      (∀ c o p, Mem.valid_access m c S.bst o p → Mem.valid_access m' c S.bst o p) →
      Unch m m' (fun z => z = S.bst ∨ z = Search.Block.workspace ∨ z = Search.Block.worktop ∨
        z = Search.Block.fmptr ∨ z = Search.Block.needshortprune ∨ z = Search.Block.invarsuclevel ∨
        z = Search.Block.invsuccesses ∨ z = Search.Block.invapplics) →
      (∀ z, Mem.valid_block m z → Mem.valid_block m' z) →
      (∀ x, x ≠ idOf 734 → PTree.get x le' = PTree.get x le) →
      Wp xi ge dense.fn.nauty Nauty.tRoot Q (nEnv bI) le' m') :
    Wp xi ge dense.fn.nauty Nauty.tWork Q (nEnv bI) le m := by
  have hm2 := Search.eval_gint (e := nEnv bI) (le := le) rfl Search.find_m hMm
  have h2m : ∀ m', IntAt m' Search.Block.m M → ∀ le', Exec.evalExpr ge (nEnv bI) le' m'
      (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint) = some (.Vint (ir (2 * M))) := by
    intro m' h le'
    rw [Exec.evalExpr, Search.eval_gint (e := nEnv bI) rfl Search.find_m h]
    simp only [Exec.evalExpr, typeof, cop, ir_mul]
  simp only [Nauty.tWork, Set.sk]
  wp_step; wp_step; wp_step
  apply wp_if_eval
  rw [Exec.evalExpr, h2m m hMm]
  simp only [Exec.evalExpr, hws, typeof, cop]
  rw [ir_lt (a := ((2 * 500 * M : Nat) : _root_.Int)) (b := 2 * (M : _root_.Int))
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  rw [if_pos (by simp; omega)]
  have W1 := hW _ (.head _)
  have W2 := hW _ (.tail _ (.head _))
  have W3 := hW _ (.tail _ (.tail _ (.head _)))
  have W4 := hW _ (.tail _ (.tail _ (.tail _ (.head _))))
  have W5 := hW _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have W6 := hW _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have W7 := hW _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  simp only at W1 W2 W3 W4 W5 W6 W7
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9⟩ := hsep
  have hpc : ∀ (b : block) (o : ptrofs) m', Cfrontend.Cop.sem_cast (.Vptr b o) (tptr tulong) (tptr tulong) m' =
      some (.Vptr b o) := fun _ _ _ => rfl
  wp_step; wp_step
  refine wp_gset (v := .Vptr bD Ptrofs.zero) rfl Search.find_workspace rfl W1
    (by simp only [Exec.evalExpr, Set.pv, hwa]) rfl (hpc _ _ _) rfl ?_
  intro m1 hP1 hu1 hv1 ha1 hp1
  simp only [seqPost, Post.after, E0_append]
  have hM1 : IntAt m1 Search.Block.m M := hMm.unch hu1 (by decide)
  have hmod : Exec.evalExpr ge (nEnv bI) le m1 (.Ebinop .Omod (Refine.tv dense.id.«worksize»)
      (.Ebinop .Omul (ci 2 tint) (.Evar dense.id.«nauty:m» tint) tint) tint) = some (.Vint (ir 0)) := by
    rw [Exec.evalExpr, h2m m1 hM1]
    simp only [Exec.evalExpr, Refine.tv, hws, typeof]
    simp [Cfrontend.Cop.sem_binary_operation, Cfrontend.Cop.sem_mod, Cfrontend.Cop.sem_binarith,
      Cfrontend.Cop.classify_binarith, Cfrontend.Cop.sem_cast, Cfrontend.Cop.classify_cast,
      Cfrontend.Cop.binarith_type, CompCert4Lean.X86_64.Archi.ptr64, Cfrontend.Cop.cast_int_int]
    have hb : ∀ x : _root_.Int, InInt x → BitVec.ofInt 32 (intOfZ (zOfInt x)) = bv32 (ir x) :=
      fun x _ => by rw [bv32_ir, intOfZ_zOfInt]
    refine ⟨⟨fun h => ?_, fun h => absurd h ?_⟩, ir_mods_dvd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨500, by push_cast; omega⟩⟩
    · rw [hb _ ⟨by omega, by omega⟩] at h
      have := congrArg BitVec.toInt h
      rw [toInt_ir ⟨by omega, by omega⟩] at this
      simp at this; omega
    · intro h
      rw [hb _ ⟨by omega, by omega⟩] at h
      have := congrArg BitVec.toInt h
      rw [toInt_ir ⟨by omega, by omega⟩, BitVec.toInt_ofInt] at this
      have h2 : intOfZ Lib.Integers.Int.min_signed = -2147483648 := by decide
      erw [h2] at this
      simp at this; omega
  have hwsp : ∀ m', PtrAt m' Search.Block.workspace (.Vptr bD Ptrofs.zero) → Exec.evalExpr ge (nEnv bI) le m'
      (.Evar dense.id.«nauty:workspace» (tptr tulong)) = some (.Vptr bD Ptrofs.zero) := fun m' h => by
    simp only [Exec.evalExpr, Exec.lvalOfVar, show PTree.get dense.id.«nauty:workspace» (nEnv bI) = none
      from rfl, Search.find_workspace, Exec.derefLoc, Cfrontend.Ctypes.access_mode, Mem.loadv,
      Alloc.Mptr_eq, show Ptrofs.unsigned Ptrofs.zero = zOfInt 0 from rfl, h.load]
  wp_step; wp_step; wp_step
  refine wp_gset (ty := tptr tulong) (chunk := .Mint64) (v := .Vptr bD (Ptrofs.repr (zOfInt (0 + 8 * (2 * 500 * M))))) rfl Search.find_worktop rfl
    (ha1 _ _ _ _ W2) ?_ rfl (hpc _ _ _) rfl ?_
  · rw [Exec.evalExpr, hwsp m1 hP1, Exec.evalExpr, hmod]
    simp only [Exec.evalExpr, Refine.tv, hws, typeof, cop, ir_sub]
    rw [show ((2 * 500 * M : Nat) : _root_.Int) - 0 = ((2 * 500 * M : Nat) : _root_.Int) by omega,
      add_ptrTo Ptrofs.zero _ (2 * 500 * M) (by omega), Set.sizeof_tulong]
    congr 3
  intro m2 hT2 hu2 hv2 ha2 hp2
  simp only [seqPost, Post.after, E0_append]
  have hP2 := hP1.unch hu2 (by decide)
  wp_step; wp_step; wp_step
  refine wp_gset (ty := tptr tulong) (chunk := .Mint64) (v := .Vptr bD Ptrofs.zero) rfl Search.find_fmptr rfl
    (ha2 _ _ _ _ (ha1 _ _ _ _ W3)) (hwsp m2 hP2) rfl (hpc _ _ _) rfl ?_
  intro m3 hF3 hu3 hv3 ha3 hp3
  simp only [seqPost, Post.after, E0_append]
  have hst3 : PtrAt m3 Search.Block.stats (.Vptr S.bst S.sofs) :=
    ((hst.unch hu1 (by decide)).unch hu2 (by decide)).unch hu3 (by decide)
  wp_step; wp_step; wp_step
  refine Search.wp_statsStore (S := S) (ty := tint) (chunk := .Mint32) (off := 20) (w' := .Vint (ir 0)) rfl
    Search.field_statsErrstatus rfl hst3 (by decide) (by simp [SLoc.sb, hso])
    (ha3 _ _ _ _ (ha2 _ _ _ _ (ha1 _ _ _ _ hwE))) rfl rfl ?_
  intro m4 hs4
  have hE4 := FieldAt.store_same hs4 (ha3 _ _ _ _ (ha2 _ _ _ _ (ha1 _ _ _ _ hwE)))
  have hu4 : Unch m3 m4 (· = S.bst) := Unch.store hs4 rfl
  have ha4 : ∀ c b o p, Mem.valid_access m3 c b o p → Mem.valid_access m4 c b o p :=
    fun c b o p h => Mem.store_valid_access_1 _ _ _ _ _ _ hs4 _ _ _ _ h
  have hv4 : ∀ z, Mem.valid_block m3 z → Mem.valid_block m4 z :=
    fun z h => Mem.store_valid_block_1 _ _ _ _ _ _ hs4 _ h
  simp only [seqPost, Post.after, E0_append]
  have hA : ∀ {c b}, Mem.valid_access m c b (zOfInt 0) .Writable → b ≠ S.bst →
      Mem.valid_access m4 c b (zOfInt 0) .Writable := fun h _ =>
    ha4 _ _ _ _ (ha3 _ _ _ _ (ha2 _ _ _ _ (ha1 _ _ _ _ h)))
  wp_step; wp_step; wp_step
  refine wp_gset (ty := tint) (chunk := .Mint32) (v := .Vint (ir 0)) rfl Search.find_needshortprune rfl
    (hA W4 (Ne.symm hq4)) rfl rfl rfl rfl ?_
  intro m5 hN5 hu5 hv5 ha5 hp5
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step
  refine wp_gset (ty := tint) (chunk := .Mint32) (v := .Vint (ir 2000000002)) rfl Search.find_invarsuclevel rfl
    (ha5 _ _ _ _ (hA W5 (Ne.symm hq5))) rfl rfl rfl rfl ?_
  intro m6 hI6 hu6 hv6 ha6 hp6
  simp only [seqPost, Post.after, E0_append]
  wp_step; wp_step; wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof]
  rw [show Cfrontend.Cop.sem_cast (.Vint (Lib.Integers.Int.repr (zOfInt 0))) tint tulong m6 =
    some (.Vlong (lr 0)) from rfl]
  simp only []
  have hlc : ∀ m', Cfrontend.Cop.sem_cast (.Vlong (lr 0)) tulong tulong m' = some (.Vlong (lr 0)) :=
    fun _ => rfl
  refine wp_gset (ty := tulong) (chunk := .Mint64) (v := .Vlong (lr 0)) rfl Search.find_invsuccesses rfl
    (ha6 _ _ _ _ (ha5 _ _ _ _ (hA W6 (Ne.symm hq6)))) (by simp [Exec.evalExpr, temps_gss]) rfl (hlc _) rfl ?_
  intro m7 hS7 hu7 hv7 ha7 hp7
  simp only [seqPost, Post.after, E0_append]
  refine wp_gset (ty := tulong) (chunk := .Mint64) (v := .Vlong (lr 0)) rfl Search.find_invapplics rfl
    (ha7 _ _ _ _ (ha6 _ _ _ _ (ha5 _ _ _ _ (hA W7 (Ne.symm hq7))))) (by simp [Exec.evalExpr, temps_gss]) rfl
    (hlc _) rfl ?_
  intro m8 hA8 hu8 hv8 ha8 hp8
  simp only [seqPost, Post.after, E0_append]
  refine wp_conseq (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ h => h) ?_
  have hU : Unch m m8 (fun z => z = S.bst ∨ z = Search.Block.workspace ∨ z = Search.Block.worktop ∨
      z = Search.Block.fmptr ∨ z = Search.Block.needshortprune ∨ z = Search.Block.invarsuclevel ∨
      z = Search.Block.invsuccesses ∨ z = Search.Block.invapplics) :=
    ((((((((hu1.mono fun _ h => .inr (.inl h)).trans (hu2.mono fun _ h => .inr (.inr (.inl h)))).trans
      (hu3.mono fun _ h => .inr (.inr (.inr (.inl h))))).trans (hu4.mono fun _ h => .inl h)).trans
      (hu5.mono fun _ h => .inr (.inr (.inr (.inr (.inl h)))))).trans
      (hu6.mono fun _ h => .inr (.inr (.inr (.inr (.inr (.inl h))))))).trans
      (hu7.mono fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))).trans
      (hu8.mono fun _ h => .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))))
  have k48 : ∀ {c b o v}, FieldAt m4 c b o v → b ≠ Search.Block.needshortprune →
      b ≠ Search.Block.invarsuclevel → b ≠ Search.Block.invsuccesses → b ≠ Search.Block.invapplics →
      FieldAt m8 c b o v := fun h h5 h6 h7 h8 =>
    (((h.unch hu5 h5).unch hu6 h6).unch hu7 h7).unch hu8 h8
  refine hQ _ m8
    (k48 ((((hP2.unch hu3 (by decide))).unch hu4 hq1.symm)) (by decide) (by decide) (by decide) (by decide))
    (k48 ((hT2.unch hu3 (by decide)).unch hu4 hq2.symm) (by decide) (by decide) (by decide) (by decide))
    (by
      rw [show (0 : _root_.Int) + 8 * (2 * (M : _root_.Int) * 0) = 0 by omega]
      exact k48 (hF3.unch hu4 hq3.symm) (by decide) (by decide) (by decide) (by decide))
    (k48 hE4 hq4 hq5 hq6 hq7)
    (((hN5.unch hu6 (by decide)).unch hu7 (by decide)).unch hu8 (by decide))
    ((hI6.unch hu7 (by decide)).unch hu8 (by decide)) (hS7.unch hu8 (by decide)) hA8
    (fun c o p h => ha8 _ _ _ _ (ha7 _ _ _ _ (ha6 _ _ _ _ (ha5 _ _ _ _ (ha4 _ _ _ _
      (ha3 _ _ _ _ (ha2 _ _ _ _ (ha1 _ _ _ _ h)))))))) hU
    (fun z h => hv8 _ (hv7 _ (hv6 _ (hv5 _ (hv4 _ (hv3 _ (hv2 _ (hv1 _ h))))))))
    (fun x hx => temps_gso _ _ hx)

end NautyVerified.Proofs.Top

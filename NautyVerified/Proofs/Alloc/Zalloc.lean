import NautyVerified.Proofs.Alloc.Malloc
import NautyVerified.Logic.Wp
import NautyVerified.Logic.Simp
import NautyVerified.Exec.Cop
import NautyVerified.Proofs.Nextelement.Satisfies

/-!
# `nauty_zalloc` meets its specification

`zallocSpec sz`: the harness's zero-filling allocator returns a fresh block
(`Fresh`, as `malloc`) whose `sz` bytes are all zero.
-/

namespace NautyVerified.Proofs.Alloc

open CompCert4Lean CompCert4Lean.Cfrontend.Clight CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values CompCert4Lean.Common.ExternalCalls CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory CompCert4Lean.Common.Memtype CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Foundation.Numbers.Rocq.Coq CompCert4Lean.Lib.Maps CompCert4Lean.Lib.Integers
open NautyVerified NautyVerified.Logic NautyVerified.Program NautyVerified.Word NautyVerified.Proofs
open NautyVerified.Source

namespace Z
abbrev sz : Common.AST.ident := dense.id.sz
abbrev p : Common.AST.ident := dense.id.p
abbrev i : Common.AST.ident := dense.id.i
abbrev t : Common.AST.ident := idOf 703

abbrev sk (s : statement) : statement := .Ssequence .Sskip s

/-- `for (i = 0; i < sz; ++i) p[i] = 0;` -/
abbrev fill : statement :=
  .Ssequence (sk (.Sset i (.Ecast (ci 0 tint) tulong)))
    (.Sloop
      (.Ssequence
        (sk (.Sifthenelse (.Ebinop .Olt (.Etempvar i tulong) (.Etempvar sz tulong) tint) .Sskip .Sbreak))
        (sk (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar p (tptr tuchar)) (.Etempvar i tulong)
          (tptr tuchar)) tuchar) (ci 0 tint))))
      (sk (.Sset i (.Ebinop .Oadd (.Etempvar i tulong) (ci 1 tint) tulong))))

abbrev body : statement :=
  .Ssequence
    (.Ssequence (sk (.Scall (some t) (.Evar dense.id.malloc (tfun [tulong] (tptr .Tvoid)))
      [.Etempvar sz tulong])) (.Sset p (.Etempvar t (tptr .Tvoid))))
    (.Ssequence (sk (.Sifthenelse (.Etempvar p (tptr tuchar)) fill .Sskip))
      (sk (.Sreturn (some (.Etempvar p (tptr tuchar))))))

kernel_rfl body_eq : dense.body.nauty_zalloc = body
end Z

/-- A zero byte. -/
abbrev zb : memval := .Byte (Byte.repr (zOfInt 0))

theorem encode_zero :
    encode_val .Mint8unsigned (.Vint (Int.zero_ext (zOfInt 8) (ir 0))) = [zb] := rfl

theorem toNat_lr {k : Nat} (hk : k < 2 ^ 63) : (bv64 (lr k)).toNat = k := by
  rw [bv64_repr, intOfZ_zOfInt, BitVec.toNat_ofInt]; omega

theorem addr_byte (ce : Cfrontend.Ctypes.composite_env) {k : Nat} (hk : k < 2 ^ 63) :
    Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul
      (Ptrofs.repr (Cfrontend.Ctypes.sizeof ce tuchar)) (Ptrofs.of_int64 (lr k)))) = zOfInt k := by
  apply intOfZ_injective
  rw [intOfZ_Ptrofs_unsigned, intOfZ_zOfInt]
  simp only [bvp_add, bvp_zero, bvp_mul, bvp_repr, bvp_of_int64]
  have h1 : intOfZ (Cfrontend.Ctypes.sizeof ce tuchar) = 1 := rfl
  rw [h1]
  have : (0 + BitVec.ofInt 64 1 * bv64 (lr k)) = bv64 (lr k) := by
    rw [show BitVec.ofInt 64 1 = 1#64 from rfl, BitVec.one_mul]; simp
  rw [this, toNat_lr hk]

theorem ltu_lr {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Lib.Integers.Int64.ltu (lr a) (lr b) = decide (a < b) := by
  rw [bv64_ltu, toNat_lr ha, toNat_lr hb]

theorem add_lr_one {k : Nat} :
    Lib.Integers.Int64.add (lr k) (Lib.Integers.Int64.repr
      (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 1)))) = lr (k + 1) := by
  apply bv64_inj.1
  simp only [bv64_add, bv64_repr, intOfZ_zOfInt]
  rw [show intOfZ (Lib.Integers.Int.signed (Lib.Integers.Int.repr (zOfInt 1))) = 1 from rfl,
    ← BitVec.ofInt_add]

/-- What the zero-filling loop keeps: memory below offset 0 of `b` (the
`malloc` header) and permissions. -/
structure Keeps (m m' : mem) (b : block) : Prop where
  unch : Unch m m' (· = b)
  low : ∀ chunk (ofs : Int), ofs + csize chunk ≤ 0 →
    Mem.load chunk m' b (zOfInt ofs) = Mem.load chunk m b (zOfInt ofs)
  perm : ∀ b' ofs k p, Mem.perm m b' ofs k p → Mem.perm m' b' ofs k p
  grow : ∀ z, Mem.valid_block m z → Mem.valid_block m' z

theorem Keeps.refl (m : mem) (b : block) : Keeps m m b :=
  ⟨Unch.refl _ _, fun _ _ _ => rfl, fun _ _ _ _ h => h, fun _ h => h⟩

theorem Keeps.trans {m₁ m₂ m₃ : mem} {b : block} (h₁ : Keeps m₁ m₂ b) (h₂ : Keeps m₂ m₃ b) :
    Keeps m₁ m₃ b :=
  ⟨h₁.unch.trans h₂.unch, fun c o h => by rw [h₂.low c o h, h₁.low c o h],
    fun _ _ _ _ h => h₂.perm _ _ _ _ (h₁.perm _ _ _ _ h), fun _ h => h₂.grow _ (h₁.grow _ h)⟩

variable {xi : ExternalCalls}

theorem wp_fill {f : function} {Q : Post} {e : env} {le : temp_env} {m : mem} {b : block} {sz : Nat}
    (hsz : sz < 2 ^ 62) (hp : PTree.get Z.p le = some (.Vptr b Ptrofs.zero))
    (hs : PTree.get Z.sz le = some (.Vlong (lr sz)))
    (hperm : ∀ ofs : Int, 0 ≤ ofs → ofs < sz → Mem.perm m b (zOfInt ofs) .Cur .Freeable)
    (hQ : ∀ le' m', Mem.loadbytes m' b (zOfInt 0) (zOfInt sz) = some (List.replicate sz zb) →
      Keeps m m' b → (∀ k, k ≠ Z.i → PTree.get k le' = PTree.get k le) → Q.normal E0 e le' m') :
    Wp xi ge f Z.fill Q e le m := by
  wp_step; wp_step; wp_step
  apply wp_set_eval
  simp only [Exec.evalExpr, typeof, cop, cast_int_long_ir (a := 0) ⟨by decide, by decide⟩, E0_append]
  let I := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ k, k ≤ sz ∧ v = sz - k ∧ PTree.get Z.i le' = some (.Vlong (lr k)) ∧
      Mem.loadbytes m' b (zOfInt 0) (zOfInt k) = some (List.replicate k zb) ∧ Keeps m m' b ∧
      ∀ k', k' ≠ Z.i → PTree.get k' le' = PTree.get k' le
  let J := fun (v : Nat) (t : trace) (e' : env) (le' : temp_env) (m' : mem) => t = E0 ∧ e = e' ∧
    ∃ k, k < sz ∧ v = sz - k ∧ PTree.get Z.i le' = some (.Vlong (lr k)) ∧
      Mem.loadbytes m' b (zOfInt 0) (zOfInt (k + 1)) = some (List.replicate (k + 1) zb) ∧
      Keeps m m' b ∧ ∀ k', k' ≠ Z.i → PTree.get k' le' = PTree.get k' le
  refine wp_loop (I := I) (J := J) ?_ ?_ (n := sz)
    ⟨rfl, rfl, 0, Nat.zero_le _, rfl, temps_gss _ _ _, Mem.loadbytes_empty _ _ _ _ (by decide),
      Keeps.refl _ _, fun k hk => temps_gso _ _ hk⟩
  · rintro v t e' le' m' ⟨rfl, rfl, k, hk, rfl, hik, hbytes, hkeep, ho⟩
    have hs' : PTree.get Z.sz le' = some (.Vlong (lr sz)) := by rw [ho _ (by decide)]; exact hs
    have hp' : PTree.get Z.p le' = some (.Vptr b Ptrofs.zero) := by rw [ho _ (by decide)]; exact hp
    wp_step; wp_step; wp_step
    apply wp_if_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m' (.Etempvar Z.i tulong) = _ from hik,
      show Exec.evalExpr ge e le' m' (.Etempvar Z.sz tulong) = _ from hs']
    simp only [typeof, cop, ltu_lr (a := k) (b := sz) (by omega) (by omega)]
    by_cases hks : k < sz
    · rw [ite_eq_left (by simpa using hks)]
      apply wp_skip
      have hva : Mem.valid_access m' .Mint8unsigned b (zOfInt k) .Writable := by
        refine ⟨fun o ho' => ?_, ⟨zOfInt k, by
          apply intOfZ_injective
          simp [intOfZ_zOfInt, show intOfZ (align_chunk .Mint8unsigned) = 1 from rfl]⟩⟩
        have h1 : (k : Int) ≤ intOfZ o := by have := ho'.1; change intOfZ _ ≤ intOfZ _ at this; simpa [intOfZ_zOfInt] using this
        have h2 : intOfZ o < k + 1 := by
          have := ho'.2; change intOfZ _ < intOfZ _ at this
          simpa [intOfZ_zOfInt, intOfZ_add, show intOfZ (size_chunk .Mint8unsigned) = 1 from rfl]
            using this
        have := hkeep.perm _ _ _ _ (hperm (intOfZ o) (by omega) (by omega))
        rw [zOfInt_intOfZ] at this
        exact Mem.perm_implies _ _ _ _ _ _ this (.perm_F_any _)
      obtain ⟨m'', hst⟩ := Mem.valid_access_store _ _ _ _
        (.Vint (Lib.Integers.Int.zero_ext (zOfInt 8) (ir 0))) hva
      wp_step; wp_step
      apply wp_assign_eval
      simp only [Exec.evalLvalue, Exec.evalExpr, hp', hik, typeof, cop, Exec.assignLoc,
        Cfrontend.Ctypes.access_mode, Mem.storev]
      rw [addr_byte _ (by omega), hst]
      refine ⟨by simp, rfl, k, hks, rfl, hik, ?_, ?_, ho⟩
      · have hlo := Mem.loadbytes_store_other _ _ _ _ _ _ hst b (zOfInt 0) (zOfInt k)
          (.inr (.inr (.inl (by change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt]))))
        have hhi := Mem.loadbytes_store_same _ _ _ _ _ _ hst
        rw [encode_zero] at hhi
        have := Mem.loadbytes_concat _ _ _ _ _ _ _ (hlo.trans hbytes)
          (show Mem.loadbytes m'' b (ZArith.BinInt.Z.add (zOfInt 0) (zOfInt k))
            (size_chunk .Mint8unsigned) = _ by
              rw [show ZArith.BinInt.Z.add (zOfInt 0) (zOfInt k) = zOfInt k by
                apply intOfZ_injective; simp [intOfZ_zOfInt]]; exact hhi)
          (by change intOfZ _ ≤ intOfZ _; simp [intOfZ_zOfInt]) (by decide)
        rw [show zOfInt ((k : Int) + 1) =
            ZArith.BinInt.Z.add (zOfInt k) (size_chunk .Mint8unsigned) by
          apply intOfZ_injective
          simp [intOfZ_zOfInt, show intOfZ (size_chunk .Mint8unsigned) = 1 from rfl],
          List.replicate_succ']
        exact this
      · refine hkeep.trans ⟨Unch.store hst rfl, fun c o hco => ?_, fun _ _ _ _ h =>
          Mem.perm_store_1 _ _ _ _ _ _ hst _ _ _ _ h, fun _ h => Mem.store_valid_block_1 _ _ _ _ _ _ hst _ h⟩
        apply Mem.load_store_other _ _ _ _ _ _ hst
        right; left
        change intOfZ _ ≤ intOfZ _
        simp only [intOfZ_add, intOfZ_zOfInt]
        have : intOfZ (size_chunk c) = csize c := rfl
        omega
    · rw [ite_eq_right (by simpa using hks)]
      apply wp_break
      have hk' : k = sz := by omega
      subst hk'
      simpa using hQ le' m' hbytes hkeep ho
  · rintro v t e' le' m' ⟨rfl, rfl, k, hk, rfl, hik, hbytes, hkeep, ho⟩
    wp_step; wp_step
    apply wp_set_eval
    rw [Exec.evalExpr, show Exec.evalExpr ge e le' m' (.Etempvar Z.i tulong) = _ from hik]
    simp only [Exec.evalExpr, typeof, cop, add_lr_one]
    refine ⟨sz - (k + 1), by omega, by simp, rfl, k + 1, hk, rfl, temps_gss _ _ _, by
      simpa using hbytes, hkeep, fun k' hk' => by rw [temps_gso _ _ hk', ho _ hk']⟩

def zallocSpec (sz : Nat) : FunSpec where
  pre args _ := args = [.Vlong (lr sz)] ∧ sz < 2 ^ 62
  post _ m t v m' := t = E0 ∧ ∃ b, v = .Vptr b Ptrofs.zero ∧ Fresh m m' b sz ∧
    Mem.loadbytes m' b (zOfInt 0) (zOfInt sz) = some (List.replicate sz zb)

theorem zalloc_satisfies (sz : Nat) :
    Satisfies xi ge (.Internal dense.fn.nauty_zalloc) (zallocSpec sz) := by
  let le0 := PTree.set Z.sz (.Vlong (lr sz)) (create_undef_temps dense.fn.nauty_zalloc.fn_temps)
  refine satisfies_internal (Entry := fun _ m₀ e le m => e = empty_env ∧ le = le0 ∧ m = m₀) ?_ ?_
  · rintro args m ⟨rfl, -⟩
    refine ⟨empty_env, le0, m, ⟨?_, ?_, ?_, .nil _ _, rfl⟩, rfl, rfl, rfl⟩
    · exact .nil _
    · exact Nextelement.norepet_of_nodup (by decide)
    · exact Nextelement.disjoint_of (by decide)
  · rintro args m₀ ⟨rfl, hsz⟩
    rw [triple_iff_wp]
    rintro e le m ⟨rfl, rfl, rfl⟩
    rw [dense.fn.nauty_zalloc.fn_body_eq, Z.body_eq]
    wp_step; wp_step; wp_step; wp_step
    refine wp_call _ (mallocSpec sz) (malloc_satisfies sz) rfl
      (by simp [Exec.evalExpr, Exec.lvalOfVar, empty_env, find_malloc, Exec.derefLoc,
        Cfrontend.Ctypes.access_mode]; rfl)
      (by simp (config := {decide := true}) [Exec.evalExprlist, Exec.evalExpr, le0, typeof, cop])
      (by simp [Common.Globalenvs.Genv.find_funct, funct_malloc]) rfl ⟨rfl, by omega⟩ ?_
    rintro t v m1 ⟨rfl, b, rfl, hfr⟩
    simp only [set_opttemp, E0_append]
    apply wp_set_eval
    simp only [Exec.evalExpr, temps_gss]
    let le2 := PTree.set Z.p (.Vptr b Ptrofs.zero) (PTree.set Z.t (.Vptr b Ptrofs.zero) le0)
    have hwv : Mem.weak_valid_pointer m1 b (Ptrofs.unsigned Ptrofs.zero) = true := by
      have h := hfr.perm (-1) (by decide) (by omega)
      have hv := (Mem.valid_pointer_nonempty_perm m1 b _).2
        (Mem.perm_implies _ _ _ _ _ _ h (.perm_any_N _))
      unfold Mem.weak_valid_pointer
      show (Mem.valid_pointer m1 b _ || Mem.valid_pointer m1 b (zOfInt (-1))) = true
      rw [hv, Bool.or_true]
    wp_step; wp_step; wp_step
    apply wp_if_eval
    simp only [Exec.evalExpr, temps_gss, typeof, cop, hwv, ite_true]
    refine wp_fill (b := b) (sz := sz) hsz (temps_gss _ _ _)
      (by simp (config := {decide := true}) only [temps_gso, le0, temps_gss])
      (fun ofs h1 h2 => hfr.perm ofs (by omega) h2) ?_
    intro le' m' hbytes hkeep ho
    have hp' : PTree.get Z.p le' = some (.Vptr b Ptrofs.zero) := by
      rw [ho _ (by decide)]; exact temps_gss _ _ _
    wp_step; wp_step
    apply wp_return_some_eval
    simp only [Exec.evalExpr, hp', typeof, cop, dense.fn.nauty_zalloc.fn_return_eq,
      Nextelement.free_empty]
    refine ⟨rfl, b, rfl, ⟨hfr.unch.trans hkeep.unch, ?_, fun o h1 h2 => hkeep.perm _ _ _ _ (hfr.perm o h1 h2),
      hfr.new, fun z hz => hkeep.grow _ (hfr.grow _ hz)⟩, hbytes⟩
    rw [hkeep.low _ (-8) (by decide)]
    exact hfr.hdr

end NautyVerified.Proofs.Alloc

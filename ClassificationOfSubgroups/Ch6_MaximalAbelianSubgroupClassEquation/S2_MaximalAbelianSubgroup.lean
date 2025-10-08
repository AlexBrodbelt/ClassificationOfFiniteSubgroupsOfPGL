import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S4_PropertiesOfCentralizers
import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S5_PropertiesOfNormalizers
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S1_ElementaryAbelian
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Sylow

set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option linter.unusedTactic false

open Subgroup

def IsMaximalAbelian {L : Type*} [Group L] (G : Subgroup L) : Prop := Maximal IsCommutative G

def MaximalAbelianSubgroupsOf { L : Type*} [Group L] (G : Subgroup L) : Set (Subgroup L) :=
  { K : Subgroup L | IsMaximalAbelian (K.subgroupOf G) ∧ K ≤ G}

structure MaximalAbelian {G : Type*} [Group G] (H : Subgroup G) extends Subgroup G where
  is_maximal' : Maximal (IsCommutative) H

def MaximalAbelianSubgroups' {L : Type*} [Group L] (G : Subgroup L) :=
  { K : Subgroup L // IsMaximalAbelian (K.subgroupOf G) ∧ K ≤ G }

open SpecialSubgroups

lemma mem_centralizer_self {G : Type*} [Group G] (x : G) : x ∈ centralizer {x} := by
  rintro y ⟨rfl⟩; rfl

section IsCommutative

lemma inf_IsCommutative_of_IsCommutative_left {G : Type*} [ Group G] (H K : Subgroup G)
  (hH : IsCommutative H) : IsCommutative (H ⊓ K) := by
  rw [IsCommutative_iff]
  intro x y
  have H_meet_K_le_H : H ⊓ K ≤ H := inf_le_left
  have x_in_H : (x : G) ∈ H := H_meet_K_le_H <| SetLike.coe_mem _
  have y_in_H : (y : G) ∈ H := H_meet_K_le_H <| SetLike.coe_mem _
  have := @mul_comm_of_mem_isCommutative G _ H hH x y x_in_H y_in_H
  exact SetLike.coe_eq_coe.mp this

lemma IsCommutative_of_IsCommutative_subgroupOf {G : Type*} [ Group G ] (H K : Subgroup G)
  (hH : IsCommutative (H.subgroupOf K)) : IsCommutative (H ⊓ K) := by
  rw [IsCommutative_iff] at hH ⊢
  intro x y
  have x_in_K : (x : G) ∈ K := x.property.right
  have y_in_K : (y : G) ∈ K := y.property.right
  have x_in_H_subgroupOf_K : ⟨x, x_in_K⟩ ∈ (H.subgroupOf K) := by
    simp [mem_subgroupOf]
    exact x.property.left
  have y_in_H_subgroupOf_K : ⟨y, y_in_K⟩ ∈ (H.subgroupOf K) := by
    simp [mem_subgroupOf]
    exact y.property.left
  specialize hH ⟨⟨x, x_in_K⟩, x_in_H_subgroupOf_K⟩ ⟨⟨y, y_in_K⟩, y_in_H_subgroupOf_K⟩
  simp [SetLike.coe_eq_coe] at hH
  exact SetLike.coe_eq_coe.mp hH

open Pointwise

def center_mul  {G : Type* } [Group G] (H : Subgroup G) : Subgroup G where
  carrier := (center G : Set G) * (H : Set G)
  mul_mem' := by
    intro x y ⟨z₁, hz₁, a₁, ha₁, h₁⟩ ⟨z₂, hz₂, a₂, ha₂, h₂⟩
    simp at h₁ h₂
    rw [← h₁, ← h₂, mul_assoc, ← mul_assoc a₁, Eq.symm (hz₂.comm a₁)]
    use z₁ * z₂
    split_ands
    · exact mul_mem hz₁ hz₂
    use a₁ * a₂
    split_ands
    · exact mul_mem ha₁ ha₂
    group
  one_mem' := by
    use 1
    split_ands
    · exact one_mem (center G)
    use 1
    split_ands
    · apply one_mem
    simp_rw [mul_one]
  inv_mem' := by
    intro x ⟨z, hz, a, ha, h⟩
    simp [Set.mem_mul]
    use z⁻¹
    split_ands
    · exact (Subgroup.inv_mem_iff (center G)).mpr hz
    use a⁻¹
    split_ands
    · exact (Subgroup.inv_mem_iff H).mpr ha
    simp at h
    rw [eq_inv_iff_mul_eq_one, ← h, mul_assoc, ← mul_assoc a⁻¹, Eq.symm (hz.comm a⁻¹)]
    group

lemma IsComm_of_center_join_IsComm {G : Type* } [Group G] (H : Subgroup G)
  (hH : IsCommutative H) : IsCommutative (center G ⊔ H) :=  by
  rw [IsCommutative_iff]
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  have center_mul_subset_center_mul :
    ((center G) :  Set G) * H ⊆ (center_mul H) := by simp [center_mul]
  rw [@sup_eq_closure_mul, mem_closure] at hx hy
  specialize hx (center_mul H) center_mul_subset_center_mul
  specialize hy (center_mul H) center_mul_subset_center_mul
  rcases hx with ⟨z₁, hz₁, h₁, hh₁, h₁'⟩
  rcases hy with ⟨z₂, hz₂, h₂, hh₂, h₂'⟩
  simp at hz₁ hz₂ h₁' h₂' ⊢
  rw [← h₁', ← h₂', mul_assoc, ← mul_assoc h₁, (hz₂.comm h₁).symm,
   mul_assoc z₂, mul_assoc z₂, ← mul_assoc h₂, (hz₁.comm h₂).symm,
   mul_comm_of_mem_isCommutative H hh₁ hh₂, ← mul_assoc,
   Eq.symm (hz₂.comm z₁)]
  group

end IsCommutative

lemma ne_union_left_of_ne {X : Type*} (A B : Set X)(not_B_le_A : ¬ B ≤ A) : A ⊂ A ∪ B := by
  rw [Set.ssubset_def]
  split_ands
  exact Set.subset_union_left
  intro h
  rw [Set.union_subset_iff] at h
  simp_rw [subset_refl, true_and] at h
  contradiction

open MulAction Pointwise

theorem Units.coeHom_injective {M : Type*} [Monoid M] : Function.Injective (Units.coeHom M) := by
  intro x y h
  rw [Units.coeHom_apply, Units.coeHom_apply, ← Units.ext_iff] at h
  exact h

open Function Units

lemma order_ne_char (F : Type*) [Field F] (p : ℕ) [hp' : Fact (Nat.Prime p)] [hC : CharP F p] :
  ∀ x : Fˣ, orderOf x ≠ p := by
  intro x
  by_contra H
  have := ExpChar.pow_prime_pow_mul_eq_one_iff p 1 1 (x : F)
  simp only [← H, pow_one, mul_one, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one x, Units.val_one,
    Units.val_eq_one, true_iff] at this
  exact hp'.out.ne_one (@orderOf_one Fˣ _ ▸ (this ▸ H)).symm

lemma dvd_pow_totient_sub_one_of_coprime {m p : ℕ} (hp : Nat.Prime p) (h : Nat.Coprime m p) :
  m ∣ p^Nat.totient m - 1 := by
  rw [← Nat.modEq_zero_iff_dvd]
  suffices p ^ m.totient ≡ 1 [MOD m] by
    rw [← add_zero (p ^ Nat.totient m), ← Nat.sub_self 1] at this
    nth_rewrite 3 [← zero_add 1] at this
    rw [← Nat.add_sub_assoc (le_refl _), Nat.sub_add_comm (one_le_pow₀ hp.one_le)] at this
    apply Nat.ModEq.add_right_cancel' 1 this
  exact Nat.ModEq.pow_totient h.symm

-- Alex's original approach inspired by a maths stack exchange was
-- the elements of the finite subgroup of the
-- finite subgroup of units of a field has order dividing p ^ k - 1 for some k ∈ ℕ
-- We show that a finite subgroup is contained in a finite field which is a subfield of
-- a possibly non-finite field. First, we take the minimal subfield 𝔽ₚ and adjoin all elements of G.
-- this extension is algebraic as every element is a solution to x^|G| - 1,
-- so the extension is algebraic, hence the field extension 𝔽ₚ(g₁, g₂, …, gₙ) is finite.
-- G ≤ 𝔽ₚ(g₁, g₂, …, gₙ)
-- Here formalized the argument by Mitchell

lemma coprime_card_fin_subgroup_of_monomorphism {F G : Type*} [Field F] {p : ℕ}
  [hp' : Fact (Nat.Prime p)] [hC : CharP F p] [Group G] (H : Subgroup G) [Finite H]
  (f : H →* Fˣ) (hf : Injective f) :
  Nat.Coprime (Nat.card H) p := by
  -- A prime number `p` is coprime to a natural number `n`
  -- if and only if `¬ p ∣ n`.
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp'.out]
  -- The order of an element `x` in the group of units of a field
  -- cannot equal the characteristic of the field `F`.
  have order_ne_p : ∀ (x : Fˣ), orderOf x ≠ p := order_ne_char F p
  -- We contrapose the statement with the assumption:
  -- `∀ x : Fˣ, orderOf x ≠ p`
  -- and the claim:
  -- `¬ p ∣ Nat.card ↥H`
  contrapose! order_ne_p
  -- `order_ne_p` now contains the assumption which states:
  -- `p ∣ Nat.card ↥H`,
  -- and the goal is to now to prove the statement:
  -- `∃ x : Fˣ, orderOf x = p`.
  let H_fintype : Fintype H := Fintype.ofFinite ↥H
  simp only [Nat.card_eq_fintype_card] at order_ne_p
  -- Since `p ∣ Nat.card ↥H`, by Cauchy's Theorem there must exist an
  -- an element `h` of the subgroup `H` which has order `p`.
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card p order_ne_p
  -- The image of `h` under the monomorphism `f : H → Fˣ` is the desired witness.
  use f h
  rw [orderOf_injective f hf h, ← hh]

instance SZ_Comm {F : Type*} [Field F] : CommGroup (S F ⊔ Z F :) := by
  rw [S_join_Z_eq_SZ]
  let inst := IsCommutative_SZ F
  exact IsCommutative.commGroup (SZ F)

namespace MaximalAbelianSubgroup



lemma not_le_of_ne {G : Type*} [Group G] (A B H : Subgroup G)
  (hA : A ∈ MaximalAbelianSubgroupsOf H) (hB : B ∈ MaximalAbelianSubgroupsOf H) (A_ne_B : A ≠ B):
  ¬ B ≤ A  := by
  intro h
  obtain ⟨⟨hA, -⟩, A_le_H⟩ := hA
  obtain ⟨⟨-, B_maximal⟩, B_le_H⟩ := hB
  have : B.subgroupOf H ≤ A.subgroupOf H := by
    rw [← map_subtype_le_map_subtype]
    simp
    exact inf_le_of_left_le h
  specialize B_maximal hA this
  have contr : A.subgroupOf H = B.subgroupOf H := by
    rw [← sup_le_inf]
    apply le_trans (b := A.subgroupOf H)
    apply sup_le (le_refl _) this
    apply le_inf (le_refl _) B_maximal
  simp at contr
  have A_meet_G_eq_A : A ⊓ H = A := inf_of_le_left A_le_H
  have B_meet_G_eq_B : B ⊓ H = B := inf_of_le_left B_le_H
  rw [A_meet_G_eq_A, B_meet_G_eq_B] at contr
  contradiction


lemma le_centralizer_of_mem {G : Type*} [Group G] {A H : Subgroup G}
  (hA : A ∈ MaximalAbelianSubgroupsOf H) {x : G} (x_in_A : x ∈ A) : A ≤ centralizer {x} := by
  intro a a_in_A
  obtain ⟨⟨A_IsCommutative', -⟩, A_le_G⟩ := hA
  have hA : IsCommutative (A ⊓ H) := IsCommutative_of_IsCommutative_subgroupOf A H A_IsCommutative'
  have A_meet_G_eq_A : A ⊓ H = A := inf_of_le_left A_le_G
  have := @mul_comm_of_mem_isCommutative G _ A (A_meet_G_eq_A ▸ hA) x a x_in_A a_in_A
  simp [mem_centralizer_iff]
  exact this

theorem le_centralizer_meet {G : Type*} [Group G] (A H : Subgroup G)
  (hA : A ∈ MaximalAbelianSubgroupsOf H) (x : G) (x_in_A : x ∈ A) :
  A ≤ centralizer {x} ⊓ H := by
  apply le_inf
  exact le_centralizer_of_mem hA x_in_A
  apply hA.right


lemma lt_centralizer_meet_G {G : Type*} [Group G] {A B H : Subgroup G}
  (hA : A ∈ MaximalAbelianSubgroupsOf H)  (hB : B ∈ MaximalAbelianSubgroupsOf H)
  (A_ne_B: A ≠ B) {x : G} (x_in_A : x ∈ A) (x_in_B : x ∈ B):
  A < centralizer {x} ⊓ H := by
  suffices (A : Set G) < centralizer {x} ⊓ H by exact this
  apply lt_of_lt_of_le (b := (A : Set G) ∪ B)
  · have not_B_le_A : ¬ B ≤ A := not_le_of_ne A B H hA hB A_ne_B
    rw [Set.lt_iff_ssubset, Set.ssubset_iff_subset_ne]
    split_ands
    · exact Set.subset_union_left
    · symm
      apply ne_of_not_le
      intro h
      simp at h
      contradiction
  · simp only [coe_inf, Set.le_eq_subset, Set.subset_inter_iff, Set.union_subset_iff,
    SetLike.coe_subset_coe]
    split_ands
    · exact le_centralizer_of_mem hA x_in_A
    · exact le_centralizer_of_mem hB x_in_B
    · exact hA.right
    · exact hB.right

lemma center_le {G : Type*} [Group G] (H A : Subgroup G) (hA : A ∈ MaximalAbelianSubgroupsOf H)
  (hH : center G ≤ H) : center G ≤ A := by
  by_contra h
  rw [SetLike.not_le_iff_exists] at h
  -- We will yield that K is less than or equal to A
  have contr := hA.left.right
  let K := (center G ⊔ A).subgroupOf H
  have A_IsComm : IsCommutative A :=
    inf_of_le_left hA.right ▸ IsCommutative_of_IsCommutative_subgroupOf A H hA.left.left
  have A_join_cen_IsComm : IsCommutative (center G ⊔ A) := IsComm_of_center_join_IsComm _ A_IsComm
  have K_IsComm : IsCommutative K := subgroupOf_isCommutative H (center G ⊔ A)
  have A_le_cen_join_A : A.subgroupOf H ≤ (center G ⊔ A).subgroupOf H := by
    simp [← map_subtype_le_map_subtype, hA.right]

  specialize contr K_IsComm A_le_cen_join_A
  obtain ⟨z, hz, z_not_in_A⟩ := h
  have z_in_H : z ∈ H := by apply hH hz
  have : ¬ K ≤ A.subgroupOf H := by
    simp only [SetLike.not_le_iff_exists, Subtype.exists, K]
    use z, z_in_H
    split_ands
    · simp only [mem_subgroupOf]; exact mem_sup_left hz
    · simp only [mem_subgroupOf]; exact z_not_in_A
  contradiction


lemma singleton_of_center_eq_G {G : Type*} [Group G] (H : Subgroup G) (hH : H = center G) :
  MaximalAbelianSubgroupsOf H = {center G} := by
  ext A
  have cen_le_G : center G ≤ H := le_of_eq hH.symm
  constructor
  · intro hA
    have center_le_A := center_le H A hA cen_le_G
    have A_le_center := hH ▸ hA.right
    -- A = center G
    simp [le_antisymm A_le_center center_le_A]
  · rintro ⟨rfl⟩
    simp [MaximalAbelianSubgroupsOf, IsMaximalAbelian]
    split_ands
    · exact subgroupOf_isCommutative H (center G)
    · intro A _A_IsComm _cen_le_A
      simp_rw [← hH]
      simp only [subgroupOf_self, le_top]
    exact cen_le_G

open scoped MatrixGroups

#check card_Z_eq_two_of_two_ne_zero

#check card_Z_eq_one_of_two_eq_zero

#check Set.subset_iff_eq_of_ncard_le
-- Argue for when cardinality of A equals two


-- Argue for when cardinality of A is less than equal to one
lemma SpecialLinearGroup.sq_eq_one_iff {F : Type*} [Field F] [two_ne_zero : NeZero (2 : F)]
  {x : SL(2,F)} (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [sq, _root_.mul_eq_one_iff_eq_inv, SpecialLinearGroup.fin_two_ext_iff,
    @Matrix.SpecialLinearGroup.SL2_inv_expl] at hx
  simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const] at hx
  obtain ⟨x00_eq_x11, x01_eq_zero, x10_eq_zero, -⟩ := hx
  have det_eq_one : Matrix.det x.val = (1 : F) := by
    exact Matrix.SpecialLinearGroup.det_coe x
  rw [Matrix.det_fin_two] at det_eq_one
  have h := two_ne_zero.out
  rw [← add_eq_zero_iff_eq_neg, ← two_mul,
    mul_eq_zero_iff_left h] at x01_eq_zero x10_eq_zero
  simp only [Fin.isValue, x00_eq_x11, x01_eq_zero, x10_eq_zero, mul_zero, sub_zero] at det_eq_one
  rw [← sq, _root_.sq_eq_one_iff] at det_eq_one
  rcases det_eq_one with (x11_eq_one | x11_eq_neg_one)
  · left
    ext <;> simp [x11_eq_one, x00_eq_x11, x01_eq_zero, x10_eq_zero]
  · right
    ext <;> simp [x11_eq_neg_one, x00_eq_x11, x01_eq_zero, x10_eq_zero]

lemma NeZero_two_of_char_ne_two (F : Type*) [Field F] {p : ℕ} [hp' : Fact (Nat.Prime p)]
  [hC : CharP F p] (p_ne_two : p ≠ 2) : NeZero (2 : F) := by
  refine { out := ?_ }
  intro two_eq_zero
  have one_ne_zero : (1 : F) ≠ 0 := one_ne_zero
  let char_eq_two : CharP F 2 := by
    exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero two_eq_zero
  have two_dvd_p : (p : F) = 0 := by exact CharP.cast_eq_zero F p
  rw [char_eq_two.cast_eq_zero_iff'] at two_dvd_p
  have two_eq_p : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp'.out).mp two_dvd_p).symm
  contradiction
-- There is a gap in the informal proof for when p = 2
/-
A counterexample is {1, !![1,1;1,0]} is a finite subgroup of $G := { !![a,b;c,d] | a,b,c,d \in 𝔽₂}$
-- where 𝔽₂ ↪ F when F is of characteristic 2.
-/
lemma eq_center_of_card_le_two {p : ℕ} [Fact (Nat.Prime p)] {F : Type*} [Field F]
  [CharP F p] (p_ne_two : p ≠ 2) (A G : Subgroup SL(2,F)) [hG : Finite G]
  (center_le_G : center (SL(2,F)) ≤ G) (hA : A ∈ MaximalAbelianSubgroupsOf G)
  (card_A_le_two : Nat.card A ≤ 2) :
  A = center SL(2,F) := by
  let inst : Finite (Z F) := by infer_instance
  let inst : Finite (Z F).carrier := by exact inst
  refine le_antisymm ?A_le_Z ?Z_le_A
  case A_le_Z =>
    intro a a_mem_A
    let A_finite : Finite (A : Set SL(2,F)) := Finite.Set.subset G hA.right
    have orderOf_a_le_two : orderOf a ≤ 2 := calc
      orderOf a ≤ Nat.card A := Subgroup.orderOf_le_card A A_finite a_mem_A
      _ ≤ 2 := card_A_le_two
    rw [@Nat.le_succ_iff_eq_or_le] at orderOf_a_le_two
    rcases orderOf_a_le_two with ( orderOf_a_eq_two | orderOf_a_le_one)
    · simp at orderOf_a_eq_two
      rw [orderOf_eq_iff (by norm_num)] at orderOf_a_eq_two
      obtain ⟨a_sq_eq_one, -⟩ := orderOf_a_eq_two
      simp [center_SL2_eq_Z]
      let NeZero_two : NeZero (2 : F) := NeZero_two_of_char_ne_two F p_ne_two
      exact SpecialLinearGroup.sq_eq_one_iff a_sq_eq_one
    -- We show $a$ is of finite order and thus the order is greater than one
    · have a_IsOfFinOrder : IsOfFinOrder a := by
        obtain ⟨n, n_pos, hn⟩ := isOfFinOrder_of_finite (⟨a, a_mem_A⟩ : A)
        use n
        split_ands
        · exact n_pos
        · rw [isPeriodicPt_mul_iff_pow_eq_one] at hn ⊢
          simp only [SubmonoidClass.mk_pow, Subtype.ext_val_iff, OneMemClass.coe_one] at hn
          exact hn
      rw [← orderOf_pos_iff, pos_iff_ne_zero] at a_IsOfFinOrder
      rw [Nat.le_one_iff_eq_zero_or_eq_one] at orderOf_a_le_one
      apply Or.resolve_left at orderOf_a_le_one
      specialize orderOf_a_le_one a_IsOfFinOrder
      rw [@orderOf_eq_one_iff] at orderOf_a_le_one
      rw [orderOf_a_le_one]
      exact Subgroup.one_mem (center SL(2, F))
  case Z_le_A =>
    exact center_le G A hA center_le_G

  -- if there exists an element not equal to the identity, then
  -- and -1 = 1 then the order of the group is not equal to 2.
  -- if x^2  = 1 then since $F$ is a field either x = 1 or x = -1.




/- Theorem 2.3 (i) If x ∈ G\Z then we have CG (x) ∈ M. -/
theorem centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral {F : Type*} [Field F]
  [IsAlgClosed F] [DecidableEq F] (G : Subgroup SL(2,F)) (x : SL(2,F))
  (hx : x ∈ (G.carrier \ (center SL(2,F)))) :
  centralizer {x} ⊓ G ∈ MaximalAbelianSubgroupsOf G := by
  obtain ⟨x_in_G, x_not_in_Z⟩ := hx
  simp at x_not_in_Z
  have IsCommutative_centralizer_S := IsCommutative_centralizer_of_not_mem_center x x_not_in_Z
  dsimp [MaximalAbelianSubgroupsOf]
  split_ands
  · rw [inf_subgroupOf_right]
    apply subgroupOf_isCommutative
  · rintro J hJ hx j j_in_J
    rw [inf_subgroupOf_right, mem_subgroupOf, mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    have x_in_J : ⟨x, x_in_G⟩ ∈ J := by
      apply hx
      apply mem_subgroupOf.mpr
      simp
      split_ands
      · exact mem_centralizer_self x
      · exact x_in_G
    have := mul_comm_of_mem_isCommutative J x_in_J j_in_J
    exact SetLike.coe_eq_coe.mpr this
  exact inf_le_right




/- Theorem 2.3 (ii) For any two distinct subgroups A and B of M, we have A ∩ B = Z. -/
theorem center_eq_meet_of_ne_MaximalAbelianSubgroups {F : Type*} [Field F] [IsAlgClosed F]
  [DecidableEq F] (A B G : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroupsOf G)
  (hB : B ∈ MaximalAbelianSubgroupsOf G) (A_ne_B: A ≠ B)(center_le_G : center SL(2,F) ≤ G) :
  A ⊓ B = center SL(2,F) := by
  ext x
  constructor
  · rintro ⟨x_in_A, x_in_B⟩
    simp at x_in_A x_in_B
    by_cases hx : x ∈ G.carrier \ (center SL(2,F))
    · have cen_meet_G_in_MaximalAbelianSubgroups :=
        centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral G x hx
      obtain ⟨⟨cen_meet_G_IsCommutative, _h⟩, -⟩ :=
        cen_meet_G_in_MaximalAbelianSubgroups
      simp only [inf_subgroupOf_right] at cen_meet_G_IsCommutative
      have cen_meet_G_le_A : centralizer {x} ⊓ G ≤ A := by
        suffices (centralizer {x}).subgroupOf G ≤ A.subgroupOf G by
          simp only [← map_subtype_le_map_subtype, subgroupOf_map_subtype, le_inf_iff, inf_le_right,
            and_true] at this
          exact this
        -- apply maximality of A
        apply hA.left.right
        exact cen_meet_G_IsCommutative
        simp only [← map_subtype_le_map_subtype, subgroupOf_map_subtype, le_inf_iff, inf_le_right,
          and_true]
        rw [inf_of_le_left hA.right]
        exact le_centralizer_of_mem hA x_in_A
        -- obtain a contradiction
      have not_cen_meet_G_le_A :=
        not_le_of_lt <| lt_centralizer_meet_G hA hB A_ne_B x_in_A x_in_B
      contradiction
    · simp at hx
      specialize hx (hA.right x_in_A)
      exact hx
  · intro hx
    have cen_le_A := center_le G A hA center_le_G
    have cen_le_B := center_le G B hB center_le_G
    exact le_inf cen_le_A cen_le_B hx

-- lemma NeZero_neg_CharP [CharP F p] : ∀ (x : F), NeZero x ↔ p • (1 : F) ≠ x := by



/- Theorem 2.3 (iii) An element A of M is either a cyclic group whose order is relatively prime
to p, or of the form Q × Z where Q is an elementary abelian Sylow p-subgroup
of G. -/
theorem IsCyclic_and_card_Coprime_CharP_of_center_eq {F : Type*} [Field F] {p : ℕ}
  (hp : Nat.Prime p) [C : CharP F p] (A G : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroupsOf G)
  (hG : G = center SL(2,F)) : IsCyclic A ∧ Nat.Coprime (Nat.card A) p := by
  rw [singleton_of_center_eq_G G hG] at hA
  simp at hA
  rw [center_SL2_eq_Z] at hA
  rw [hA]
  split_ands
  · exact IsCyclic_Z
  · by_cases h : p ≠ 2
    · have two_ne_zero : (2 : F) ≠ 0 := by
        intro h'
        have : ((2 : ℕ ) : F) = (2 : F) := by rfl
        rw [← this, CharP.cast_eq_zero_iff F p 2,
         Nat.prime_dvd_prime_iff_eq hp Nat.prime_two] at h'
        contradiction
      have NeZero_two : NeZero (2 : F) := { out := two_ne_zero }
      rw [card_Z_eq_two_of_two_ne_zero, Nat.coprime_two_left]
      exact Nat.Prime.odd_of_ne_two hp h
    · simp at h
      let C' : CharP F 2 := by exact CharP.congr p h
      have two_eq_zero : (2 : F) = 0 := CharTwo.two_eq_zero
      rw [card_Z_eq_one_of_two_eq_zero two_eq_zero]
      exact Nat.gcd_one_left p

open IsElementaryAbelian

lemma center_not_mem_of_center_ne {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  {G : Subgroup SL(2,F)} (hG : center SL(2,F) ≠ G) :
  center SL(2,F) ∉ MaximalAbelianSubgroupsOf G := by
  intro h
  by_cases h' : center SL(2,F) ≤ G
  · obtain ⟨x, x_in_G, x_not_in_cen⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h' hG)
    have centra_ne_cen : centralizer {x} ⊓ G ≠ center SL(2,F) := by
      apply ne_of_gt
      rw [SetLike.lt_iff_le_and_exists]
      split_ands
      · exact le_inf (Subgroup.center_le_centralizer ({x} : Set SL(2,F))) h'
      · exact ⟨x, ⟨mem_centralizer_self x, x_in_G⟩, x_not_in_cen⟩
    have centra_mem_MaxAbSub :=
      centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral
        G x (Set.mem_diff_of_mem x_in_G x_not_in_cen)
    have cen_le_centra : center SL(2, F) ≤ centralizer {x} ⊓ G :=
      le_inf (center_le_centralizer {x}) h'
    have cen_le_centra' : (center SL(2, F)).subgroupOf G ≤ (centralizer {x} ⊓ G).subgroupOf G := by
      simp [← map_subtype_le_map_subtype]; rw [inf_of_le_left h']; exact center_le_centralizer {x}
    have centra_le_cen := h.left.right centra_mem_MaxAbSub.left.left cen_le_centra'
    simp [← map_subtype_le_map_subtype] at centra_le_cen
    absurd centra_ne_cen (le_antisymm centra_le_cen cen_le_centra)
    trivial
  · absurd h' h.right
    trivial

open SpecialSubgroups SpecialMatrices

lemma eq_centralizer_meet_of_center_lt {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (A G : Subgroup SL(2,F)) (center_lt : center SL(2,F) < A) (hA : A ∈ MaximalAbelianSubgroupsOf G) :
  ∃ x : SL(2,F), x ∈ G.carrier \ center SL(2,F) ∧ A = centralizer {x} ⊓ G := by
  rw [SetLike.lt_iff_le_and_exists] at center_lt
  obtain ⟨-, x, x_in_A, x_not_in_center⟩ := center_lt
  have hx : x ∈ G.carrier \ center SL(2,F) := Set.mem_diff_of_mem (hA.right x_in_A) x_not_in_center
  obtain ⟨⟨centra_meet_G_IsComm, -⟩, -⟩ :=
    centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral G x hx
  -- We show centralizer {x} ⊓ G ≤ A
  have A_le_centralizer_meet_G := (le_centralizer_meet A G hA x x_in_A)
  have A_le_centralizer_meet_G' : A.subgroupOf G ≤ (centralizer {x} ⊓ G).subgroupOf G := by
    simp [← map_subtype_le_map_subtype]
    exact le_trans inf_le_left <| le_trans A_le_centralizer_meet_G inf_le_left
  -- by using the maximality of A and using the fact A ≤ centralizer {x} ⊓ G
  have centralizer_meet_G_le_A := hA.left.right centra_meet_G_IsComm A_le_centralizer_meet_G'
  simp [← map_subtype_le_map_subtype] at centralizer_meet_G_le_A
  -- We show A = centralizer {x} ⊓ G
  exact ⟨x, hx, le_antisymm A_le_centralizer_meet_G centralizer_meet_G_le_A⟩





open MulAut

lemma conj_ZS_eq_conj_Z_join_S {F : Type*} [Field F] (c : SL(2,F)):
  conj c • SZ F = conj c • S F ⊔ Z F := by
  rw [← SZ_eq_SZ']
  ext x
  constructor
  · rintro ⟨t, ⟨⟨t, ht, z, hz, rfl⟩, rfl⟩⟩
    simp at ht ⊢
    simp [← center_SL2_eq_Z] at hz ⊢
    rw [mul_assoc c, mul_assoc t, ← mem_center_iff.mp hz c⁻¹]
    rw [← SetLike.mem_coe, mul_normal]
    use c * t * c⁻¹
    constructor
    · simp [pointwise_smul_def, ht]
    use z
    constructor
    · exact hz
    group
  · rw [← SetLike.mem_coe, ← center_SL2_eq_Z, mul_normal]
    rintro ⟨y, hy, z, hz, rfl⟩
    simp [pointwise_smul_def] at hy ⊢
    obtain ⟨t, ht, rfl⟩ := hy
    use t * z
    constructor
    · simp only [SZ', mem_mk]
      use t
      constructor
      · exact ht
      use z
      constructor
      · exact center_SL2_eq_Z F ▸ hz
      rfl
    rw [mul_assoc c, mul_assoc t, ← mem_center_iff.mp hz c⁻¹]
    group


lemma Z_eq_Z_meet_G (F : Type*) [Field F] (G : Subgroup SL(2,F))
  (center_le_G : center SL(2,F) ≤ G) :
  Z F = Z F ⊓ G := ((center_SL2_eq_Z F).symm) ▸ left_eq_inf.mpr center_le_G

lemma conj_S_join_Z_meet_G_eq_conj_S_meet_G_join_Z {F : Type*} [Field F]{G : Subgroup SL(2,F)}
  (center_le_G : center SL(2,F) ≤ G) (c : SL(2,F)) :
  (conj c • (S F ⊔ Z F)) ⊓ G = conj c • S F ⊓ G ⊔ Z F :=
  calc
  (conj c • (S F ⊔ Z F)) ⊓ G = (conj c • S F ⊔ Z F) ⊓ G := by
    simp [smul_sup, ← center_SL2_eq_Z, smul_normal c]
  _ = (conj c • S F ⊓ G) ⊔ (Z F ⊓ G) := by
        ext y
        rw [← SetLike.mem_coe, ← Z_eq_Z_meet_G F G center_le_G, ← center_SL2_eq_Z,
          Subgroup.coe_inf, Subgroup.mul_normal (N := center SL(2,F)), ← SetLike.mem_coe,
          Subgroup.mul_normal (N := center SL(2,F)), Subgroup.coe_inf]
        constructor
        · rintro ⟨⟨s, s_in_S, z, hz, rfl⟩, y_in_G⟩
          simp at y_in_G ⊢
          use s
          split_ands
          · exact s_in_S
          · rw [← mul_one s, ← mul_inv_cancel z, ← mul_assoc]
            exact Subgroup.mul_mem G y_in_G <| inv_mem (center_le_G hz)
          use z
        · rintro ⟨s, ⟨s_in_S, s_in_G⟩, z, z_in_Z, rfl⟩
          simp
          split_ands
          · use s
            split_ands
            exact s_in_S
            use z
          exact Subgroup.mul_mem G s_in_G <| center_le_G z_in_Z
  _ = (conj c • S F ⊓ G) ⊔ Z F := by rw [← Z_eq_Z_meet_G F G center_le_G]

lemma conj_inv_conj_eq (F : Type*) [Field F](G : Subgroup SL(2,F)) (c : SL(2,F)):
  conj c⁻¹ • ((conj c • S F ⊓ G) ⊔ Z F) = (S F ⊓ conj c⁻¹ • G) ⊔ Z F := by
  simp only [smul_inf, ← center_SL2_eq_Z, smul_normal c⁻¹, smul_sup]
  simp [map_inv, inv_smul_smul]

lemma coprime_card_fin_subgroup_of_inj_hom_group_iso_units {F G : Type*} [Field F] {p : ℕ}
    [hp' : Fact (Nat.Prime p)] [hC : CharP F p] [Group G] (H : Subgroup G) [Finite H]
    (f : H →* Fˣ) (hf : Injective f) :
    Nat.Coprime (Nat.card H) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp'.out]
    have order_ne_p := @order_ne_char F _ p _ _
    contrapose! order_ne_p
    let H_fintype : Fintype H := Fintype.ofFinite ↥H
    simp only [Nat.card_eq_fintype_card] at order_ne_p
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card p order_ne_p
    use f h
    rw [orderOf_injective f hf ↑h, ← hh]

theorem IsConj_fin_subgroup_D_and_card_coprime_CharP_and_IsCyclic_of_IsConj_d {F : Type*} [Field F]
  [IsAlgClosed F] [DecidableEq F] (p : ℕ) [hp' : Fact (Nat.Prime p)] [hC : CharP F p]
  (G : Subgroup SL(2,F)) [hG₀ : Finite G] (A : Subgroup SL(2,F)) (x : SL(2,F))
  (x_not_in_center : x ∉ center SL(2,F)) (A_eq_centra : A = centralizer {x} ⊓ G )
  (δ : Fˣ) (x_IsConj_d : IsConj (d δ) x) :
  (∃ (c : SL(2,F)) (D₀ : Subgroup SL(2,F)),
  Finite D₀ ∧ D₀ ≤ D F ∧ A = conj c • D₀) ∧ (Nat.Coprime (Nat.card A) p ∧ IsCyclic A)
   := by
  simp [center_SL2_eq_Z] at x_not_in_center
  have δ_ne_one : δ ≠ 1 := by rintro rfl; simp_all
  have δ_ne_neg_one : δ ≠ -1 := by rintro rfl; simp_all
  obtain ⟨c, c_smul_D_eq_centralizer⟩ :=
      conjugate_centralizers_of_IsConj (SpecialMatrices.d δ) x x_IsConj_d
  rw [centralizer_d_eq_D δ δ_ne_one δ_ne_neg_one] at c_smul_D_eq_centralizer
  -- A = conj c • D ⊓ G ≤ conj c • D F
  have A_le_conj_D :=
      le_trans (le_of_eq A_eq_centra) <|
      le_trans inf_le_left (le_of_eq c_smul_D_eq_centralizer.symm)
  -- to prove A has cardinality coprime to p we construct the following homomorphism
  -- compose the monoid homomorphisms of inclusions and isomorphisms
  let f₁ : A →* (conj c • D F:) := inclusion A_le_conj_D
  let f₂ : (conj c • D F:) →* D F := (MulEquiv.subgroupMap (conj c) (D F)).symm.toMonoidHom
  let f₃ : (D F) →* Fˣ := (D_iso_units F).toMonoidHom
  let f : A →* Fˣ := f₃.comp (f₂.comp f₁)
  -- f is injective
  have f_inj : Injective f := by
    dsimp [f]
    apply Injective.comp
    exact MulEquiv.injective (D_iso_units F)
    apply Injective.comp
    -- we construct the monoid homomorphism from the isomorphism
    exact MulEquiv.injective (MulEquiv.subgroupMap (conj c) (D F)).symm
    -- we construct the inclusion monoid homomorphism
    exact inclusion_injective A_le_conj_D
  -- to prove A is cyclic we construct the following homomorphism
  -- `F *← Fˣ *← A`
  let f' : A →* F := (Units.coeHom F).comp f
  have f'_inj : Injective f' := by
    dsimp [f']
    apply Injective.comp
    exact Units.coeHom_injective
    exact f_inj
  let inst : Finite A := A_eq_centra ▸ Set.Finite.subset hG₀ inf_le_right
  split_ands
  · use c
    use D F ⊓ conj c⁻¹ • G
    split_ands
    · apply Set.Finite.subset (s := conj c⁻¹ • G)
      exact
        Set.Finite.of_surjOn
          (⇑((MulDistribMulAction.toMonoidEnd (MulAut SL(2, F)) SL(2, F)) (conj c⁻¹)))
          (fun ⦃a⦄ a ↦ a) hG₀
      rw [← Set.le_iff_subset, coe_inf]
      apply inf_le_right
    · exact inf_le_left
    · rw [smul_inf, smul_smul, MonoidHom.map_inv, mul_inv_cancel,
        one_smul, c_smul_D_eq_centralizer, A_eq_centra]
    -- cardinality of A is coprime to p, the characteristic of F as Fˣ has no element of order p
    -- after looking at the frobenius endomorphism
  · exact coprime_card_fin_subgroup_of_inj_hom_group_iso_units A f f_inj
      -- A is cyclic as it is finite and there exists a monoid monomorphism into F
  · exact isCyclic_of_subgroup_isDomain f' f'_inj

#check map_inf_eq
lemma centralizer_eq_conj_SZ_of_IsConj_s_or_IsConj_neg_s {F : Type*} [Field F]
  [IsAlgClosed F] [DecidableEq F] (A G : Subgroup SL(2,F)) (σ : F) (x : SL(2,F))
  (x_IsConj_s_or_neg_s : IsConj (s σ) x ∨ IsConj (- s σ) x)
  (x_in_G : x ∈ G.carrier) (x_not_in_center : x ∉ center SL(2,F)) (hx : centralizer {x} ⊓ G = A) :
  ∃ c : SL(2,F), conj c • SZ F = centralizer {x} := by
  simp [center_SL2_eq_Z, ← ne_eq] at x_not_in_center
  obtain ⟨x_ne_one, x_ne_neg_one⟩ := x_not_in_center
  have σ_ne_zero : σ ≠ 0 := by
    rintro rfl
    simp at x_IsConj_s_or_neg_s
    symm at x_IsConj_s_or_neg_s
    rcases x_IsConj_s_or_neg_s with (rfl | rfl) <;> contradiction
  rcases x_IsConj_s_or_neg_s with (x_IsConj_s | x_IsConj_neg_s)
  · obtain ⟨c, c_smul_SZ_eq_centralizer⟩ :=
      conjugate_centralizers_of_IsConj (s σ) x x_IsConj_s
    rw [centralizer_s_eq_SZ σ_ne_zero] at c_smul_SZ_eq_centralizer
    exact Exists.intro c c_smul_SZ_eq_centralizer
  · obtain ⟨c, c_smul_SZ_eq_centralizer⟩ :=
      conjugate_centralizers_of_IsConj (- s σ) x x_IsConj_neg_s
    rw [← centralizer_neg_eq_centralizer,
      centralizer_s_eq_SZ σ_ne_zero] at c_smul_SZ_eq_centralizer
    exact Exists.intro c c_smul_SZ_eq_centralizer



theorem Nat.Prime.three_le_of_ne_two {p : ℕ} (hp : Nat.Prime p) (p_ne_two : p ≠ 2) : 3 ≤ p := by
  by_contra! h
  revert p_ne_two hp
  intro hp p_ne_two
  have p_le_two : p ≤ 2 := by linarith
  have p_lt_two : p < 2 := by apply lt_of_le_of_ne p_le_two p_ne_two
  have one_lt_p := hp.one_lt
  linarith



lemma exists_noncenter_of_card_center_lt_card_center_Sylow (F : Type*) [Field F] {p : ℕ}
  [hp' : Fact (Nat.Prime p)] [hC : CharP F p] (G : Subgroup SL(2,F)) [Finite G] (S : Sylow p G)
  (p_le_card_center_S : p ≤ Nat.card ↥(center S)) :
  ∃ x ∈ (Subgroup.map (G.subtype.comp S.toSubgroup.subtype) (center S)), x ∉ center SL(2,F) := by
  let fintype_G : Fintype G := Fintype.ofFinite ↥G
  let fintype_center_S : Fintype (center S) := Fintype.ofFinite ↥(center S)
  let fintype_set_center_S :
    Fintype (center SL(2, F)) := Fintype.ofFinite ↥(center SL(2, F))
  let fintype_map :
        Fintype
          ((Subgroup.map (G.subtype.comp S.toSubgroup.subtype) (center S)) : Set SL(2,F)) := by
        rw [Subgroup.coe_map, MonoidHom.coe_comp]
        exact Fintype.ofFinite ↑(⇑G.subtype ∘ ⇑(S.toSubgroup).subtype '' ↑(center S))
  let fintype_image :
        Fintype
          ↑((⇑(G.subtype.comp S.toSubgroup.subtype) '' (center S)) : Set SL(2,F)) := fintype_map
  have : Fintype.card
        ((Subgroup.map (G.subtype.comp S.toSubgroup.subtype) (center S)) : Set SL(2,F)) =
          Fintype.card (center S) := by
        apply Set.card_image_of_injective
        rw [MonoidHom.coe_comp]
        refine Injective.comp ?h1 ?h2
        · exact subtype_injective G
        · exact subtype_injective S.toSubgroup
  let inst₁ : CommRing F := Field.toCommRing
  let inst₂ : NoZeroDivisors F := IsLeftCancelMulZero.to_noZeroDivisors F
  have card_center_lt_card_center_S :
    Fintype.card ((center SL(2,F)) : Set SL(2,F)) <
      Fintype.card
        ((Subgroup.map (G.subtype.comp S.toSubgroup.subtype) (center S)) : Set SL(2,F)) := by
    by_cases hp : p = 2
    · calc
      Fintype.card (center SL(2, F)) = Nat.card (center SL(2,F)) := Fintype.card_eq_nat_card
      _ = 1 := by
        rw [center_SL2_eq_Z, card_Z_eq_one_of_two_eq_zero];
        simp only [hp] at hC
        exact CharTwo.two_eq_zero
      _ < 2 := by norm_num
      _ ≤ Nat.card ↥(center S) := hp ▸ p_le_card_center_S
      _ = Fintype.card (center S) := Nat.card_eq_fintype_card
      _ = Fintype.card ↑↑(Subgroup.map (G.subtype.comp S.toSubgroup.subtype) (center S)) := by
        symm
        apply Set.card_image_of_injective
        rw [MonoidHom.coe_comp]
        apply Injective.comp
        exact subtype_injective G
        exact subtype_injective _
    · let two_ne_zero : NeZero (2 : F) := NeZero_two_of_char_ne_two F hp
      calc
      Fintype.card (center SL(2, F)) = Nat.card (center SL(2,F)) := Fintype.card_eq_nat_card
      _ = 2 := by rw [center_SL2_eq_Z, card_Z_eq_two_of_two_ne_zero]
      _ < 3 := by norm_num
      _ ≤ p := Nat.Prime.three_le_of_ne_two hp'.out hp
      _ ≤ Nat.card ↥(center S) := p_le_card_center_S
      _ = Fintype.card (center S) := Nat.card_eq_fintype_card
      _ = Fintype.card ↑↑(Subgroup.map (G.subtype.comp S.toSubgroup.subtype) (center S)) := by
        symm
        apply Set.card_image_of_injective
        rw [MonoidHom.coe_comp]
        apply Injective.comp
        exact subtype_injective G
        exact subtype_injective _
  have coe₁ :
    Set.ncard ((center SL(2,F)) : Set SL(2,F)) = Fintype.card (center SL(2, F)) := by
      rw [Fintype.card_eq_nat_card]; rfl
  have coe₂ :
    Set.ncard ((Subgroup.map (G.subtype.comp S.toSubgroup.subtype) (center S)) : Set SL(2,F))
      = Fintype.card
          ((Subgroup.map (G.subtype.comp S.toSubgroup.subtype) (center S)) : Set SL(2,F)) := by
            rw [Fintype.card_eq_nat_card]; rfl
  have ncard_center_lt_ncard_center_S : Set.ncard ((center SL(2,F)) : Set SL(2,F)) <
    Set.ncard ((Subgroup.map (G.subtype.comp S.toSubgroup.subtype) (center S)) : Set SL(2,F)) := by
        rw [coe₁, coe₂]
        exact card_center_lt_card_center_S
  exact Set.exists_mem_not_mem_of_ncard_lt_ncard ncard_center_lt_ncard_center_S


theorem mul_center_inj {F : Type*} [Field F] (S Q : Subgroup SL(2,F))
  (Q_le_S : Q ≤ S) (h' : (1 : SL(2,F)) = -1 ∨ -1 ∉ S)
  (hSQ : S.carrier * center SL(2,F) = Q.carrier * center SL(2,F)) : S = Q := by
  symm
  apply le_antisymm Q_le_S
  intro s s_in_S
  have key : s * 1 ∈ S.carrier * center SL(2,F) := by
    use s, s_in_S, 1, Subgroup.one_mem _
  simp [hSQ] at key
  obtain ⟨q, q_in_Q, z, z_in_center, hx⟩ := key
  simp [center_SL2_eq_Z] at z_in_center
  rcases z_in_center with (rfl | rfl)
  · simp at hx
    simp [← hx]
    exact q_in_Q
  · rcases h' with (one_eq_neg_one | h')
    · rw [one_eq_neg_one] at hx
      simp at hx
      rw [← hx]
      exact q_in_Q
    -- order of every element must divide p^S and 2 does not divide p^S
    · have neg_one_in_S : q⁻¹ * s ∈ S := by
        refine Subgroup.mul_mem S ?q_inv_in_S s_in_S
        apply Subgroup.inv_mem
        apply Q_le_S q_in_Q
      have : -1 = q⁻¹ * s := by rw [← hx]; group
      rw [← this] at neg_one_in_S
      contradiction


theorem A_eq_Q_join_Z_of_IsConj_s_or_neg_s {F : Type*} [Field F]
  [IsAlgClosed F] [DecidableEq F] {p : ℕ} [hp' : Fact (Nat.Prime p)] [hC : CharP F p]
  (G : Subgroup SL(2,F))[hG₀ : Finite G] (A : Subgroup SL(2,F))
  (hA : A ∈ MaximalAbelianSubgroupsOf G) (center_le_G : center SL(2,F) ≤ G)
  (center_lt_A : center SL(2,F) < A) (x : SL(2,F))
  (x_in_G : x ∈ G.carrier) (x_not_in_center : x ∉ center SL(2,F))
  (A_eq_centra : A = centralizer {x} ⊓ G) (σ : F)
  (x_IsConj_t_or_neg_t : IsConj (s σ) x ∨ IsConj (- s σ) x) :
  ∃ Q : Subgroup SL(2,F),
  Nontrivial Q ∧
  Finite Q ∧
  Q ≤ G ∧
  A = Q ⊔ Z F ∧
  IsElementaryAbelian p Q ∧
  ∃ S : Sylow p G, Q.subgroupOf G = S := by
  -- centralizer {x} = conj c • TZ F
  obtain ⟨c, c_smul_TZ_eq_centralizer ⟩:=
    centralizer_eq_conj_SZ_of_IsConj_s_or_IsConj_neg_s
      A G σ x x_IsConj_t_or_neg_t x_in_G x_not_in_center A_eq_centra.symm
  have A_eq_conj_T_join_Z_meet_G : A = (conj c • (S F ⊔ Z F)) ⊓ G := by
      rw [A_eq_centra, S_join_Z_eq_SZ, c_smul_TZ_eq_centralizer]
  -- from the subgroup equality and conjugacy isomorphisms
  -- we construct the isomorphisms and compose all of them
  -- `A = conj c • (S F ⊔ Z F) ⊓ G `
  let f₁ := (MulEquiv.subgroupCongr A_eq_conj_T_join_Z_meet_G)
  -- `(conj c • S F ⊔ Z F) ⊓ G = ((conj c • (S F ⊔ Z F)) ⊓ G) ≃* A`
  let f₂ := (MulEquiv.subgroupCongr (conj_S_join_Z_meet_G_eq_conj_S_meet_G_join_Z center_le_G c))
  -- `conj c⁻¹ • ((conj c • S F ⊔ G) ⊓ Z F) ≃* conj c • S F ⊓ G ⊔ Z F`
  let f₃ := (equivSMul (conj c⁻¹) (conj c • S F ⊓ G ⊔ Z F))
  -- `(S F ⊔ conj c⁻¹ • G) ⊓ Z F = conj c⁻¹ • ((conj c • S F ⊔ G) ⊓ Z F)`
  let f₄ := MulEquiv.subgroupCongr (conj_inv_conj_eq F G c)
  -- Compose all isomorphism together to get the desired isomorphism
  let φ : A ≃* ((S F ⊓ conj c⁻¹ • G) ⊔ Z F :) := ((f₁.trans f₂).trans f₃).trans f₄
  -- the monoid homomorphism composed by the pull back composed with
  -- the inclusion of A into SL(2,F)
  let f : ((S F ⊓ conj c⁻¹ • G) ⊔ Z F :) →* SL(2,F) := A.subtype.comp (φ.symm.toMonoidHom)
  have f_inj : Injective f := by
    apply Injective.comp (Subtype.val_injective) <| MulEquiv.injective φ.symm
  -- pull back `S F ⊓ conj c⁻¹ • G ` along the monoid homomorphism
  let Q := Subgroup.map f ((S F ⊓ conj c⁻¹ • G :).subgroupOf ((S F ⊓ conj c⁻¹ • G) ⊔ Z F :))
  -- necessary for proving Q is p-Sylow
  have nontrivial_Q : Nontrivial Q := by
    refine (nontrivial_iff_ne_bot Q).mpr ?_
    intro Q_eq_bot
    simp only [Q] at Q_eq_bot
    -- injective map has trivial kernel
    rw [(map_eq_bot_iff_of_injective ((S F ⊓ conj c⁻¹ • G).subgroupOf (S F ⊓ conj c⁻¹ • G ⊔ Z F))
          f_inj)] at Q_eq_bot
    have : S F ⊓ conj c⁻¹ • G ≤ S F ⊓ conj c⁻¹ • G ⊔ Z F := le_sup_left
    rw [← bot_subgroupOf, subgroupOf_inj, bot_inf_eq, inf_of_le_left this] at Q_eq_bot
    -- if S F ⊓ conj c⁻¹ • G = ⊥ then there is an isomorphism from A to Z
    -- the different sizes of the cardinality provide a contradiction
    rw [Q_eq_bot, bot_sup_eq, ← center_SL2_eq_Z] at φ
    have card_A_le_two : Nat.card A ≤ Nat.card (center SL(2,F)) :=
      le_of_eq (Nat.card_eq_of_bijective φ <| MulEquiv.bijective φ)
    let fin_center : Finite (center SL(2,F)) := by
      rw [center_SL2_eq_Z]
      infer_instance
    let Fintype_center : Fintype (center SL(2,F)) := Fintype.ofFinite ↥(center SL(2, F))
    let fin_A : Finite A := Set.Finite.subset hG₀ hA.right
    let Fintype_A : Fintype A := Fintype.ofFinite ↥A
    have card_center_lt_card_A : Nat.card (center SL(2,F)) < Nat.card A := by
      calc Nat.card (center SL(2,F)) = Fintype.card (center SL(2,F)) := Nat.card_eq_fintype_card
      _ < Fintype.card A := Set.card_lt_card center_lt_A
      _ = Nat.card A := Fintype.card_eq_nat_card
    linarith
  have Q_le_G : Q ≤ G := by
    let Q₀ := ((S F ⊓ conj c⁻¹ • G).subgroupOf (S F ⊓ conj c⁻¹ • G ⊔ Z F))
    have h₁: Subgroup.map φ.symm.toMonoidHom Q₀ ≤ ⊤ := le_top
    have h₂ :
      Subgroup.map A.subtype (Subgroup.map φ.symm.toMonoidHom Q₀) ≤ Subgroup.map A.subtype ⊤ :=
      map_subtype_le_map_subtype.mpr h₁
    have eq_A : Subgroup.map A.subtype ⊤ = A := by ext; simp
    rw [eq_A, Subgroup.map_map] at h₂
    exact le_trans h₂ hA.right
  have Q_fin : Finite Q := by
    apply Set.Finite.image
    apply Set.Finite.preimage
    · exact Injective.injOn fun ⦃a₁ a₂⦄ a ↦ a
    apply Set.Finite.preimage
    · simp [Set.injOn_subtype_val]
    · apply Set.Finite.inf_of_right
      exact Set.Finite.of_surjOn
          (⇑((MulDistribMulAction.toMonoidEnd (MulAut SL(2, F)) SL(2, F)) (conj c⁻¹)))
          (fun ⦃a⦄ a ↦ a) hG₀
  have orderOf_eq_p : ∀ (h : ↥Q), h ≠ 1 → orderOf h = p := by
    rintro ⟨q, t₀, t₀_in_subgroupOf, hf⟩ q_ne_one
    obtain ⟨⟨σ₀, hσ₀⟩, t₀_in_conj_G⟩ := t₀_in_subgroupOf
    have : ((1 : (S F ⊓ conj c⁻¹ • G ⊔ Z F :)) : SL(2,F)) = 1 := rfl
    -- σ ≠ 0, as otherwise f q = 1 → q = 1; a contradiction
    have σ₀_ne_zero : σ₀ ≠ 0 := by
      intro σ_eq_zero
      simp [σ_eq_zero] at hσ₀
      rw [← this, ← Subtype.ext_iff] at hσ₀
      simp [← hσ₀] at hf
      simp [← hf] at q_ne_one
    have orderOf_t₀_eq_p := @order_s_eq_char F _ p _ _ σ₀ σ₀_ne_zero
    simp [hσ₀] at orderOf_t₀_eq_p
    -- By injectivity of f the orders must be the same
    have orderOf_q_eq_p : orderOf q = p :=
      hf.symm ▸ orderOf_t₀_eq_p ▸ orderOf_injective f f_inj t₀
    rw [← orderOf_q_eq_p]
    exact orderOf_mk q (Exists.intro t₀ ⟨⟨Exists.intro σ₀ hσ₀, t₀_in_conj_G⟩, hf⟩)
  have IsElementaryAbelian_Q : IsElementaryAbelian p Q := by
    refine ⟨?IsCommutative_Q, ?orderOf_eq_p⟩
    case IsCommutative_Q =>
      let CommInst₁ : IsCommutative (S F ⊓ conj c⁻¹ • G) :=
        inf_IsCommutative_of_IsCommutative_left (S F) (conj c⁻¹ • G) (IsCommutative_S F)
      let CommInst₂ : IsCommutative ((S F ⊓ conj c⁻¹ • G).subgroupOf (S F ⊓ conj c⁻¹ • G ⊔ Z F)) :=
        subgroupOf_isCommutative _ _
      exact Subgroup.map_isCommutative _ _
      -- Every element is order p
    case orderOf_eq_p => exact orderOf_eq_p
  -- We show A is the join of Q and Z
  have A_eq_Q_join_Z : A = Q ⊔ Z F := by
    have ker_f_eq_bot : f.ker = ⊥ := by
      exact (MonoidHom.ker_eq_bot_iff f).mpr f_inj
    have Z_le_A : Z F ≤ A := (le_of_lt ((center_SL2_eq_Z F).symm ▸ center_lt_A))
    have Z_le_range : Z F ≤ f.range := by
      intro z hz
      use (φ.toMonoidHom ⟨z, Z_le_A hz⟩)
      simp [f]
    have map_eq_map_iff := ker_f_eq_bot ▸
      @map_eq_map_iff (S F ⊓ conj c⁻¹ • G ⊔ Z F:) _ SL(2,F)
        _ f (Subgroup.comap f (Z F)) ((Z F).subgroupOf (S F ⊓ conj c⁻¹ • G ⊔ Z F))
    -- Manually check that every element in Z is preserved under f
    let inst : Nonempty ↥(S F ⊓ (conj c)⁻¹ • G ⊔ Z F) := One.instNonempty
    have key :
      Subgroup.map φ.symm.toMonoidHom (((Z F).subgroupOf (S F ⊓ conj c⁻¹ • G ⊔ Z F))) =
        (Z F).subgroupOf A := by
      ext z
      -- easier than unpacking all layers of conjugation and isomorphisms
      constructor
      · intro hz
        simp at hz
        obtain ⟨a, ha, a_mem_Z, rfl⟩ := hz
        simp [mem_subgroupOf] at a_mem_Z ⊢
        rcases a_mem_Z with (rfl | rfl)
        · left; rfl
        · right
          simp [φ, f₁, f₂, f₃, f₄]
      · intro hz
        simp [mem_subgroupOf] at hz ⊢
        rcases hz with (rfl | h)
        · left; rfl
        · right
          have z_eq_neg_one : z = ⟨-1, Z_le_A <| neg_one_mem_Z⟩ := by
            simp only [← h, Subtype.coe_eta]
          simp [z_eq_neg_one]
          have Z_le_join : Z F ≤ S F ⊓ (conj c)⁻¹ • G ⊔ Z F := le_sup_right
          use Z_le_join <| neg_one_mem_Z
          simp [Subtype.ext_iff, φ, f₁, f₂, f₃, f₄]
    have comap_Z_eq_Z : Subgroup.comap f (Z F) = (Z F).subgroupOf (S F ⊓ conj c⁻¹ • G ⊔ Z F) := by
      rw [← sup_bot_eq (Subgroup.comap f (Z F)),
      ← sup_bot_eq ((Z F).subgroupOf (S F ⊓ conj c⁻¹ • G ⊔ Z F)),
      ← map_eq_map_iff, map_comap_eq, inf_of_le_right Z_le_range,
      ← Subgroup.map_map, key, subgroupOf_map_subtype, left_eq_inf]
      exact Z_le_A
    have Q_le_range : Q ≤ f.range := by
      exact map_le_range f ((S F ⊓ conj c⁻¹ • G).subgroupOf (S F ⊓ conj c⁻¹ • G ⊔ Z F))
    have A_le_range : A ≤ f.range := by
      intro a ha
      use (φ.toMonoidHom ⟨a, ha⟩)
      simp [f]
    apply le_antisymm
    · rw [← comap_le_comap_of_le_range A_le_range,
        ← comap_sup_eq_of_le_range f Q_le_range Z_le_range,
        comap_map_eq_self_of_injective f_inj, comap_Z_eq_Z,
        sup_subgroupOf_eq ?h1 ?h2]
      rw [subgroupOf_self]
      exact le_top
      case h1 => exact SemilatticeSup.le_sup_left (S F ⊓ conj c⁻¹ • G) (Z F)
      case h2 => exact SemilatticeSup.le_sup_right (S F ⊓ conj c⁻¹ • G) (Z F)
    · have Q_join_Z_le_range : Q ⊔ Z F ≤ f.range := sup_le Q_le_range Z_le_range
      rw [← comap_le_comap_of_le_range Q_join_Z_le_range,
        ← comap_sup_eq_of_le_range f Q_le_range Z_le_range]
      rw [comap_map_eq_self_of_injective f_inj]
      rw [comap_Z_eq_Z, sup_subgroupOf_eq ?h1 ?h2]
      rw [subgroupOf_self]
      case h1 => exact SemilatticeSup.le_sup_left (S F ⊓ conj c⁻¹ • G) (Z F)
      case h2 => exact SemilatticeSup.le_sup_right (S F ⊓ conj c⁻¹ • G) (Z F)
      intro q _hq
      simp [f]
  -- Show Q satisfies the desired properties
  use Q
  refine ⟨?Q_is_nontrivial, ?Q_is_finite, ?Q_le_G, ?A_eq_Q_join_Z, ?IsElementaryAbelian, ?IsPSylow⟩
  case Q_is_nontrivial => exact nontrivial_Q
  -- Q is finite as it is the image of a subgroup of a finite group S F ⊓ conj c⁻¹ • G ⊔ Z F
  case Q_is_finite => exact Q_fin
  -- Q ≤ A ≤ G, have to extract data before it is sent through the inclusion
  case Q_le_G => exact Q_le_G
  -- pushing Q ⊔ Z through f⁻¹ will yield (S F ⊓ conj c⁻¹ • G ⊔ Z which is isomorphic to A
  case A_eq_Q_join_Z => exact A_eq_Q_join_Z
  -- Q is commutative because it is the image of a subgroup of a commutative group
  case IsElementaryAbelian => exact IsElementaryAbelian_Q
  -- Is p-Sylow
  case IsPSylow =>
    -- as Q.subgroupOf G ≃* Q, Q.subgroupOf G is nontrivial as Q is nontrivial
    have nontrivial_Q_subgroupOf_G: Nontrivial (Q.subgroupOf G) :=
      (subgroupOfEquivOfLe Q_le_G).nontrivial
    -- Q.subgroupOf G is finite as it is the preimage of a finite set on an injective function
    let subgroupOf_fin : Finite (Q.subgroupOf G) := by
      apply Set.Finite.preimage
      · exact Injective.injOn fun ⦃a₁ a₂⦄ a ↦ a
      exact Set.toFinite (Q.subgroupOf G).carrier
    have IsElementaryAbelian_Q_subgroupOf_G :=
      @subgroupOf SL(2,F) _ Q G p _ IsElementaryAbelian_Q
    have bot_lt_Q_subgroupOf_G : ⊥ < Q.subgroupOf G := by
      apply Ne.bot_lt'
      symm
      rw [← nontrivial_iff_ne_bot]
      exact nontrivial_Q_subgroupOf_G
    have IsPGroup_Q_subgroupOf_G:=
      @IsPGroup
        G _ p hp'.out (Q.subgroupOf G) _ IsElementaryAbelian_Q_subgroupOf_G bot_lt_Q_subgroupOf_G
    have exists_Sylow := @IsPGroup.exists_le_sylow p G _ (Q.subgroupOf G) IsPGroup_Q_subgroupOf_G
    obtain ⟨S, hS⟩ := exists_Sylow
    use S
    refine le_antisymm ?Q_le_S ?S_le_Q
    case Q_le_S =>
      exact hS
    case S_le_Q =>
      -- As Q is nontrivial, S must be nontrivial as there is an injection from Q to S
      have nontrivial_S : Nontrivial S := Injective.nontrivial (inclusion_injective hS)
      let nonempty_center_S : Nonempty (center S) := One.instNonempty
      have zero_lt_card_center_S : 0 < Nat.card (center S) := Nat.card_pos
      have p_dvd_card_center_S :=
        @IsPGroup.p_dvd_card_center S p hp'.out _ _ nontrivial_S S.isPGroup'
      have p_le_card_center_S : p ≤ Nat.card (center S) := by
        apply Nat.le_of_dvd zero_lt_card_center_S p_dvd_card_center_S
      -- Given the cardinality of `center S` is greater than cardinality of `center SL(2,F)`,
      -- there must exist an element of center S that does not lie in SL(2,F)
      obtain ⟨y, y_in_center_S, y_not_in_center⟩ :=
        @exists_noncenter_of_card_center_lt_card_center_Sylow F _ p _ _ G _ S p_le_card_center_S
      let inst : CommGroup (center S) := IsCommutative.commGroup (center S)
      have y_commutes_in_S : ∀ w : S, w * y = y * w := by
        intro w
        simp only [mem_map] at y_in_center_S
        obtain ⟨y', y'_in_center, rfl⟩ := y_in_center_S
        have w_eq : (G.subtype.comp S.toSubgroup.subtype) w = ((w : G) : SL(2,F)) := rfl
        -- Pull back w through the inclusion
        rw [← w_eq, ← MonoidHom.map_mul, ← MonoidHom.map_mul]
        congr 1
        rw [mem_center_iff] at y'_in_center
        exact y'_in_center _
      have S_join_Z_le_centra_meet_G :
        ((Subgroup.map G.subtype S.toSubgroup) ⊔ Z F :) ≤ centralizer {y} ⊓ G := by
        intro w hw
        rw [← center_SL2_eq_Z, ← SetLike.mem_coe,  mul_normal (N := center SL(2,F))] at hw
        obtain ⟨s', hs, z, z_in_center, rfl⟩ := hw
        simp at hs
        obtain ⟨s'_in_G, s''_in_S⟩ := hs
        simp
        split_ands
        · simp [mem_centralizer_iff]
          -- Coerce the following equality
          have y_commutes_with_s :
            y * (⟨(⟨s', s'_in_G⟩ : G), s''_in_S⟩ : S) =
              (⟨(⟨s', s'_in_G⟩ : G), s''_in_S⟩ : S)  * y := by
            symm; exact y_commutes_in_S _
          simp at y_commutes_with_s
          simp [mem_center_iff] at z_in_center
          rw [mul_assoc, ← z_in_center y, ← mul_assoc, y_commutes_with_s]
          group
        · exact (Subgroup.mul_mem_cancel_right G (center_le_G z_in_center)).mpr s'_in_G
      have Q_le_range_inclusion_G : Q ≤ G.subtype.range := by simp only [range_subtype, Q_le_G]
      have Q_le_map_S : Q ≤ (Subgroup.map G.subtype S.toSubgroup) := by
        rw [← comap_le_comap_of_le_range Q_le_range_inclusion_G]
        apply le_trans hS
        exact le_comap_map G.subtype ↑S
      -- A = Q ⊔ Z ≤ S ⊔ Z = centralizer {y} ⊓ G
      -- so by the maximality of A and because S ⊔ Z = centralizer {y} ⊓ G is commutative
      -- Q ⊔ Z = S ⊔ Z and Q ≤ S which implies Q = S
      have Q_join_Z_le_S_join_Z : Q ⊔ Z F ≤ (Subgroup.map G.subtype S.toSubgroup) ⊔ Z F :=
        sup_le_sup_right Q_le_map_S (Z F)
      have y_in_G : y ∈ G := by
        simp only [mem_map] at y_in_center_S
        obtain ⟨w, w_in_center_S, hw⟩ := y_in_center_S
        simp at hw
        rw [← hw]
        simp only [← SetLike.mem_coe, Subtype.coe_prop]
      have y_in_G_sdif_center_SL : y ∈ G.carrier \ ↑(center SL(2, F)) := by
        split_ands
        · exact y_in_G
        · exact y_not_in_center
      have centra_y_meet_G_in_MaxAbSub :=
        centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral G
      have A_le_centra_meet_G : A ≤ centralizer {y} ⊓ G := by
        apply le_trans <| le_of_eq A_eq_Q_join_Z
        apply le_trans Q_join_Z_le_S_join_Z
        exact S_join_Z_le_centra_meet_G
      have A_le_range : A ≤ G.subtype.range := by simp; exact hA.right
      have A_subgroupOf_G_le_centra_meet_G_subgroupOf_G :
        A.subgroupOf G ≤ (centralizer {y} ⊓ G).subgroupOf G := by
        simp only [Subgroup.subgroupOf, comap_le_comap_of_le_range A_le_range]
        exact A_le_centra_meet_G
      have IsCommutative_centra_y_meet_G : IsCommutative ((centralizer {y} ⊓ G)) := by
        apply inf_IsCommutative_of_IsCommutative_left
        apply IsCommutative_centralizer_of_not_mem_center _ y_not_in_center
      -- A subgroup of commutative group is commutative
      have IsCommutative_centra_y_meet_G_subgroupOf_G :
        IsCommutative ((centralizer {y} ⊓ G).subgroupOf G) := by
        exact subgroupOf_isCommutative G (centralizer {y} ⊓ G)
      have centra_meet_G_le_range : centralizer {y} ⊓ G ≤ G.subtype.range := by simp
      -- By the maximality of A we have that in fact A = centralizer {y} ⊓ G
      have A_eq_centra_y_meet_G : A = centralizer {y} ⊓ G := by
        apply le_antisymm
        · exact A_le_centra_meet_G
        · have centra_meet_G_le_A := @hA.left.right
            ((centralizer {y} ⊓ G).subgroupOf G)
              IsCommutative_centra_y_meet_G_subgroupOf_G
                A_subgroupOf_G_le_centra_meet_G_subgroupOf_G
          simp only [← comap_le_comap_of_le_range centra_meet_G_le_range]
          exact centra_meet_G_le_A
      -- From this equality we have that Q ⊔ Z = S ⊔ Z
      have Q_join_Z_eq_S_join_Z : Q ⊔ Z F = (Subgroup.map G.subtype S.toSubgroup) ⊔ Z F := by
        apply le_antisymm
        · exact Q_join_Z_le_S_join_Z
        · rw [← A_eq_Q_join_Z]
          apply le_trans
          exact S_join_Z_le_centra_meet_G
          exact le_of_eq A_eq_centra_y_meet_G.symm
      simp only [← center_SL2_eq_Z,
        ← SetLike.coe_set_eq, mul_normal (N := center SL(2,F))] at Q_join_Z_eq_S_join_Z
      -- This statement is key to show that from S ⊔ Z = Q ⊔ Z and S ≤ Q we have that S = Q
      have h' : (1 : SL(2,F)) = (-1 : SL(2,F)) ∨ -1 ∉ (Subgroup.map G.subtype S.toSubgroup) := by
        by_cases hp : p = 2
        -- In char F = 2, -1 = 1
        · left
          apply SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero
          simp only [hp] at hC
          apply CharTwo.two_eq_zero
        -- Order of every element is p but -1 has order 2
        · right
          rw [← ne_eq] at hp
          have ne_zero_two : NeZero (2 : F) := @NeZero_two_of_char_ne_two F _ p hp' hC hp
          intro neg_one_in_S
          have order_neg_one_eq_two : orderOf (-1 : SL(2,F)) = 2 := orderOf_neg_one_eq_two
          have two_dvd_pow_p :=
            @Subgroup.orderOf_dvd_natCard
              SL(2,F) _ (Subgroup.map G.subtype S.toSubgroup) (-1) neg_one_in_S
          have card_image_eq : Nat.card (Subgroup.map G.subtype S) = Nat.card S.toSubgroup := by
            apply card_map_of_injective <| subtype_injective G
          rw [order_neg_one_eq_two, card_image_eq, Sylow.card_eq_multiplicity] at two_dvd_pow_p
          have two_dvd_p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two two_dvd_pow_p
          have two_eq_p : p = 2 :=
            ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp'.out).mp two_dvd_p).symm
          contradiction
      apply le_of_eq
      have := @mul_center_inj
        F _ (Subgroup.map G.subtype S) Q Q_le_map_S h' Q_join_Z_eq_S_join_Z.symm
      have ker_G_subtype_le_S : G.subtype.ker ≤ S :=
        calc
        G.subtype.ker = ⊥ := ker_subtype G
        _ ≤ S := by apply bot_le
      simp only [Subgroup.subgroupOf, ← this]
      rw [comap_map_eq_self ker_G_subtype_le_S]

-- theorem IsConj_fin_subgroup_D : {F : Type*}
--   [Field F] [IsAlgClosed F] [DecidableEq F] {p : ℕ} [hp' : Fact (Nat.Prime p)] [hC : CharP F p]
--   (G : Subgroup SL(2, F)) [hG₀ : Finite ↥G] (A : Subgroup SL(2, F))
--   (hA : A ∈ MaximalAbelianSubgroupsOf G) (center_le_G : center SL(2, F) ≤ G)

theorem IsCyclic_and_card_coprime_CharP_or_eq_Q_join_Z_of_center_ne
  {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] (p : ℕ) [hp' : Fact (Nat.Prime p)]
  [hC : CharP F p] (G : Subgroup SL(2,F))[hG₀ : Finite G] (A : Subgroup SL(2,F))
  (hA : A ∈ MaximalAbelianSubgroupsOf G) (center_le_G : center SL(2,F) ≤ G)
  (center_ne_G : G ≠ center SL(2,F)) :
  (∃ (c : SL(2,F)) (D₀ : Subgroup SL(2,F)), Finite D₀ ∧ D₀ ≤ D F ∧ A = conj c • D₀)
  ∧ (Nat.Coprime (Nat.card A) p ∧ IsCyclic A)
  ∨
  (
  ∃ Q : Subgroup SL(2,F),
  Nontrivial Q ∧
  Finite Q ∧
  Q ≤ G ∧
  A = Q ⊔ Z F ∧
  IsElementaryAbelian p Q ∧
  ∃ S : Sylow p G, Q.subgroupOf G = S
  ) := by
  have center_ne_A : center SL(2,F) ≠ A :=
    (ne_of_mem_of_not_mem hA (center_not_mem_of_center_ne center_ne_G.symm)).symm
  have center_lt_A : center SL(2,F) < A :=
    lt_of_le_of_ne (center_le G A hA center_le_G) center_ne_A
  -- Take the element that belongs to A but does not belong to Z
  -- We will use this element to show A = centralizer {x} ⊓ G
  obtain ⟨x, ⟨x_in_G, x_not_in_center⟩, A_eq_centra⟩ :=
    eq_centralizer_meet_of_center_lt A G center_lt_A hA
  -- Once shown A = centralizer {x} ⊓ G and recalling x is conjugate to d δ or ± s σ
  -- We show the centralizer in each of these cases is conjugate to finite
  -- commutative subgroups of either D or SZ
  rcases SL2_IsConj_d_or_IsConj_s_or_IsConj_neg_s_of_AlgClosed x with
    (⟨δ, x_IsConj_d⟩ | x_IsConj_s_or_neg_s)
  -- x is conjugate to d δ
  · left
    exact
      IsConj_fin_subgroup_D_and_card_coprime_CharP_and_IsCyclic_of_IsConj_d
        p G A x x_not_in_center A_eq_centra δ x_IsConj_d
  -- x is conjugate to s σ
  · right
    have x_IsConj_s_or_neg_s : ∃ σ, IsConj (s σ) x ∨ IsConj (-s σ) x := by
      rcases x_IsConj_s_or_neg_s with (⟨σ, hσ⟩ | ⟨σ, hσ⟩) <;> use σ
      exact Or.inl hσ
      exact Or.inr hσ
    obtain ⟨σ, x_IsConj_s_or_neg_s⟩ := x_IsConj_s_or_neg_s
    exact
      A_eq_Q_join_Z_of_IsConj_s_or_neg_s G A hA center_le_G center_lt_A x x_in_G
        x_not_in_center A_eq_centra σ x_IsConj_s_or_neg_s



/-
Theorem 2.3 (iii)
-/
theorem IsCyclic_and_card_coprime_CharP_or_eq_Q_join_Z {F : Type*}
  [Field F] [IsAlgClosed F] [DecidableEq F] {p : ℕ} [hp' : Fact (Nat.Prime p)] [hC : CharP F p]
  (G : Subgroup SL(2, F)) [hG₀ : Finite ↥G] (A : Subgroup SL(2, F))
  (hA : A ∈ MaximalAbelianSubgroupsOf G) (center_le_G : center SL(2, F) ≤ G)  :
  IsCyclic ↥A ∧ (Nat.card ↥A).Coprime p
  ∨
  ∃ Q : Subgroup SL(2,F),
    Nontrivial Q ∧ Finite Q ∧ Q ≤ G ∧ A = Q ⊔ Z F ∧
      IsElementaryAbelian p Q ∧ ∃ S : Sylow p G, Q.subgroupOf G = S := by
  obtain (center_eq_G | center_ne_G ) := eq_or_ne G (center SL(2, F))
  case inl =>
    left
    exact IsCyclic_and_card_Coprime_CharP_of_center_eq hp'.out A G hA center_eq_G
  case inr =>
    obtain (⟨-, h₁, h₂⟩ | h₃) :=
    IsCyclic_and_card_coprime_CharP_or_eq_Q_join_Z_of_center_ne p G A hA
      center_le_G center_ne_G
    · left
      exact ⟨h₂, h₁⟩
    · right
      exact h₃






#check IsCyclic_and_card_Coprime_CharP_of_center_eq

#check IsCyclic_and_card_coprime_CharP_or_eq_Q_join_Z_of_center_ne

-- could probably generalise to any map
lemma iff_conj_MaximalAbelianSubgroupsOf_conj {G : Type* } [Group G]
  (A H : Subgroup G) (c : G) :
  A ∈ MaximalAbelianSubgroupsOf H ↔ conj c • A ∈ MaximalAbelianSubgroupsOf (conj c • H) := by
  constructor
  · intro ⟨⟨hA₁, hA₂⟩, A_le_H⟩
    split_ands
    · rw [@IsCommutative_iff]
      intro ⟨⟨x, hx₁⟩, hx₂⟩ ⟨⟨y, hy₁⟩, hy₂⟩
      have hx₁' := hx₁
      have hy₁' := hy₁
      rw [mem_smul_pointwise_iff_exists] at hx₁' hy₁'
      simp
      obtain ⟨x', hx'⟩ := hx₁'
      obtain ⟨y', hy'⟩ := hy₁'
      simp [mem_subgroupOf] at hx₂ hy₂
      rw [← hx'.right] at hx₂
      rw [← hy'.right] at hy₂
      rw [@smul_mem_pointwise_smul_iff] at hx₂ hy₂
      rw [@IsCommutative_iff] at hA₁
      specialize hA₁ ⟨
        ⟨x', hx'.left⟩, mem_subgroupOf.mpr hx₂⟩ ⟨⟨y', hy'.left⟩, mem_subgroupOf.mpr hy₂⟩
      simp [← hx'.right, ← hy'.right]
      simpa using hA₁
    -- We show that the image of A under conjugation is maximal abelian subgroup
    · intro K IsCommutative_K le_K
      have h₁ : IsCommutative (conj c⁻¹ • map (conj c • H).subtype K) :=
        map_isCommutative (Subgroup.map (conj c • H).subtype K)
            ((MulDistribMulAction.toMonoidEnd (MulAut G) G) (conj c⁻¹))
      have h₂ : IsCommutative ((conj c⁻¹ • map (conj c • H).subtype K).subgroupOf H) := by
        exact subgroupOf_isCommutative H (conj c⁻¹ • Subgroup.map (conj c • H).subtype K)
      have le_H : conj c⁻¹ • map (conj c • H).subtype K ≤ H := by
        rw [@pointwise_smul_subset_iff, MonoidHom.map_inv, inv_inv]
        intro x hx
        rw [mem_map] at hx
        obtain ⟨x', x'_mem_K, hx⟩ := hx
        simp [← hx]
      have A_subgroupOf_le : A.subgroupOf H
        ≤ (conj c⁻¹ • Subgroup.map (conj c • H).subtype K).subgroupOf H := by
        rw [← @map_subtype_le_map_subtype, map_subgroupOf_eq_of_le A_le_H,
          subgroupOf_map_subtype, inf_of_le_left le_H, subset_pointwise_smul_iff, MonoidHom.map_inv,
          inv_inv]
        rwa [← map_subtype_le_map_subtype, subgroupOf_map_subtype,
          ← smul_inf, inf_of_le_left A_le_H] at le_K
      have le_A_subgroupOf := hA₂ h₂ A_subgroupOf_le
      rw [← @map_subtype_le_map_subtype, map_subgroupOf_eq_of_le le_H, pointwise_smul_subset_iff,
        MonoidHom.map_inv, inv_inv] at le_A_subgroupOf
      rwa [map_subgroupOf_eq_of_le A_le_H, map_le_iff_le_comap] at le_A_subgroupOf
    · exact pointwise_smul_le_pointwise_smul_iff.mpr A_le_H
  · intro ⟨⟨hA₁, hA₂⟩, A_le_H⟩
    split_ands
    · replace hA₁ := hA₁.is_comm.comm
      rw [@IsCommutative_iff]
      intro ⟨x, hx⟩ ⟨y, hy⟩
      have conj_x_mem_conj_H : conj c • H.subtype x ∈ (conj c • H) := by
        rw [smul_mem_pointwise_smul_iff, coeSubtype]
        exact SetLike.coe_mem x
      have conj_y_mem_conj_H : conj c • H.subtype y ∈ (conj c • H) := by
        rw [smul_mem_pointwise_smul_iff, coeSubtype]
        exact SetLike.coe_mem y
      simp only [Subtype.forall, MulMemClass.mk_mul_mk, Subtype.mk.injEq] at hA₁
      specialize hA₁ (conj c • H.subtype x) conj_x_mem_conj_H
        (by rw [mem_subgroupOf, smul_mem_pointwise_smul_iff]; exact hx)
        (conj c • H.subtype y) conj_y_mem_conj_H
        (by rw [mem_subgroupOf, smul_mem_pointwise_smul_iff]; exact hy)
      simpa [← Subtype.val_inj] using hA₁
    · intro K IsCommutative_K A_subgroupOf_le_K
      have IsCommutative_conj_K :
        IsCommutative ((conj c • (map H.subtype K) ).subgroupOf (conj c • H)) := by
          rw [IsCommutative_iff]
          intro ⟨x, hx⟩ ⟨y, hy⟩
          replace IsCommutative_K := IsCommutative_K.is_comm.comm
          simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
          rw [mem_subgroupOf, mem_smul_pointwise_iff_exists] at hx hy
          obtain ⟨x', x'_mem_map, hx'⟩ := hx
          obtain ⟨y', y'_mem_map, hy'⟩ := hy
          rw [mem_map] at x'_mem_map y'_mem_map
          obtain ⟨x'', x''_mem_K, hx''⟩ := x'_mem_map
          obtain ⟨y'', y''_mem_K, hy''⟩ := y'_mem_map
          simp only [← hx'', coeSubtype, MulAut.smul_def, conj_apply] at hx'
          simp only [← hy'', coeSubtype, MulAut.smul_def, conj_apply] at hy'
          simp only [← Subtype.val_inj, Subgroup.coe_mul, ← hx', ← hy']
          specialize IsCommutative_K ⟨x'', x''_mem_K⟩ ⟨y'', y''_mem_K⟩
          suffices x'' * y'' = y'' * x'' by
            rw [
              show c * ↑x'' * c⁻¹ * (c * ↑y'' * c⁻¹) = c * ↑y'' * c⁻¹ * (c * ↑x'' * c⁻¹)
                ↔ c * (↑x'' * ↑y'') * c⁻¹ = c * (↑y'' * ↑x'') * c⁻¹ by
                  group]
            simp only [_root_.mul_left_inj, _root_.mul_right_inj]
            simpa [← Subtype.val_inj] using this
          simpa using IsCommutative_K
      have le_conj_H : conj c • Subgroup.map H.subtype K ≤ conj c • H := by
        rw [@pointwise_smul_le_pointwise_smul_iff]
        exact map_subtype_le K
      have conj_A_subgroupOf_conj_H_le : (conj c • A).subgroupOf (conj c • H)
        ≤ (conj c • Subgroup.map H.subtype K).subgroupOf (conj c • H) := by
        rw [← map_subtype_le_map_subtype, map_subgroupOf_eq_of_le A_le_H,
        subgroupOf_map_subtype, inf_of_le_left le_conj_H, pointwise_smul_le_pointwise_smul_iff]
        rwa [← @map_subtype_le_map_subtype, subgroupOf_map_subtype,
        inf_of_le_left (pointwise_smul_le_pointwise_smul_iff.mp A_le_H)] at A_subgroupOf_le_K
      specialize hA₂ IsCommutative_conj_K conj_A_subgroupOf_conj_H_le
      rwa [← map_subtype_le_map_subtype, map_subgroupOf_eq_of_le le_conj_H,
        map_subgroupOf_eq_of_le A_le_H, pointwise_smul_le_pointwise_smul_iff,
        map_le_iff_le_comap] at hA₂
    · exact pointwise_smul_le_pointwise_smul_iff.mp A_le_H



/- Theorem 2.3 (iv a) If A ∈ M and |A| is relatively prime to p, then we have [N_G (A) : A] ≤ 2. -/
theorem index_normalizer_le_two {p : ℕ} [hp : Fact (Nat.Prime p)]
  {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] [CharP F p] (p_ne_two : p ≠ 2)
  (A G : Subgroup SL(2,F)) (center_le_G : center SL(2,F) ≤ G)
  (hA : A ∈ MaximalAbelianSubgroupsOf G) [hG : Finite G]
  (hA' : Nat.Coprime (Nat.card A) p) : ((A.subgroupOf G).subgroupOf (A.subgroupOf G).normalizer).index ≤ 2 := by
  by_cases h : Nat.card A ≤ 2

  · have key := eq_center_of_card_le_two p_ne_two A G center_le_G hA h
    rw [key]
    have center_is_normal : Normal ((center SL(2,F)).subgroupOf G) := normal_subgroupOf
    rw [normalizer_eq_top_iff.mpr center_is_normal, ← comap_subtype, ← subgroupOf_self, index_comap,
      Subgroup.range_subtype, relindex_subgroupOf fun ⦃x⦄ a ↦ a]

    have G_eq_center : G = center SL(2,F) := by
      rw [key] at hA
      contrapose! hA
      exact center_not_mem_of_center_ne hA.symm
    suffices (center SL(2, F)).relindex G = 1 by linarith
    rw [relindex_eq_one]
    exact le_of_eq_of_le G_eq_center fun ⦃x⦄ a ↦ a
  · simp only [not_le] at h
    have G_ne_center : G ≠ center SL(2,F) := by
      intro G_eq_center
      have A_eq_center : A = center SL(2,F) := by
        rw [← Set.mem_singleton_iff, ← singleton_of_center_eq_G G G_eq_center]
        exact hA
      have card_le_two : Nat.card A ≤ 2 := by
        rw [A_eq_center, center_SL2_eq_Z]
        exact card_Z_le_two
      linarith
    rcases IsCyclic_and_card_coprime_CharP_or_eq_Q_join_Z_of_center_ne p G A hA
      center_le_G G_ne_center with (⟨A_cyclic, -⟩ | h)
    · obtain ⟨c, A', Finite_A', A'_le_D, A_eq_conj_A'⟩ := A_cyclic
      let G' := conj c⁻¹ • G
      have G_eq_conj_G' : G = conj c • G' := by simp [G']
      have hA' : A' ∈ MaximalAbelianSubgroupsOf G' := by
        rw [iff_conj_MaximalAbelianSubgroupsOf_conj A' G' c, ← A_eq_conj_A', ← G_eq_conj_G']
        exact hA
      have normalizer_eq : conj c⁻¹ • map G.subtype (A.subgroupOf G).normalizer
        = map G'.subtype (A'.subgroupOf G').normalizer := by
        ext x
        constructor
        · intro hx
          rw [mem_smul_pointwise_iff_exists] at hx
          obtain ⟨s, hs, conj_s_eq_x⟩ := hx
          rw [mem_map] at hs ⊢
          obtain ⟨s', hs', h⟩ := hs
          rw [mem_normalizer_iff''] at hs'
          have conj_A_eq_A' : conj c⁻¹ • A = A' := by
            rwa [← inv_smul_eq_iff, ← MonoidHom.map_inv] at A_eq_conj_A'
          have conj_G_eq_G' : conj c⁻¹ • G = G' := rfl
          refine Exists.intro
            ⟨
            conj c⁻¹ • s',
            by
            rw [mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
            exact s'.property⟩
            ⟨?_,  ?_⟩
          · rw [mem_normalizer_iff'']
            intro a'
            constructor
            · intro ha'
              simp [mem_subgroupOf] at ha' ⊢
              rw [← conj_A_eq_A', mem_smul_pointwise_iff_exists] at ha'
              obtain ⟨a'', a''_mem_A, conj_a''_eq_a'⟩ := ha'
              rw [← conj_a''_eq_a']
              rw [MulAut.smul_def, conj_apply]
              group
              specialize hs' ⟨a'', hA.right a''_mem_A⟩
              simp [mem_subgroupOf] at hs'
              simp_rw [A_eq_conj_A', mem_pointwise_smul_iff_inv_smul_mem, ← MonoidHom.map_inv,
                MulAut.smul_def, conj_apply] at hs'
              group at hs'
              rw [← hs']
              rw [zpow_neg_one, ← conj_inv_apply, ← MulAut.smul_def,
                ← mem_pointwise_smul_iff_inv_smul_mem, ← A_eq_conj_A']
              exact a''_mem_A
            · intro ha'
              simp [mem_subgroupOf] at ha' ⊢
              group at ha'
              rw [zpow_neg_one, zpow_neg_one,
                (by group :
                  c⁻¹ * (↑s')⁻¹ * c * ↑a' * c⁻¹ * ↑s' * c
                    = c⁻¹ *( (↑s')⁻¹ * c * ↑a' * c⁻¹ * ↑s') * c),
                ← conj_inv_apply, ← MulAut.smul_def, ← mem_pointwise_smul_iff_inv_smul_mem,
                ← A_eq_conj_A'] at ha'
              simp [← conj_A_eq_A', mem_pointwise_smul_iff_inv_smul_mem]
              specialize hs' ⟨
                  c * a' * c⁻¹,
                  by
                  rw [← conj_apply, ← MulAut.smul_def, ← inv_inv (conj c),
                    ← mem_pointwise_smul_iff_inv_smul_mem,
                    ← MonoidHom.map_inv, conj_G_eq_G']
                  exact a'.prop
                  ⟩
              simp [mem_subgroupOf] at hs'
              rw [hs']
              group at ha' ⊢
              exact ha'
          · rw [coeSubtype] at h
            simpa [h] using conj_s_eq_x
        · intro hx
          rw [mem_map] at hx
          rw [mem_pointwise_smul_iff_inv_smul_mem, MonoidHom.map_inv, inv_inv, mem_map,
            G_eq_conj_G']
          obtain ⟨x', x'_mem_A', hx'⟩ := hx
          have  mem_conj_G' : conj c • G'.subtype x' ∈ conj c • G' := by
            rw [smul_mem_pointwise_smul_iff]
            simp only [coeSubtype, SetLike.coe_mem, G']
          have mem_normalizer : ⟨conj c • G'.subtype x', mem_conj_G'⟩
            ∈ (A.subgroupOf (conj c • G')).normalizer := by
            rw [mem_normalizer_iff] at x'_mem_A' ⊢
            intro ⟨z, hz⟩
            constructor
            · intro hz'
              simp_rw [mem_subgroupOf] at hz' x'_mem_A' ⊢
              rw [mem_pointwise_smul_iff_inv_smul_mem] at hz
              specialize x'_mem_A' ⟨(conj c)⁻¹ • z, hz⟩
              simp at x'_mem_A'
              simp [A_eq_conj_A', mem_pointwise_smul_iff_inv_smul_mem]
              group at x'_mem_A' ⊢
              rw [← x'_mem_A']
              rw [A_eq_conj_A'] at hz'
              simpa [mem_pointwise_smul_iff_inv_smul_mem] using hz'
            · intro hz'
              simp_rw [mem_subgroupOf] at hz' x'_mem_A' ⊢
              rw [mem_pointwise_smul_iff_inv_smul_mem] at hz
              simp at hz'
              specialize x'_mem_A' ⟨(conj c)⁻¹ • z, hz⟩
              simp only [MulAut.smul_def, conj_inv_apply, Subgroup.coe_mul,
                InvMemClass.coe_inv] at x'_mem_A'
              simp only [A_eq_conj_A', mem_pointwise_smul_iff_inv_smul_mem, smul_mul',
                MulAut.smul_def, conj_inv_apply, inv_mul_cancel, one_mul, smul_inv', mul_inv_rev,
                inv_inv] at hz' ⊢
              group at hz' x'_mem_A' ⊢
              rwa [x'_mem_A']
          use ⟨conj c • G'.subtype x', mem_conj_G'⟩, mem_normalizer
          simpa
      have index_eq : ((A'.subgroupOf G').subgroupOf (A'.subgroupOf G').normalizer).index = ((A.subgroupOf G).subgroupOf (A.subgroupOf G).normalizer).index := by
        -- rw [A_eq_conj_A', G_eq_conj_G']
        rw [index_eq_card, index_eq_card]

        -- let φ := MulEquiv.subgroupCongr G_eq_conj_G'
        -- define one quotient to be the image of another, to do this one must define the monoid homomorphism between G and G',
        -- and show that the normalizer is the preimage of one normalizer contains the other.
        -- exact (QuotientGroup.congr G' sorry sorry).toEquiv
        -- let ϕ := ((MulDistribMulAction.toMonoidEnd (MulAut SL(2, F)) SL(2, F)) (conj c⁻¹))
        rw [← inv_smul_eq_iff, ← MonoidHom.map_inv] at A_eq_conj_A' G_eq_conj_G'
        let φ : (A.subgroupOf G).normalizer ≃* (A'.subgroupOf G').normalizer :=
          {
            toFun := fun ⟨g, hg⟩ => ⟨
                ⟨
                  conj c⁻¹ • G.subtype g,
                  by
                  dsimp only [G']
                  rw [smul_mem_pointwise_smul_iff]
                  exact g.property⟩,
                by
                  rw [mem_normalizer_iff] at hg ⊢
                  intro h
                  constructor
                  · intro h_mem_A'
                    rw [← A_eq_conj_A', mem_subgroupOf, mem_pointwise_smul_iff_inv_smul_mem]
                    simp only [map_inv, inv_inv, coeSubtype, MulAut.smul_def, conj_inv_apply,
                      Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, smul_mul', smul_inv',
                      conj_apply, _root_.mul_inv_cancel_right, G']
                    group
                    rw [← A_eq_conj_A', mem_subgroupOf] at h_mem_A'
                    have conj_h_mem_G : conj c • G'.subtype h ∈ G := by
                      rw [← @mem_inv_pointwise_smul_iff, ← MonoidHom.map_inv, G_eq_conj_G']
                      exact h.property
                    specialize hg ⟨conj c • h, conj_h_mem_G⟩
                    simp only [MulAut.smul_def, conj_apply, mem_subgroupOf, Subgroup.coe_mul,
                      InvMemClass.coe_inv, G'] at hg
                    group at hg
                    rw [← hg]
                    simpa [MonoidHom.map_inv, mem_pointwise_smul_iff_inv_smul_mem, inv_inv,
                      MulAut.smul_def, conj_apply, G'] using h_mem_A'
                  · intro conj_mem_A'
                    rw [mem_subgroupOf]
                    have conj_h_mem_G : conj c • G'.subtype h ∈ G := by
                      rw [← mem_inv_pointwise_smul_iff, ← MonoidHom.map_inv, G_eq_conj_G']
                      exact h.property

                    specialize hg ⟨conj c • G'.subtype h,  conj_h_mem_G⟩
                    simp only [coeSubtype, MulAut.smul_def, conj_apply, mem_subgroupOf,
                      Subgroup.coe_mul, InvMemClass.coe_inv, G'] at hg
                    simp only [← A_eq_conj_A', MonoidHom.map_inv,
                      mem_pointwise_smul_iff_inv_smul_mem, inv_inv, MulAut.smul_def, conj_apply, G']
                    rw [hg]
                    simp [mem_subgroupOf, ← A_eq_conj_A',
                      mem_pointwise_smul_iff_inv_smul_mem] at conj_mem_A'
                    group at conj_mem_A' ⊢
                    assumption
                ⟩
            invFun := fun ⟨g', hg'⟩ => ⟨
                ⟨
                  conj c • G'.subtype g',
                  by
                  rw [MonoidHom.map_inv, inv_smul_eq_iff,] at G_eq_conj_G'
                  rw [G_eq_conj_G', smul_mem_pointwise_smul_iff]
                  exact g'.property⟩ ,
                by
                  rw [mem_normalizer_iff] at hg' ⊢
                  intro g
                  constructor
                  · intro hg
                    simp only [mem_subgroupOf, coeSubtype, MulAut.smul_def, conj_apply,
                      Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv, G'] at hg ⊢
                    specialize hg' ⟨
                      conj c⁻¹ • g,
                      by rw [← G_eq_conj_G', smul_mem_pointwise_smul_iff]; apply g.property
                      ⟩
                    simp only [map_inv, MulAut.smul_def, conj_inv_apply, mem_subgroupOf,
                      Subgroup.coe_mul, InvMemClass.coe_inv, G'] at hg'
                    rw [smul_eq_iff_eq_inv_smul, MonoidHom.map_inv, inv_inv] at A_eq_conj_A'
                    simp only [A_eq_conj_A', mem_pointwise_smul_iff_inv_smul_mem, smul_mul',
                      MulAut.smul_def, conj_inv_apply, inv_mul_cancel, one_mul, smul_inv',
                      mul_inv_rev, inv_inv] at hg ⊢
                    group at hg hg' ⊢
                    rwa [← hg']
                  · intro hg
                    rw [mem_subgroupOf] at hg ⊢
                    specialize hg' ⟨
                        conj c⁻¹ • g,
                        by rw [← G_eq_conj_G', smul_mem_pointwise_smul_iff]; apply g.property
                        ⟩
                    simp only [map_inv, MulAut.smul_def, conj_inv_apply, mem_subgroupOf,
                      Subgroup.coe_mul, InvMemClass.coe_inv, G'] at hg'
                    rw [smul_eq_iff_eq_inv_smul, MonoidHom.map_inv, inv_inv] at A_eq_conj_A'
                    simp [A_eq_conj_A', mem_pointwise_smul_iff_inv_smul_mem] at hg ⊢
                    group at hg hg' ⊢
                    rwa [hg']
                ⟩
            left_inv := by
              intro g
              simp only [map_inv, coeSubtype, MulAut.smul_def, conj_inv_apply, smul_mul', smul_inv',
                conj_apply, _root_.mul_inv_cancel_right]
              group
            right_inv := by
              intro g'
              simp only [map_inv, coeSubtype, MulAut.smul_def, conj_apply, smul_mul',
                conj_inv_apply, inv_mul_cancel, one_mul, smul_inv']
              group
            map_mul' := by
              intro g₁ g₂
              simp
          }
        have : Subgroup.map φ ((A.subgroupOf G).subgroupOf (A.subgroupOf G).normalizer)
          = (A'.subgroupOf G').subgroupOf (A'.subgroupOf G').normalizer := by
          sorry
        -- let p : Normal ((A.subgroupOf G).normalizer) := by apply?
        let ϕ := QuotientGroup.congr
          ((A.subgroupOf G).subgroupOf (A.subgroupOf G).normalizer)
          ((A'.subgroupOf G').subgroupOf (A'.subgroupOf G').normalizer) φ this


        refine Nat.card_congr ϕ.symm
      have two_lt_card_A' : 2 < Nat.card A' := by sorry
      have normalizer_A'_le_DW := normalizer_subgroup_D_eq_DW two_lt_card_A' A'_le_D
      -- have := QuotientGroup.quotientInfEquivProdNormalQuotient (H := A'.normalizer ⊓ G') (N := (D F).subgroupOf (D F).normalizer)
















      -- problem: One is equality between subgroups and the other is an isomorphism



      -- let Normal_A: Normal A := by apply?
      -- let Normal_A : Normal (A.subgroupOf G) := by
      --   refine normal_subgroupOf
      -- let f₁ : A →* (conj c • D F:) := inclusion A_le_conj_D
      -- let f₂ : (conj c • D F:) →* D F := (MulEquiv.subgroupMap (conj c) (D F)).symm.toMonoidHom
      -- Show that the quotient is a subgroup of ℤ₂ and thus its order is less than 2.
      sorry
    -- Contradiction since the cardinality of A is coprime to p and
    -- should A = Q ⊔ Z where Q is p elementary abelian, then p ∣ |A|
    · obtain ⟨Q, hQ, Q_Finite, Q_le_G, A_eq_Q_join_Z, Q_isElementaryAbelian, -⟩ := h
      -- rw [A_eq_Q_join_Z] at hA'
      suffices p ∣ Nat.card A by
        have contr : ¬ Nat.Coprime (Nat.card A) p := by
          rwa [Nat.coprime_comm, ← Nat.Prime.dvd_iff_not_coprime hp.out]
        contradiction
      trans Nat.card Q
      rw [nontrivial_iff_ne_bot, ← bot_lt_iff_ne_bot] at hQ
      apply Q_isElementaryAbelian.dvd_card hQ
      rw [A_eq_Q_join_Z]
      apply Subgroup.card_dvd_of_le
      exact le_sup_left

#check QuotientGroup.map
#check MulEquiv.toEquiv
/-
Theorem 2.3 (iv b) Furthermore, if [NG (A) : A] = 2,
then there is an element y of NG (A)\A such that, yxy⁻¹ = x⁻¹  for all x ∈ A.
 -/
theorem of_index_normalizer_eq_two {F : Type*} [Field F] {p : ℕ }(A G : Subgroup SL(2,F))
  (hA : A ∈ MaximalAbelianSubgroupsOf G) (hA' : Nat.Coprime (Nat.card A) p)
  (hNA : A.normalizer.index = 2) (x : A) :
  ∃ y ∈ A.normalizer.carrier \ A, y * x * y⁻¹ = x⁻¹ := by sorry

/-
Theorem 2.3 (v a) Let Q be a Sylow p-subgroup of G.
If Q = { I_G }, then there is a cyclic subgroup K of G such that N_G (Q) = Q K.
-/
theorem exists_IsCyclic_K_normalizer_eq_Q_join_K {F : Type*} [Field F] { p : ℕ }
  (hp : Nat.Prime p)
  (G : Subgroup SL(2,F))
  (Q : Sylow p G)
  (h : Q.toSubgroup ≠ ⊥) :
  ∃ K : Subgroup G, IsCyclic K ∧ normalizer Q.toSubgroup = Q.toSubgroup ⊔ K := by sorry

/-
Theorem 2.3 (v b)If |K| > |Z|, then K ∈ M.
-/
theorem K_mem_MaximalAbelianSubgroups_of_center_lt_card_K {F : Type*} [Field F] { p : ℕ } [hp' : Fact (Nat.Prime p)] (G : Subgroup SL(2,F))
  (Q : Sylow p G) (h : Q.toSubgroup ≠ ⊥) (K : Subgroup G)(hK : IsCyclic K)
  (hNG : normalizer Q.toSubgroup = Q.toSubgroup ⊔ K) (h : Nat.card K > Nat.card (center SL(2,F))) :
  map G.subtype K ∈ MaximalAbelianSubgroupsOf G := by
  sorry

end MaximalAbelianSubgroup

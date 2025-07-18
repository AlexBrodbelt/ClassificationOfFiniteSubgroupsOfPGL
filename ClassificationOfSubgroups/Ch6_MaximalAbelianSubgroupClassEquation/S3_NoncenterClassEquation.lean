import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_MaximalAbelianSubgroup
import Mathlib

set_option linter.style.longLine true
set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0


universe u


open Matrix MatrixGroups Subgroup MulAut MaximalAbelianSubgroup Pointwise SpecialSubgroups


/- The non-central part of a subgroup -/
def Subgroup.noncenter {G : Type*} [Group G] (H : Subgroup G) : Set G :=
  H.carrier \ center G




/-
Definition. The set $\mathcal{C}(A) = Cl(A) = \{x A x^{-1} \; | \; x ∈ G \}$
is called the conjugacy class of $A \in \mathcal{M}$.
-/
def ConjClassOfSet {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G)  :=
  { conj x • A.val | x ∈ G }

/- let M∗ be the set of all Aᵢ* and let Cᵢ* be the conjugacy class of Aᵢ* .-/
def noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :=
  { noncenter (K : Subgroup SL(2,F)) | K ∈ MaximalAbelianSubgroupsOf G }

def noncenter_ConjClassOfSet {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : noncenter_MaximalAbelianSubgroupsOf G)  :=
  { conj x • A.val | x ∈ G }


noncomputable def card_noncenter_ConjClassOfSet {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) : noncenter_MaximalAbelianSubgroupsOf G → ℕ :=
  fun A => Nat.card (noncenter_ConjClassOfSet G A)

section noncenter_MaximalAbelianSubgroupsOf


lemma noncenter_mem_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : A.val.noncenter ∈ noncenter_MaximalAbelianSubgroupsOf G := by
  use A, A.prop

#check noncenter_MaximalAbelianSubgroupsOf

/-
Define the equivalence relation $\sim$ on $\mathcal{M}^*$ by
$A_i \sim A_j$ if and only if $A_i = x A_j x^{-1}$ for some $x \in G$.
 -/
instance lift_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Setoid (noncenter_MaximalAbelianSubgroupsOf G) where
  r A B := ∃ x ∈ G, conj x • A.val = B.val
  iseqv := {
    refl := by rintro A
               exact ⟨1, Subgroup.one_mem G, by simp⟩
    symm := by
      rintro A B ⟨x, x_in_G, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact ⟨x_in_G, hx.symm⟩
    trans := by
      rintro A B C ⟨x, x_in_G,  hx⟩ ⟨y, y_in_G, hy⟩
      use y * x
      rw [← hy, ← hx, smul_smul, MonoidHom.map_mul]
      exact ⟨Subgroup.mul_mem G y_in_G x_in_G, rfl⟩
  }

def Partition_lift_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) := (lift_noncenter_MaximalAbelianSubgroupsOf G).classes

#check Partition_lift_noncenter_MaximalAbelianSubgroupsOf

#check Setoid.IsPartition.sUnion_eq_univ

#check sUnion_memPartition

#check Set
/-
Define $C (A)^* = \bicup_{x \in G} x A^*  x^{-1}$
-/
def union_conj_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  noncenter_MaximalAbelianSubgroupsOf G → Set SL(2,F) :=
    fun A => ⋃ x ∈ G, conj x • A.val

lemma noncenter_C_eq_of_related {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :
 (∀ (A B : (noncenter_MaximalAbelianSubgroupsOf G)),
  A ≈ B → union_conj_noncenter_MaximalAbelianSubgroupsOf G A =
     union_conj_noncenter_MaximalAbelianSubgroupsOf G B) := by
  intro A B ArB
  obtain ⟨r, r_in_G, hr⟩ := ArB
  simp [union_conj_noncenter_MaximalAbelianSubgroupsOf]
  ext y
  constructor
  <;> intro hy
  <;> simp only [Set.mem_iUnion, exists_prop] at hy ⊢
  <;> obtain ⟨g, g_in_G, y_in_conj⟩ := hy
  · simp only [← hr]
    use g * r⁻¹
    split_ands
    · exact Subgroup.mul_mem G g_in_G (inv_mem r_in_G)
    · simp only [_root_.map_mul, map_inv, ← MulAction.mul_smul, inv_mul_cancel_right]
      exact y_in_conj
  · simp only [←  hr] at y_in_conj
    use g * r
    split_ands
    · exact Subgroup.mul_mem G g_in_G r_in_G
    rw [_root_.map_mul, MulAction.mul_smul]
    exact y_in_conj

def lift_union_conj_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :=
  @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G)
    (f := union_conj_noncenter_MaximalAbelianSubgroupsOf G) (noncenter_C_eq_of_related G)



end noncenter_MaximalAbelianSubgroupsOf

section MaximalAbelianSubgroupsOf
/-
We define the equivalence relation on the set of Maximal Abelian Subgroups of `G`, a finite
group of `SL(2,F)`
-/
instance lift_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Setoid (MaximalAbelianSubgroupsOf G) where
  r A B := ∃ x ∈ G, conj x • A.val = B.val
  iseqv := {
    refl A := ⟨1, Subgroup.one_mem _ , by simp⟩
    symm := by
      rintro ⟨A, hA⟩  ⟨B, hB⟩ ⟨x, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact ⟨hx.left, hx.right.symm⟩
    trans := by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      split_ands
      apply Subgroup.mul_mem G hy.left hx.left
      rw [← hy.right, ← hx.right, smul_smul, MonoidHom.map_mul]
  }

-- noncomputable def card_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
--   (G : Subgroup SL(2,F)) [Finite G] : MaximalAbelianSubgroupsOf G → ℕ :=
--   fun A => Nat.card ((A.val.carrier \ (center SL(2,F)).carrier) :)

-- /-
-- The function which computes the cardinality of the noncentral part of a maximal abelian subgroup,
-- respects the equivalence relation on the setoid of maximal abelian subgroups of `G`.
-- -/
-- lemma card_eq_of_related_noncenter_subgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
--   (center_le_G : center SL(2,F) ≤ G)[ hG : Finite G] :
--   ∀ (A B : (MaximalAbelianSubgroupsOf G)),
--     A ≈ B → card_noncenter_MaximalAbelianSubgroupsOf G A =
--       card_noncenter_MaximalAbelianSubgroupsOf G B := by
--   rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨x, x_in_G, rfl⟩
--   simp only [card_noncenter_MaximalAbelianSubgroupsOf, center_toSubmonoid,
--     Submonoid.center_toSubsemigroup, pointwise_smul_toSubmonoid, Set.Nat.card_coe_set_eq]
--   let center_finite : Finite (center SL(2, F)) := by
--     rw [center_SL2_eq_Z]
--     infer_instance
--   have center_le_A : (Subsemigroup.center SL(2, F)).carrier ⊆ A.carrier :=
--     @MaximalAbelianSubgroup.center_le SL(2,F) _ G A hA center_le_G
--   let center_coe_finite : Finite (Subsemigroup.center SL(2, F)).carrier := center_finite
--   have center_le_conj_A :
--     (Subsemigroup.center SL(2, F)).carrier ⊆ (conj x • A.toSubmonoid).carrier := by
--     intro z hz
--     rw [Submonoid.mem_carrier, Submonoid.mem_pointwise_smul_iff_inv_smul_mem]
--     have hz' := hz
--     rw [Subsemigroup.mem_carrier, Subsemigroup.mem_center_iff] at hz'
--     simp only [MulAut.smul_def, conj_inv_apply, mem_toSubmonoid]
--     rw [hz' x⁻¹]
--     group
--     exact center_le_A hz
--   rw [Set.ncard_diff center_le_A, Set.ncard_diff center_le_conj_A]
--   have key : (conj x • A.toSubmonoid).carrier.ncard = A.carrier.ncard := by
--     symm
--     refine Set.ncard_congr (fun a ha ↦ x * a * x⁻¹) ?closure ?injective ?surjective
--     case closure =>
--       intro a ha
--       simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
--         Submonoid.mem_pointwise_smul_iff_inv_smul_mem,
--         smul_mul', MulAut.smul_def, conj_inv_apply, inv_mul_cancel, one_mul, smul_inv',
--         mem_toSubmonoid]
--       group
--       exact ha
--     case injective =>
--       intro a b ha hb hab
--       simp only [mul_left_inj, mul_right_inj] at hab
--       exact hab
--     case surjective =>
--       rintro b ⟨y, hy, rfl⟩
--       use y, hy
--       congr
--   rw [key]

noncomputable def card_noncenter {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : noncenter_MaximalAbelianSubgroupsOf G → ℕ :=
  fun A => Nat.card A.val

/-
The function which computes the cardinality of the noncentral part of a maximal abelian subgroup,
respects the equivalence relation on the setoid of maximal abelian subgroups of `G`.
-/
lemma card_noncenter_eq_of_related {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] :
  ∀ (A B : (noncenter_MaximalAbelianSubgroupsOf G)),
    A ≈ B → card_noncenter G A =
      card_noncenter G B := by
  rintro ⟨A_star, A, A_in_MaxAbSub, hA⟩ ⟨B_star, B, B_in_MaxAbSub, hB⟩ ⟨x, x_in_G, rfl⟩
  simp only [card_noncenter, center_toSubmonoid,
    Submonoid.center_toSubsemigroup, pointwise_smul_toSubmonoid, Set.Nat.card_coe_set_eq]
  let center_finite : Finite (center SL(2, F)) := by
    rw [center_SL2_eq_Z]
    infer_instance
  simp

/-
We lift the function which computes the cardinality of the noncentral part of a maximal subgroup
-/
noncomputable def lift_card_noncenter {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] := @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G)
    (f := card_noncenter G)
    (card_noncenter_eq_of_related G)


def toConjClassOfSet {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : noncenter_MaximalAbelianSubgroupsOf G → Set (Set SL(2,F)) :=
  fun A => noncenter_ConjClassOfSet G A

lemma conj_noncenter_eq_noncenter_conj {F : Type*} [Field F] {G :Subgroup SL(2,F)}
  (A : MaximalAbelianSubgroupsOf G) (x : SL(2,F)) :
  (conj x • A.val).noncenter = conj x • A.val.noncenter := by
  ext y
  constructor
  · rintro ⟨⟨a, a_in_A, rfl⟩, conj_a_not_in_center⟩
    simp at conj_a_not_in_center ⊢
    simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_mul', MulAut.smul_def, conj_inv_apply,
      inv_mul_cancel, one_mul, smul_inv']
    group
    have a_not_in_center : a ∉ center SL(2,F) := by
      intro a_in_center
      rw [mem_center_iff] at a_in_center
      have contr : x * a * x⁻¹ ∈ center SL(2,F) := by
        rw [mem_center_iff]
        rw [a_in_center x]
        group
        exact a_in_center
      contradiction
    exact ⟨a_in_A, a_not_in_center⟩
  · rintro ⟨a, ⟨a_in_A, a_not_in_center⟩, rfl⟩
    simp
    rw [noncenter, Set.mem_diff]
    split_ands
    · simp only [pointwise_smul_toSubmonoid, Subsemigroup.mem_carrier,
      Submonoid.mem_toSubsemigroup, Submonoid.mem_pointwise_smul_iff_inv_smul_mem, smul_mul',
      MulAut.smul_def, conj_inv_apply, inv_mul_cancel, one_mul, smul_inv', mem_toSubmonoid]
      group
      exact a_in_A
    · intro conj_in_center
      rw [SetLike.mem_coe, mem_center_iff] at conj_in_center
      have a_in_center : a ∈ center SL(2,F) := by
        rw [mem_center_iff]
        intro g
        specialize conj_in_center (x * g * x⁻¹)
        group at conj_in_center
        rw [mul_left_inj, mul_assoc, mul_assoc, mul_right_inj] at conj_in_center
        exact conj_in_center
      contradiction

lemma toConjClassOfSet_eq_of_related_noncenter_subgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  (∀ (A B : noncenter_MaximalAbelianSubgroupsOf G),
    A ≈ B → toConjClassOfSet G A = toConjClassOfSet G B) := by
  intro A B ArB
  obtain ⟨x, x_in_G, hx⟩ := ArB
  simp [toConjClassOfSet, noncenter_ConjClassOfSet]
  ext s
  constructor
  · rintro ⟨y, y_in_G, rfl⟩
    simp only [← hx, Set.mem_setOf_eq]
    use y * x⁻¹
    rw [MonoidHom.map_mul, MulAction.mul_smul, smul_left_cancel_iff, map_inv, inv_smul_eq_iff]
    exact ⟨Subgroup.mul_mem G y_in_G (inv_mem x_in_G), rfl⟩
  · rintro ⟨y, y_in_G, rfl⟩
    simp only [← hx, Set.mem_setOf_eq]
    use y * x
    rw [MonoidHom.map_mul, MulAction.mul_smul, smul_left_cancel_iff]
    exact ⟨Subgroup.mul_mem G y_in_G x_in_G, rfl⟩

-- conj_noncenter_eq_noncenter_conj A x

def lift_ConjClassOfSet {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :=
  @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G) (f := toConjClassOfSet G)
    (toConjClassOfSet_eq_of_related_noncenter_subgroups G)


end MaximalAbelianSubgroupsOf

section Finite

open Function

lemma Injective_subroup_to_subset {L : Type*} [Group L] (G : Subgroup L) [Finite G] :
  Injective
    (fun (H : {K | (K : Subgroup L) ≤ G}) =>
      (⟨H.val.carrier, H.property⟩ : {K | K ⊆ G.carrier})) := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ hAB
  simp at hAB ⊢
  refine toSubmonoid_inj.mp ?_
  ext x
  exact Eq.to_iff (congrFun hAB x)


instance finite_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Set.Finite (MaximalAbelianSubgroupsOf G) := by
  apply Set.Finite.subset (s := {K | (K : Subgroup SL(2,F)) ≤ G})
  · apply @Finite.of_injective _ _ ?set_finite _ (Injective_subroup_to_subset G)
    exact Set.Finite.finite_subsets hG
  · intro M hM
    exact hM.right

instance finite_MaximalAbelianSubgroups' {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (MaximalAbelianSubgroupsOf G) :=
    Set.finite_coe_iff.mpr <| finite_MaximalAbelianSubgroups G

instance finite_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : Finite (noncenter_MaximalAbelianSubgroupsOf G) := by
  dsimp [noncenter_MaximalAbelianSubgroupsOf]
  refine Finite.of_surjective (
    fun (A : MaximalAbelianSubgroupsOf G) =>
    (
      ⟨noncenter A.val,
      noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G A⟩ :
      noncenter_MaximalAbelianSubgroupsOf G
    )
    ) ?_
  rintro ⟨A_star, A, A_mem_MaximalAbelianSubgroupsOf, hA⟩
  use ⟨A, A_mem_MaximalAbelianSubgroupsOf⟩
  simp [hA]

instance finite_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (Quotient (lift_MaximalAbelianSubgroupsOf G)) := Quotient.finite _

instance finite_lift_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  Finite (Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)) := Quotient.finite _

noncomputable instance fintype_lift_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  Fintype (Quotient (lift_MaximalAbelianSubgroupsOf G)) := by
  apply fintypeOfNotInfinite
  rw [not_infinite_iff_finite]
  exact finite_MaximalAbelianSubgroups_lift G

noncomputable instance fintype_lift_noncenter_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  Fintype (Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)) := by
  apply fintypeOfNotInfinite
  rw [not_infinite_iff_finite]
  exact finite_lift_noncenter_MaximalAbelianSubgroupsOf G


end Finite

/-
Somehow need to lift this statement

⋃ A_star : lift_noncenter_MaximalAbelianSubgroupsOf G,
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star

or

⋃ A_star : lift_noncenter_MaximalAbelianSubgroupsOf G,
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star.exists_rep.choose


-/

lemma union_noncenter_C_eq_G_diff_center {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  G.carrier \ center SL(2,F) =
    ⋃ A_star : noncenter_MaximalAbelianSubgroupsOf G,
      union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star := by
    ext x
    constructor
    · rintro hx
      rw [Set.mem_iUnion]
      use ⟨
        centralizer {x} ⊓ G \ center SL(2,F), by
        dsimp [noncenter_MaximalAbelianSubgroupsOf]
        use centralizer {x} ⊓ G
        constructor
        · exact centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral G x hx
        · rw [Set.inter_diff_distrib_left]
          have center_le_centralizer : center SL(2,F) ≤ centralizer {x} := center_le_centralizer {x}
          rw [Set.inter_eq_self_of_subset_right center_le_centralizer]
          rfl⟩
      dsimp [union_conj_noncenter_MaximalAbelianSubgroupsOf]
      rw [@Set.mem_iUnion₂]
      use 1
      simp only [_root_.map_one, one_smul, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_diff,
        exists_and_left, exists_prop]
      split_ands
      · exact mem_centralizer_singleton_iff.mpr rfl
      · apply hx.left
      · exact Subgroup.one_mem G
      · apply hx.right
    · intro hx
      rw [@Set.mem_iUnion] at hx
      obtain ⟨A_star, hA⟩ := hx
      dsimp [union_conj_noncenter_MaximalAbelianSubgroupsOf] at hA
      simp [noncenter_MaximalAbelianSubgroupsOf] at A_star
      rw [Set.mem_iUnion₂] at hA
      obtain ⟨c, hc⟩ := hA
      simp only [exists_prop] at hc
      obtain ⟨c_mem_G, x_mem_conj_c⟩ := hc
      obtain ⟨A, A_MaximalAbelian, hA⟩ := A_star.prop
      simp [← hA, noncenter, Set.mem_smul_set_iff_inv_smul_mem] at x_mem_conj_c
      have A_subs_G := A_MaximalAbelian.right
      obtain ⟨x_mem_G, x_not_mem_center⟩ := x_mem_conj_c
      rw [← @conj_inv_apply, ← MulAut.smul_def, ← mem_carrier,
        ← Set.mem_smul_set_iff_inv_smul_mem] at x_mem_G x_not_mem_center
      simp only [Set.mem_diff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
        mem_toSubmonoid, SetLike.mem_coe]
      split_ands
      · apply conj_smul_le_of_le A_subs_G ⟨c, c_mem_G⟩
        apply x_mem_G
      · have conj_center_eq_center : conj c • (center SL(2, F)) = (center SL(2,F)) := by
          exact smul_normal c (center SL(2, F))
        have : conj c • (center SL(2,F)).carrier = (conj c • (center SL(2, F))).carrier := by rfl
        rw [(by rfl : conj c • (center SL(2,F)).carrier = (conj c • (center SL(2, F))).carrier),
          conj_center_eq_center] at x_not_mem_center
        exact x_not_mem_center

-- theorem key {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
--   (G : Subgroup SL(2,F)) [hG : Finite G]  : ⋃ A_star : noncenter_MaximalAbelianSubgroupsOf G,
--       union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star =


/-
Theorem 2.4 i a)
The union of elements of the `Quotient` on the `Setoid`,
`lift_noncenter_MaximalAbelianSubgroups G` is equal to `G \ Z`
-/
lemma union_lift_union_conj_noncenter_MaximalAbelianSubgroupsOf_eq_G_diff_center {F : Type*}
  [Field F] [IsAlgClosed F] [DecidableEq F] (G : Subgroup SL(2,F)) [hG : Finite G] :
  G.carrier \ center SL(2,F) =
    ⋃ A_star : Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G),
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star := by
    rw [union_noncenter_C_eq_G_diff_center]
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx ⊢
      obtain ⟨noncenter_M, hM⟩ := hx
      use Quotient.mk (lift_noncenter_MaximalAbelianSubgroupsOf G) noncenter_M
      exact hM
    · intro hx
      rw [Set.mem_iUnion] at hx ⊢
      obtain ⟨lift_noncenter_M, hM⟩ := hx
      obtain ⟨noncenter_M, hM'⟩ := Quot.exists_rep lift_noncenter_M
      use noncenter_M
      rw [← hM'] at hM
      exact hM

/-
use disjUnion
-/
-- lemma union_equiv_clasess_eq_union_lift {F : Type*}
--   [Field F] [IsAlgClosed F] [DecidableEq F] (G : Subgroup SL(2,F)) [hG : Finite G]  : ⋃ A_star : Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G),
--       lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star = ⋃ A_star : (lift_noncenter_MaximalAbelianSubgroupsOf G).classes, union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star := by sorry

def equivalence_classes {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) := Setoid.isPartition_classes <|lift_noncenter_MaximalAbelianSubgroupsOf G

#check Setoid.IsPartition.sUnion_eq_univ

/-
Theorem 2.4 i b)
Distinct elements in the `Quotient` of the `Setoid`,
`lift_noncenter_MaximalAbelianSubgroups G` map to disjoint subsets
when sent through `lift_noncenter_C`.
-/




section Subsets

def subsets_MaximalAbelianSubgroups {L : Type*} [Group L] (G : Subgroup L) :=
  { (K : Set L) | K ∈ MaximalAbelianSubgroupsOf G }

lemma mem_subsets_MaximalAbelianSubgroups {F : Type*} [Field F] {G : Subgroup SL(2,F)}
  (A : MaximalAbelianSubgroupsOf G) : A.val.carrier ∈ subsets_MaximalAbelianSubgroups G := by
  simp only [subsets_MaximalAbelianSubgroups, Set.mem_setOf_eq];
  use A.val
  simp only [Subtype.coe_prop, true_and]
  congr

noncomputable def finset_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :=
  (@Set.Finite.toFinset _ (s := MaximalAbelianSubgroupsOf G) )
  (h := finite_MaximalAbelianSubgroups G)

open Function

/-
Now we do the same but for MaximalAbelianSubgroups being a Set (Set SL(2,F))
-/
lemma Surjective_MaxAbSub_to_subsets_MaxAbSub {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Surjective
    (fun (A : MaximalAbelianSubgroupsOf G) =>
      (⟨A.val.carrier, mem_subsets_MaximalAbelianSubgroups A⟩ :
        subsets_MaximalAbelianSubgroups G)) := by
    rintro ⟨A, ⟨M, hM₁, hM₂⟩⟩
    use ⟨M, hM₁⟩
    exact SetCoe.ext hM₂

lemma finite_subsets_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [ hG : Finite G] : Set.Finite (subsets_MaximalAbelianSubgroups G) := by
  let inst₀ : Set.Finite (MaximalAbelianSubgroupsOf G) := finite_MaximalAbelianSubgroups G
  let inst₁:  Finite ↑(MaximalAbelianSubgroupsOf G) := inst₀
  exact @Finite.of_surjective
    (α := (MaximalAbelianSubgroupsOf G)) _ _ _ (Surjective_MaxAbSub_to_subsets_MaxAbSub G)

noncomputable def finset_subsets_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] := @Set.Finite.toFinset _
    (s := subsets_MaximalAbelianSubgroups G) (h := finite_subsets_MaximalAbelianSubgroups G)

/-
Define the equivalence relation $\sim$ on $\mathcal{M}^*$ by
$A_i \sim A_j$ if and only if $A_i = x A_j x^{-1}$ for some $x \in G$.
 -/
instance finset_subsets_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] :  Setoid (finset_subsets_MaximalAbelianSubgroups G) where
  r A B := ∃ (x : SL(2,F)), conj x • A.val = B.val
  iseqv := {
    refl A := ⟨1, by simp⟩
    symm := by
      rintro A B ⟨x, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact hx.symm
    trans := by
      rintro A B C ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      rw [← hy, ← hx, smul_smul, MonoidHom.map_mul]
  }

open Setoid


def isPartition_MaximalAbelianSubgroups_lift {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :=
  isPartition_classes (finset_subsets_MaximalAbelianSubgroups_lift G)


noncomputable def finpartition_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] := @Setoid.IsPartition.finpartition SL(2,F)
    (c := finset_subsets_MaximalAbelianSubgroups G)
    --(hc := isPartition_classes (finset_subsets_MaximalAbelianSubgroups_lift G))



end Subsets


/-
Define $C(A) = \bigcup_{x \in G} xA x^{-1}$
-/
def C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G]
  (A : MaximalAbelianSubgroupsOf G) := ⋃ x ∈ G, conj x • A.val.carrier



/-
We compute the cardinality of the noncenter conjugacy class
-/
-- noncomputable def card_noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :
--  noncenter_MaximalAbelianSubgroupsOf G → ℕ := fun A => Nat.card (noncenter_C G A)

/-
We have the relation $|C(A^*)| = |A^*| |\mathcal{C}(A^*)|$
-/
lemma card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet
  {F : Type*} [hF : Field F] (G : Subgroup SL(2,F)) [hG : Finite G]
  (A : noncenter_MaximalAbelianSubgroupsOf G) :
  Nat.card (union_conj_noncenter_MaximalAbelianSubgroupsOf G A) =
    Nat.card A * card_noncenter_ConjClassOfSet G A := by





  sorry

#check Group.nat_card_center_add_sum_card_noncenter_eq_card

#check Group.card_center_add_sum_card_noncenter_eq_card


-- lemma card_noncenter_C_eq_of_related {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :
--   ∀ (A B : noncenter_MaximalAbelianSubgroupsOf G),
--     A ≈ B → card_noncenter_C G A = card_noncenter_C G B := by
--   rintro A B ⟨y, y_in_G, conj_y_A_eq_B⟩
--   simp [card_noncenter_C, noncenter_C, ← conj_y_A_eq_B]
--   congr
--   ext z; constructor <;> rintro ⟨s, hs, z_in_s⟩
--   <;> obtain ⟨g, eq_s⟩ := hs
--   <;> rw [← eq_s] at z_in_s
--   <;> simp [Set.mem_iUnion] at z_in_s ⊢
--   <;> obtain ⟨g_in_G, z_in_conj_g_A⟩ := z_in_s
--   · use g * y⁻¹, Subgroup.mul_mem G g_in_G (inv_mem y_in_G)
--     simp only [_root_.map_mul, map_inv, smul_smul, inv_mul_cancel_right]
--     exact z_in_conj_g_A
--   · use g * y, Subgroup.mul_mem G g_in_G y_in_G
--     rw [_root_.map_mul, ← smul_smul]
--     exact z_in_conj_g_A

-- noncomputable def lift_card_noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :=
--   @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G)
--   (f := card_noncenter_C G) (card_noncenter_C_eq_of_related G)

#check Setoid.isPartition_classes

#check Setoid.IsPartition.pairwiseDisjoint

#check Finset.card_disjiUnion

#check lift_noncenter_MaximalAbelianSubgroupsOf
/-
We have the relation $|C_i^*| = |A_i^*| |\mathcal{C}_i^*|$
-/
lemma card_noncenter_C_eq_card_A_mul_card_noncenter_ConjClass {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G]  (A : noncenter_MaximalAbelianSubgroupsOf G) :
  Nat.card (union_conj_noncenter_MaximalAbelianSubgroupsOf G A) =
    Nat.card A * card_noncenter_ConjClassOfSet G A := by

  sorry

/- $G \setminus Z(\textrm{SL}_2(F)) = \bigcup_{A \in \mathcal{M}} (C A)^*$ -/
lemma subgroup_sdiff_center_eq_union_noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] : G.carrier \ center (SL(2,F)) =
    ⋃ A : noncenter_MaximalAbelianSubgroupsOf G, union_conj_noncenter_MaximalAbelianSubgroupsOf G A := by sorry

/-
Theorem 2.4 ii)
$|\mathcal{C}_i| = |\mathcal{C}_i^*|$
-/
lemma card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) :
  Nat.card (ConjClassOfSet G A) =
    Nat.card (noncenter_ConjClassOfSet G (
      ⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G A⟩
    )) := by sorry

/-
Theorem 2.4 iii)
$|\mathcal{C}_i| = [G : N_G(A_i)]$
-/
lemma card_ConjClassOfSet_eq_index_normalizer {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) :
  Nat.card (ConjClassOfSet G A) = index (normalizer (A.val.subgroupOf G)) := by sorry

noncomputable instance {F : Type*} [Field F] {G : Subgroup SL(2,F)} [Finite G] :
  Fintype (Quotient (lift_MaximalAbelianSubgroupsOf G)) := by infer_instance


/-
the setNormalizer needs to be restricted to G
-/
-- noncomputable def lift_index_normalizer {F : Type*} [Field F] {G : Subgroup SL(2,F)} [Finite G] :=
--   @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G)
--     (fun (A_star : noncenter_MaximalAbelianSubgroupsOf G) => index (setNormalizer (A_star.val)))



/-
Theorem 2.4 iv)
$|G \setminus Z| = \sum_{[A] \in \mathfrak{M} / \sim } |[A*]| |[C(A)*]|$
-/
theorem card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G) :
  Nat.card (G.carrier \ (center SL(2,F)).carrier : Set SL(2,F)) =
  ∑ lift_A : Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G),
    lift_card_noncenter G lift_A * Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G lift_A) := by sorry

#check Sylow

-- inductive lift_noncenter_MaximalAbelianSubgroupsOfType {L : Type*} [Group L] (G : Subgroup L) extends lift_noncenter_MaximalAbelianSubgroupsOf G
--   | S
--   | T

#check MonoidHom



/- Lemma 2.5 N_G(A) = N_G(A*)-/
lemma normalizer_noncentral_eq {F : Type*} [Field F] (A G : Subgroup SL(2,F)) [Finite G]
  (hA : A ∈ MaximalAbelianSubgroupsOf G) : normalizer (A.subgroupOf G) = setNormalizer (noncenter (A.subgroupOf G)) := by
  sorry

/- Lemma Let `Q` be a `p`-Sylow subgroup of `G` then $N_G(Q \sqcup Z) = N_G(Q)$-/
lemma normalizer_Sylow_join_center_eq_normalizer_Sylow {F : Type*} [Field F] {p : ℕ}
[Fact (Nat.Prime p)] [CharP F p] (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) :
  normalizer (map G.subtype Q.toSubgroup ⊔ center SL(2,F)) =
    normalizer (map G.subtype Q.toSubgroup) := by
  sorry



#min_imports

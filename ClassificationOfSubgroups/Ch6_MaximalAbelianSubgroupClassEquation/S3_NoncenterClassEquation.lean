import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_MaximalAbelianSubgroup

set_option linter.style.longLine true
set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0


universe u

variable (F : Type u) [Field F]

open Matrix MatrixGroups Subgroup MulAut MaximalAbelianSubgroup




/- Lemma 2.2: Every finite subgroup of a multiplicative group of a field is cyclic. -/
-- lemma IsCyclic_of_finite_subgroup_units (H : Subgroup Fˣ) [Finite H] : IsCyclic H :=
--   subgroup_units_cyclic H

open SpecialSubgroups


/- Conjugacy of Maximal Abelian subgroups -/
/-
Definition. The set Ci = Clᵢ = {x Aᵢx⁻¹ : x ∈ G} is called the conjugacy class of
A ∈ M.
-/

/- We define the conjugacy class of a maximal abelian subgroup of `G`, `Aᵢ` -/
def Cᵢ {F : Type*} [Field F] (Aᵢ : Subgroup SL(2,F)) := (ConjClasses Aᵢ)

#check Cᵢ

/- The non-central part of a subgroup -/
def Subgroup.noncenter {G : Type*} [Group G] (H : Subgroup G) : Set G := {x : G | x ∈ H.carrier \ center G}


def Cᵢ_noncentral (Aᵢ G : Subgroup SL(2,F)) := { K : Cᵢ Aᵢ // True }


#check noncenter

def noncenter_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F)) :=
  { noncenter K | K ∈ MaximalAbelianSubgroups G }

-- #leansearch "conjugacy class?"

/- Let Aᵢ* be the non-central part of Aᵢ ∈ M -/

#check ConjClasses
#check ConjClasses.noncenter

#check MulAction.card_eq_sum_card_group_div_card_stabilizer

/- let M∗ be the set of all Aᵢ* and let Cᵢ* be the conjugacy class of Aᵢ* .-/
namespace Noncenter

protected def setoid (α : Type*) [Monoid α] : Setoid α where
  r := IsConj
  iseqv := ⟨IsConj.refl, IsConj.symm, IsConj.trans⟩

/-- The quotient type of conjugacy classes of a group. -/
def ConjClasses (α : Type*) [Monoid α] : Type _ :=
  Quotient (Noncenter.setoid α)

/- Define a setoid -/
def SetoidOfMaximalAbelianSubgroup {G : Type*} [Group G] (H : Set G) : Setoid G where
 r := IsConj
 iseqv := {
  refl := fun a => by exact ConjClasses.mk_eq_mk_iff_isConj.mp rfl,
  symm := fun {x y} a ↦ id (IsConj.symm a),
  trans := by exact fun {x y z} a a_1 ↦ IsConj.trans a a_1 }

def ConjClassesOfMaximalAbelianSubgroup {G : Type*} [Group G] (H : Set G) : Type _ :=
  Quotient (Noncenter.SetoidOfMaximalAbelianSubgroup H)


end Noncenter
-- lemma theorem_2_4 {F : Type*} [Field F] {G : Subgroup SL(2,F)} [Finite G]

/-
Clᵢ = {x Aᵢx⁻¹ : x ∈ G}

For some Ai ∈ M and A∗i ∈ M∗ let,
Ci = ⋃ x ∈ G, x * Aᵢ * x⁻¹, and Cᵢ* = ⋃ x ∈ G, x Aᵢ* x⁻¹

It’s evident that Cᵢ* = Cᵢ \ Z(SL(2,F)) and that there is a Cᵢ corresponding to each
Cᵢ . Clearly we have the relation, |Cᵢ*| = |Aᵢ*||Clᵢ*|
-/

#leansearch "finite union?"

-- def C_i {F : Type*} [Field F] (A G : Subgroup SL(2,F)) [Finite G] (hA : A ∈ MaximalAbelianSubgroups G) :=  ⋃ x ∈ G,

-- lemma card_noncentral_conjugacy_eq_mul_noncentral_MaxAbSub


/- Lemma 2.5 N_G(A) = N_G(A*)-/
lemma normalizer_noncentral_eq {F : Type*} [Field F] (A G : Subgroup SL(2,F)) [Finite G] (hA : A ∈ MaximalAbelianSubgroups G) : normalizer A = setNormalizer (noncenter A) := by
  sorry

/- Lemma Let `Q` be a `p`-Sylow subgroup of `G` then $N_G(Q \sqcup Z) = N_G(Q)$-/
lemma normalizer_Sylow_join_center_eq_normalizer_Sylow {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)] [CharP F p] (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) : normalizer (map G.subtype Q.toSubgroup ⊔ center SL(2,F)) = normalizer (map G.subtype Q.toSubgroup) := by
  sorry



#min_imports

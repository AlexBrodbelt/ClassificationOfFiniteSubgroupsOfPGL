import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S3_JordanNormalFormOfSL



set_option autoImplicit false
set_option linter.style.longLine true

open Matrix MatrixGroups Subgroup Pointwise

open SpecialMatrices SpecialSubgroups

universe u


variable
  (F : Type u) [Field F]
  (n : Type u) [Fintype n]
  (R : Type u) [CommRing R]
  {G : Type u} [Group G]



/- Lemma 1.2.2.2 H ⧸ T = D -/
-- def quot_iso_subgroupGeneratedByD {F : Type* } [Field F] :
--   H F ⧸ T F ≃* D F := by sorry -- needs HasQuotient

/- Lemma 1.3. Z(SL(2,F)) = ⟨ -I ⟩ .-/
-- def center_of_SL_2_F : center SL(2,F) ≃* rootsOfUnity 2 F  :=
--   Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' 2



/-
Proposition 1.6.i
N_{SL(2,F)}(S₀) ⊆ L, where S₀ is any subgroup of S with order greater than 1.
-/
lemma normalizer_subgroup_S_le_L [DecidableEq F] { S₀ : Subgroup (SL(2,F)) }
 (hT₀ : 1 < Nat.card S₀ ) (h : S₀ ≤ S F) : normalizer S₀ ≤ L F := by
  intro x hx
  rw [mem_normalizer_iff] at hx
  by_cases h' : ∃ σ, σ ≠ 0 ∧ s σ ∈ S₀
  · obtain ⟨σ, σ_ne_zero, hσ⟩  := h'
    specialize hx (s σ)
    rw [hx] at hσ
    let α := x.1 0 0
    let β := x.1 0 1
    let γ := x.1 1 0
    let δ := x.1 1 1
    have x_eq : x = !![α, β; γ, δ] := by ext <;> rfl
    have : x * s σ * x⁻¹ ∈ S F := by exact h hσ
    obtain ⟨σ' , hσ'⟩ := this
    simp [x_eq] at hσ'
    -- uses decidable equality
    rw [SpecialSubgroups.mem_L_iff_lower_triangular, lower_triangular_iff_top_right_entry_eq_zero]
    have β_eq_zero : s σ' 0 1 = 0 := by simp [s]
    rw [hσ'] at β_eq_zero
    simp [x_eq, s] at β_eq_zero
    ring_nf at β_eq_zero
    rw [neg_eq_zero] at β_eq_zero
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero σ_ne_zero at β_eq_zero
    rw [sq_eq_zero_iff] at β_eq_zero
    simp [x_eq]
    exact β_eq_zero
  · push_neg at h'
    have S₀_eq_bot : S₀ = ⊥ := by
      rw [eq_bot_iff_forall]
      intro x hx
      obtain ⟨σ, rfl⟩ := h hx
      specialize h' σ
      rw [not_imp_not] at h'
      specialize h' hx
      simp [h']
    have : Nat.card S₀ = 1 := by simp [S₀_eq_bot]
    -- contradiction with the assumption that Nat.card S₀ > 1
    linarith

#check mul_normal
/-
Proposition 1.7.
(i) N_L (D₀) = ⟨D, W⟩, where D₀ is any subgroup of D with order greater than 2.
-/
lemma normalizer_subgroup_D_eq_DW { D₀ : Subgroup (SL(2,F)) }
 (hD₀ : 2 < Nat.card D₀ ) (D₀_leq_D : D₀ ≤ D F) : normalizer D₀ ≤ DW F := by
  intro x hx
  rw [mem_normalizer_iff] at hx
  have ⟨δ', h₀, h₁, hδ'⟩ := ex_of_card_D_gt_two hD₀ D₀_leq_D
  specialize hx (d δ')
  rw [hx] at hδ'
  have mem_D := D₀_leq_D hδ'
  rw [mem_D_iff, ← SpecialLinearGroup.fin_two_diagonal_iff] at mem_D
  rcases get_entries x with ⟨α, β, γ, δ, hα, hβ, hγ, hδ, x_eq⟩
  rcases mem_D with ⟨top_right, bottom_left⟩
  simp [d, x_eq] at top_right bottom_left
  ring_nf at top_right bottom_left
  have top_right_eq : -(α * (δ' : F) * β) + α * β * (δ' : F)⁻¹ = α * β * ((↑δ')⁻¹ - ↑δ') := by ring
  have bottom_left_eq : (δ' : F) * γ * δ - (δ' : F)⁻¹ * γ * δ  = γ * δ * (↑δ' - (↑δ')⁻¹) := by ring
  replace top_right := top_right_eq ▸ top_right
  replace bottom_left := bottom_left_eq ▸ bottom_left
  have det_eq_one : det (x : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [SpecialLinearGroup.det_coe]
  have δ_sub_δ_inv_ne_zero : (δ' : F)⁻¹ - δ' ≠ 0 := by
    field_simp
    intro h
    rw [sub_eq_zero, ← sq] at h
    symm at h
    rw [sq_eq_one_iff] at h
    apply not_or_intro h₀ h₁ h
  have δ_inv_neg_δ_ne_zero : (δ') - (δ' : F)⁻¹ ≠ 0 := by
    rw [← neg_ne_zero, neg_sub]; exact δ_sub_δ_inv_ne_zero
  have α_or_β_eq_zero : α * β = 0 :=
    eq_zero_of_ne_zero_of_mul_right_eq_zero δ_sub_δ_inv_ne_zero top_right
  have γ_or_δ_eq_zero : γ * δ = 0 :=
    eq_zero_of_ne_zero_of_mul_right_eq_zero δ_inv_neg_δ_ne_zero bottom_left
  rw [mul_eq_zero] at α_or_β_eq_zero γ_or_δ_eq_zero
  rcases α_or_β_eq_zero with (α_eq_zero | β_eq_zero) <;>
  rcases γ_or_δ_eq_zero with (γ_eq_zero | δ_eq_zero)
  · have det_eq_zero : det (x : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [det_fin_two, ← hα, ← hγ, α_eq_zero, γ_eq_zero, mul_zero, zero_mul, sub_zero]
    rw [det_eq_zero] at det_eq_one
    absurd zero_ne_one det_eq_one
    trivial
  · apply Dw_leq_DW
    rw [mem_D_w_iff, ← SpecialLinearGroup.fin_two_antidiagonal_iff]
    simp_rw [← hα, ← hδ, α_eq_zero, δ_eq_zero]
    trivial
  · apply D_leq_DW
    rw [mem_D_iff, ← SpecialLinearGroup.fin_two_diagonal_iff]
    simp_rw [← hβ, ← hγ, β_eq_zero, γ_eq_zero]
    trivial
  · have det_eq_zero : det (x : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [det_fin_two, ← hβ, ← hδ, β_eq_zero, δ_eq_zero, mul_zero, zero_mul, sub_zero]
    rw [det_eq_zero] at det_eq_one
    absurd zero_ne_one det_eq_one
    trivial

#min_imports

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Fintype.Parity
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Henselian

open Matrix MatrixGroups Subgroup Pointwise

universe u

variable {R F : Type u} [CommRing R] [Field F]

@[ext]
lemma Matrix.fin_two_ext {R : Type*} [CommSemiring R] {M N : Matrix (Fin 2) (Fin 2) R}
  (h₀₀ : M 0 0 = N 0 0)(h₀₁ : M 0 1 = N 0 1)(h₁₀ : M 1 0 = N 1 0)(h₁₁ : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

@[ext]
lemma SpecialLinearGroup.fin_two_ext (A B : SL(2,R))
    (h₀₀ : A.1 0 0 = B.1 0 0) (h₀₁ : A.1 0 1 = B.1 0 1) (h₁₀ : A.1 1 0 = B.1 1 0)
    (h₁₁ : A.1 1 1 = B.1 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

namespace SpecialMatrices

/-
The shear matrix with $\sigma \in F$ as the bottom left entry.
This is $t_\lambda$ in the notes.
-/
def s (σ : F) : SL(2,F) :=
  ⟨!![1, 0; σ, 1], by simp⟩

section Shear

@[simp]
lemma s_zero_eq_one : s (0 : F) = 1 := by ext <;> rfl

lemma s_eq_s_iff (σ μ : F) : s σ = s μ ↔ σ = μ := by
  constructor
  · intro h
    rw [SpecialLinearGroup.fin_two_ext_iff] at h
    obtain ⟨-, -, h, -⟩ := h
    exact h
  · exact fun a ↦ congrArg s a

lemma s_eq_one_iff (σ : F) : s σ = 1 ↔ σ = 0 := by
  exact (@s_zero_eq_one F).symm ▸ s_eq_s_iff σ 0


@[simp]
lemma s_inv (σ : F) : (s σ)⁻¹ = s (-σ) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl, s]; rfl

@[simp]
lemma inv_neg_t_eq (σ : F) : (- s σ)⁻¹ = - s (-σ) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext <;> simp [s]

-- (ii)
@[simp]
lemma s_mul_s_eq_s_add (σ μ : F) : s σ * s μ = s (σ + μ) := by
  ext <;> simp [s]

@[simp]
lemma s_pow_eq_s_mul (σ : F) (n : ℕ) : (s σ)^n = s (n • σ) := by
  induction n
  case zero => simp only [pow_zero, zero_smul, s_zero_eq_one]
  case succ k hk =>
    simp only [pow_add, hk, nsmul_eq_mul, pow_one, s_mul_s_eq_s_add, Nat.cast_add, Nat.cast_one]
    congr
    ring

lemma order_s_eq_char {p : ℕ} [Fact (Nat.Prime p)] [CharP F p]
  (σ : F) (hσ : σ ≠ 0) : orderOf (s σ) = p := by
  refine orderOf_eq_prime ?hg ?hg1
  · simp only [s_pow_eq_s_mul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, s_zero_eq_one]
  · contrapose! hσ
    exact (s_eq_one_iff σ).mp hσ

end Shear

section Diagonal

/-
The diagonal matrix with $\delta \in F^\times$ as the top left entry.
-/
def d (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), 0; 0 , δ⁻¹], by norm_num⟩

@[simp]
lemma inv_d_eq_d_inv (δ : Fˣ) : (d δ)⁻¹ = d (δ⁻¹) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl, d]; rfl

lemma d_eq_inv_d_inv (δ : Fˣ) : d δ = (d δ⁻¹)⁻¹ := by
  rw [inv_d_eq_d_inv, inv_inv]

lemma d_eq_diagonal (δ : Fˣ) :
  (d δ : Matrix (Fin 2) (Fin 2) F) = diagonal (fun i ↦ if i.val = 0 then (δ : F) else δ.inv) := by
  ext <;> simp [d]

@[simp]
lemma d_one_eq_one : d (1 : Fˣ) = 1 := by ext <;> simp [d]

@[simp]
lemma d_neg_one_eq_neg_one : d (-1 : Fˣ) = -1 := by ext <;> simp [d]

@[simp]
lemma neg_d_eq_d_neg (δ : Fˣ) : - d δ = d (-δ) :=  by ext <;> simp [d, inv_neg]

lemma d_coe_eq { δ : Fˣ} : (d (δ : Fˣ) : Matrix (Fin 2) (Fin 2) F) = !![(δ : F), 0; 0, δ⁻¹] := by
  apply Matrix.fin_two_ext
  repeat' simp [d]

lemma d_0_0_is_unit (δ : Fˣ) : IsUnit ((d δ) 0 0) := by simp [d]

-- (i)
@[simp]
lemma d_mul_d_eq_d_mul (δ ρ : Fˣ) : d δ * d ρ = d (δ * ρ) := by
  ext <;> simp [d, mul_comm]

end Diagonal

lemma s_eq_d_iff {δ : Fˣ} {σ : F} : d δ = s σ ↔ δ = 1 ∧ σ = 0 := by
  constructor
  · intro h
    have δ_eq_one : d δ 0 0 = 1 := by simp [h, s]
    simp [d] at δ_eq_one
    have σ_eq_zero : s σ 1 0 = 0 := by simp [← h, d]
    simp [s] at σ_eq_zero
    exact ⟨δ_eq_one, σ_eq_zero⟩
  · rintro ⟨rfl, rfl⟩
    simp

section Rotation

-- Defines the matrix which corresponds to a rotation by `π / 2` radians
def w : SL(2, F) :=
  ⟨!![0,1;-1,0], by norm_num⟩

@[simp]
lemma w_inv {F : Type*} [Field F] :
  (w : SL(2,F))⁻¹  = - w := by ext <;> simp [w]

lemma w_mul_w_eq_neg_one : w * w = (-1 : SL(2, F)) := by ext <;> simp [w]

end Rotation

section Interactions

def ds (δ : Fˣ) (σ : F) : SL(2, F) :=
  ⟨!![δ, 0; σ * δ⁻¹, δ⁻¹], by norm_num⟩

-- Lemma 1.1.iii
lemma d_mul_s_mul_d_inv_eq_s (δ : Fˣ) (σ : F) : d δ * s σ * (d δ)⁻¹ = s (σ * δ⁻¹ * δ⁻¹) := by
  simp; ext <;> simp [s, d, mul_comm]

def dw (δ : Fˣ) : SL(2,F) :=
  ⟨!![0, δ; -δ⁻¹, 0], by norm_num⟩

lemma d_mul_s_eq_ds (δ : Fˣ) (σ : F) : d δ * s σ = ds δ σ := by ext <;> simp [d, s, ds, mul_comm]

lemma d_mul_w_eq_dw (δ : Fˣ) : d δ * w = dw δ := by ext <;> simp [d, w, dw]

@[simp]
lemma inv_of_d_mul_w (δ : Fˣ) : (d δ * w)⁻¹ = d (-δ) * w := by
  simp [mul_inv_rev]
  ext <;> simp [d, w, inv_neg]

-- (iv)
lemma w_mul_d_mul_inv_w_eq_inv_d (δ : Fˣ) : w * (d δ) * w⁻¹ = (d δ)⁻¹ := by
  simp; ext <;> simp [d, w]

@[simp]
lemma w_mul_d_eq_d_inv_w  (δ : Fˣ):  w * (d δ) = (d δ)⁻¹ * w :=  by
  rw [← mul_inv_eq_iff_eq_mul]
  exact w_mul_d_mul_inv_w_eq_inv_d _

@[simp]
lemma neg_d_mul_w (δ : Fˣ) : -(d δ * w) = d (-δ) * w := by rw [← neg_mul, neg_d_eq_d_neg]

end Interactions

end SpecialMatrices

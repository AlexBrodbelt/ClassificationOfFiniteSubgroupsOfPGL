import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option linter.style.longLine true
set_option autoImplicit false
set_option maxHeartbeats 0

universe u v w


open Matrix LinearMap Subgroup

open scoped MatrixGroups

scoped[MatrixGroups] notation "SL"  => Matrix.SpecialLinearGroup

def Matrix.transvection.toSL {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {i j : n} (hij : i ≠ j) (c : R): SL n R :=
  ⟨Matrix.transvection i j c, (det_transvection_of_ne i j hij (c : R))⟩


namespace Matrix.TransvectionStruct

open Matrix

def toSL {n : Type u} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
  (t : TransvectionStruct n R) : SL n R := Matrix.transvection.toSL t.hij t.c

def toGL {n : Type u} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
  (t : TransvectionStruct n R) : GL n R := Matrix.transvection.toSL t.hij t.c

end Matrix.TransvectionStruct

namespace GeneralLinearGroup

def scalar (n : Type*) [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
  (r : Rˣ) : GL n R :=
  Units.map (Matrix.scalar n).toMonoidHom r

/-- The scalar matrix `r • 1` belongs to `GL n R` if and only if `r` is a unit -/
theorem coe_scalar_matrix {n : Type u} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
  (r : Rˣ) : Matrix.scalar n r.val = GeneralLinearGroup.scalar n r := rfl

theorem mem_range_unit_scalar_of_mem_range_scalar_and_mem_general_linear_group
  {n : Type u} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
  {M : GL n R} (hM : (M : Matrix n n R) ∈ Set.range (Matrix.scalar n)) :
    ∃ r : Rˣ, r • 1 = M := by
    obtain ⟨r', hr'⟩ := hM
    have det_scalar : (Matrix.scalar n r').det = r'^(Nat.card n) := by simp
    have det_M_is_unit: IsUnit ((M : Matrix n n R).det) := by simp only [isUnits_det_units]
    rw [← hr', det_scalar] at det_M_is_unit
    cases hn : isEmpty_or_nonempty n
    · exact ⟨1, Subsingleton.elim _ _⟩
    · have n_ne_zero : Nat.card n ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
      have r'_is_unit : IsUnit r' := by
        rw [← isUnit_pow_iff n_ne_zero]
        exact det_M_is_unit
      obtain ⟨r, hr⟩ := r'_is_unit
      use r
      ext
      simp [← hr', ← smul_one_eq_diagonal, ← hr]
      rfl


section Center

open Subgroup GeneralLinearGroup

theorem mem_center_general_linear_group_iff {n : Type u} [DecidableEq n]
  [Fintype n] {R : Type*} [CommRing R] {M : GL n R} :
  M ∈ center (GL n R) ↔ (∃ r : Rˣ, (r • 1) = M) := by
  rw [mem_center_iff]
  refine ⟨?mp, ?mpr⟩
  case mp =>
    intro hM
    -- If M commutes with every matrix then it must commute with the transvection matrices
    have h₀ : ∀ (t : TransvectionStruct n R), Commute (t.toGL) M := fun t => hM t.toGL
    /-
    If M commutes with the transvection matrices,
    then M ∈ Set.range (Matrix.scalar n) where Set.range is Rˣ
    -/
    simp_rw [← Commute.units_val_iff] at h₀
    have h₁ : (M : Matrix n n R) ∈ Set.range ⇑(Matrix.scalar n) :=
      mem_range_scalar_of_commute_transvectionStruct h₀
    obtain ⟨r, rfl⟩ :=
      mem_range_unit_scalar_of_mem_range_scalar_and_mem_general_linear_group h₁
    use r
  case mpr =>
    intro hM N
    obtain ⟨r, rfl⟩ := hM
    ext i j
    simp

end Center

end GeneralLinearGroup

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]


open scoped MatrixGroups

/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup : Type _ :=
    GL n R ⧸ center (GL n R)

/-- `PGL n R` is the projective special linear group `(GL n R)/ Z(GL(n R))`. -/
abbrev PGL := ProjectiveGeneralLinearGroup

/-- A projective special linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveSpecialLinearGroup : Type _ :=
    SpecialLinearGroup n R ⧸ center (SpecialLinearGroup n R)

/-- `PSL(n, R)` is the projective special linear group `SL(n, R)/Z(SL(n, R))`. -/
abbrev PSL := ProjectiveSpecialLinearGroup

section Isomorphism

variable (n : ℕ) (F : Type u) [Field F] [IsAlgClosed F]

open Subgroup

def SL_monoidHom_GL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  SL n R →* GL n R := SpecialLinearGroup.toGL

def SL_monoidHom_PSL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  SL n R →* PSL n R := QuotientGroup.mk' (center (SL n R))

def GL_monoidHom_PGL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  GL n R →* PGL n R := QuotientGroup.mk' (center (GL n R))

def SL_monoidHom_PGL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  SL n R →* PGL n R := (GL_monoidHom_PGL n R).comp (SL_monoidHom_GL n R)

lemma coe {n : Type*}  [Fintype n] [DecidableEq n] (x : SpecialLinearGroup n R):
  SpecialLinearGroup.toGL x = (x : Matrix n n R) := rfl

lemma scalar_eq_smul_one (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] (r : R):
  (scalar n) r = r • 1 := by
  simp [smul_one_eq_diagonal]

lemma center_SL_le_ker (n : Type*) [Fintype n] [DecidableEq n]
  (R : Type*) [CommRing R]:
  center (SpecialLinearGroup n R) ≤ (SL_monoidHom_PGL n R).ker := by
  cases hn : isEmpty_or_nonempty n
  · exact le_of_subsingleton
  · intro x x_mem_center
    rw [SpecialLinearGroup.mem_center_iff] at x_mem_center
    obtain ⟨ω, hω, h⟩ := x_mem_center
    simp [MonoidHom.mem_ker, SL_monoidHom_PGL, GL_monoidHom_PGL, SL_monoidHom_GL]
    rw [GeneralLinearGroup.mem_center_general_linear_group_iff]
    have IsUnit_ω : IsUnit ω := IsUnit.of_pow_eq_one hω Fintype.card_ne_zero
    use IsUnit_ω.unit
    ext
    simp only [coe, ← h, scalar_eq_smul_one]
    rfl

-- By the universal property the map from PSL n F to PGL n F is well defined
def PSL_monoidHom_PGL (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R] :
  PSL n R →* PGL n R :=
  QuotientGroup.lift _ (SL_monoidHom_PGL n R) (center_SL_le_ker n R)

open Polynomial

lemma exists_SL_eq_scaled_GL_of_IsAlgClosed {n F : Type*} [hn₁ : Fintype n] [DecidableEq n]
  [Field F] [IsAlgClosed F] (G : GL n F) :
  ∃ α : Fˣ, ∃ S : SL n F, α • S.toGL = G := by
  cases hn : isEmpty_or_nonempty n
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  let P : F[X] := X^(Nat.card n) - C (det G.val)
  have nat_card_ne_zero : (Nat.card n) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩;
  have deg_P_ne_zero : degree P ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C]
    exact Nat.cast_ne_zero.mpr nat_card_ne_zero
    exact Nat.card_pos
  obtain ⟨α, hα⟩ := @IsAlgClosed.exists_root F _ _ P deg_P_ne_zero
  have c_ne_zero : α ≠ 0 := by
    rintro rfl
    simp [P] at hα
    have det_G_ne_zero : det G.val ≠ 0 := IsUnit.ne_zero <| isUnits_det_units G
    contradiction
  have IsUnit_c : IsUnit α := by exact Ne.isUnit c_ne_zero
  have hα' : ∃ c : Fˣ, c^(Nat.card n) = det G.val := by
    use IsUnit_c.unit
    simp [P, sub_eq_zero] at hα
    simp [hα]
  obtain ⟨α, hα⟩ := hα'
  have det_inv_c_G_eq_one : det (α⁻¹ • G).1 = (1 : F) := by
    simp [← hα, Units.smul_def]
  use α, ⟨(α⁻¹ • G), det_inv_c_G_eq_one⟩
  ext
  simp

open Function

lemma lift_scalar_matrix_eq_one {n F : Type*} [hn₁ : Fintype n] [DecidableEq n]
  [Field F] [IsAlgClosed F] (c : Fˣ) : GL_monoidHom_PGL n F (c • 1)  = 1 := by
  simp [GL_monoidHom_PGL]
  rw [GeneralLinearGroup.mem_center_general_linear_group_iff]
  use c

instance (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R] :
  IsScalarTower Rˣ (GL n R) (GL n R) := by
  refine IsScalarTower.of_smul_one_mul ?_
  intro r g
  ext
  simp


theorem Injective_PSL_monoidHom_PGL  (n F : Type*) [hn₁ : Fintype n] [DecidableEq n]
  [Field F] [IsAlgClosed F] : Injective (PSL_monoidHom_PGL n F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro psl psl_in_ker
  obtain ⟨S, hS⟩ := Quotient.exists_rep psl
  rw [← hS] at psl_in_ker
  simp only [PSL_monoidHom_PGL, SL_monoidHom_PGL, GL_monoidHom_PGL, SL_monoidHom_GL,
    MonoidHom.mem_ker, QuotientGroup.lift_mk, MonoidHom.coe_comp, QuotientGroup.coe_mk',
    Function.comp_apply, QuotientGroup.eq_one_iff] at psl_in_ker
  rw [GeneralLinearGroup.mem_center_general_linear_group_iff] at psl_in_ker
  obtain ⟨ω, hω⟩ := psl_in_ker
  have ω_eq_root_of_unity : det S.val = 1 := SpecialLinearGroup.det_coe S
  simp [GeneralLinearGroup.ext_iff, SpecialLinearGroup.toGL] at hω
  have S_eq_omega_smul_one : (S : Matrix n n F) = ω • 1 := Eq.symm (Matrix.ext hω)
  simp [S_eq_omega_smul_one] at ω_eq_root_of_unity
  simp only [← hS, mem_bot, QuotientGroup.eq_one_iff]
  refine SpecialLinearGroup.mem_center_iff.mpr ?_
  use ω
  refine ⟨?ω_is_root_of_unity, ?S_is_scalar_matrix⟩
  case ω_is_root_of_unity => exact (eq_one_iff_eq_one_of_mul_eq_one ω_eq_root_of_unity).mpr rfl
  case S_is_scalar_matrix => rw [S_eq_omega_smul_one]; exact scalar_eq_smul_one n F ↑ω

theorem SpecialLinearGroup.toGL_inj {n : Type*} [DecidableEq n] [Fintype n] {R : Type*}
  [CommRing R] : Injective (@SpecialLinearGroup.toGL n _ _ R _) := by
  refine (injective_iff_map_eq_one SpecialLinearGroup.toGL).mpr ?_
  intro x hx
  simp [GeneralLinearGroup.ext_iff] at hx
  ext i j
  exact hx i j

theorem ker_SL_monoidHom_PGL_eq_center (n F : Type*) [hn₁ : Fintype n] [DecidableEq n]
  [Field F] [IsAlgClosed F] : (SL_monoidHom_PGL n R).ker = center (SL n R) := by
  dsimp [SL_monoidHom_PGL, GL_monoidHom_PGL, SL_monoidHom_GL]
  rw [← @MonoidHom.comap_ker, QuotientGroup.ker_mk']
  ext x
  constructor
  · intro hx
    simp [mem_center_iff] at hx ⊢
    intro y
    specialize hx y.toGL
    rw [← MonoidHom.map_mul, ← MonoidHom.map_mul] at hx
    apply SpecialLinearGroup.toGL_inj at hx
    exact hx
  · intro hx
    rw [SpecialLinearGroup.mem_center_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    simp [mem_center_iff]
    intro y
    ext i j
    simp [← hr]
    exact CommMonoid.mul_comm (y i j) r

theorem Surjective_PSL_monoidHom_PGL (n F : Type*) [hn₁ : Fintype n] [DecidableEq n]
  [Field F] [IsAlgClosed F] : Surjective (PSL_monoidHom_PGL n F) := by
  intro pgl
  obtain ⟨G, hG⟩ := Quotient.exists_rep pgl
  obtain ⟨c, S, h⟩ := exists_SL_eq_scaled_GL_of_IsAlgClosed G
  use (SL_monoidHom_PSL n F) S
  have class_G_eq_class_S : (⟦G⟧ : PGL n F) = ⟦S.toGL⟧ := by
    rw [Quotient.eq, QuotientGroup.leftRel_apply,
      GeneralLinearGroup.mem_center_general_linear_group_iff]
    use c⁻¹
    suffices c⁻¹ • 1 * G = S by
      simp [← h]
      ext
      simp
    rw [← h, smul_mul_assoc, one_mul, inv_smul_eq_iff]
  rw [← hG, class_G_eq_class_S]
  -- by definition these equivalence classes are the same
  rfl

theorem Bijective_PSL_monoidHom_PGL (n F : Type*) [hn₁ : Fintype n] [DecidableEq n]
  [Field F] [IsAlgClosed F] : Bijective (PSL_monoidHom_PGL n F) := by
  refine ⟨?injective, ?surjective⟩
  case injective => exact Injective_PSL_monoidHom_PGL n F
  case surjective => exact Surjective_PSL_monoidHom_PGL n F

-- We define the isomorphism between
-- the projective general linear group and the projective special linear group
noncomputable def PGL_iso_PSL (n F : Type*) [Fintype n] [DecidableEq n] [Field F]
  [IsAlgClosed F] : PSL n F ≃* PGL n F :=
    MulEquiv.ofBijective (PSL_monoidHom_PGL n F) (Bijective_PSL_monoidHom_PGL n F)

end Isomorphism

import PfaffianDescent.QuarticTwistedCubicAmbientCocycle

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups

universe u
variable {K : Type u} [Field K]

/-- On the chart `x₀ ≠ 0`, the three standard quadratic relations give the
usual affine cubic-Veronese parametrization. -/
theorem standardTwistedCubic_point_eq_scale_cubicVeronese_of_zero_ne
    (x : Fin 4 → K)
    (h1 : x 1 ^ 2 = x 0 * x 2)
    (h2 : x 1 * x 2 = x 0 * x 3)
    (hx0 : x 0 ≠ 0) :
    x = x 0 • cubicVeronese (1 : K) (x 1 / x 0) := by
  have hx2 : x 0 * x 2 = x 1 ^ 2 := h1.symm
  have hx3 : x 3 * x 0 ^ 2 = x 1 ^ 3 := by
    calc
      x 3 * x 0 ^ 2 = (x 0 * x 3) * x 0 := by ring
      _ = (x 1 * x 2) * x 0 := by rw [h2]
      _ = x 1 * (x 0 * x 2) := by ring
      _ = x 1 * x 1 ^ 2 := by rw [hx2]
      _ = x 1 ^ 3 := by ring
  ext i
  fin_cases i
  · simp [cubicVeronese]
  · simp [cubicVeronese]
    field_simp
  · simp [cubicVeronese]
    field_simp
    simpa [mul_comm] using hx2
  · simp [cubicVeronese]
    field_simp
    exact hx3

/-- On the chart `x₃ ≠ 0`, the three standard quadratic relations give the
other affine cubic-Veronese parametrization. -/
theorem standardTwistedCubic_point_eq_scale_cubicVeronese_of_three_ne
    (x : Fin 4 → K)
    (h2 : x 1 * x 2 = x 0 * x 3)
    (h3 : x 2 ^ 2 = x 1 * x 3)
    (hx3 : x 3 ≠ 0) :
    x = x 3 • cubicVeronese (x 2 / x 3) (1 : K) := by
  have hx1 : x 1 * x 3 = x 2 ^ 2 := h3.symm
  have hx0 : x 0 * x 3 ^ 2 = x 2 ^ 3 := by
    calc
      x 0 * x 3 ^ 2 = (x 0 * x 3) * x 3 := by ring
      _ = (x 1 * x 2) * x 3 := by rw [h2]
      _ = x 2 * (x 1 * x 3) := by ring
      _ = x 2 * x 2 ^ 2 := by rw [hx1]
      _ = x 2 ^ 3 := by ring
  ext i
  fin_cases i
  · simp [cubicVeronese]
    field_simp
    exact hx0
  · simp [cubicVeronese]
    field_simp
    exact hx1
  · simp [cubicVeronese]
    field_simp
  · simp [cubicVeronese]

/-- Every nonzero field-valued point of the three standard quadrics is a
nonzero scalar multiple of a cubic-Veronese point. -/
theorem exists_scale_cubicVeronese_of_standardTwistedCubic_relations
    (x : Fin 4 → K)
    (h1 : x 1 ^ 2 = x 0 * x 2)
    (h2 : x 1 * x 2 = x 0 * x 3)
    (h3 : x 2 ^ 2 = x 1 * x 3)
    (hx : x ≠ 0) :
    ∃ r s t : K, r ≠ 0 ∧ (s ≠ 0 ∨ t ≠ 0) ∧ x = r • cubicVeronese s t := by
  by_cases hx0 : x 0 = 0
  · have hx1 : x 1 = 0 := by
      apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
      rw [h1, hx0, zero_mul]
    have hx2 : x 2 = 0 := by
      apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
      rw [h3, hx1, zero_mul]
    have hx3 : x 3 ≠ 0 := by
      intro h
      apply hx
      funext i
      fin_cases i <;> simp [hx0, hx1, hx2, h]
    refine ⟨x 3, x 2 / x 3, 1, hx3, Or.inr one_ne_zero, ?_⟩
    exact standardTwistedCubic_point_eq_scale_cubicVeronese_of_three_ne x h2 h3 hx3
  · refine ⟨x 0, 1, x 1 / x 0, hx0, Or.inl one_ne_zero, ?_⟩
    exact standardTwistedCubic_point_eq_scale_cubicVeronese_of_zero_ne x h1 h2 hx0

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups

universe u
variable {K : Type u} [Field K]

/-- Every cubic-Veronese point annihilates the standard twisted-cubic ideal. -/
theorem standardTwistedCubicIdeal_eval_cubicVeronese
    (s t : K) (p : MvPolynomial (Fin 4) K)
    (hp : p ∈ standardTwistedCubicIdeal K) :
    MvPolynomial.aeval (cubicVeronese s t) p = 0 := by
  rw [standardTwistedCubicIdeal_eq_ker] at hp
  rw [← standardTwistedCubicParam_eval]
  change standardTwistedCubicParam K p = 0 at hp
  rw [hp, map_zero]

/-- A linear coordinate change preserving the standard ideal sends each
cubic-Veronese point to a point satisfying the three standard relations. -/
theorem linearSubstitution_preserving_standardTwistedCubic_relations
    (B : Matrix (Fin 4) (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map (linearSubstitution B).toRingHom =
      standardTwistedCubicIdeal K)
    (s t : K) :
    ((B.mulVec (cubicVeronese s t)) 1) ^ 2 =
        (B.mulVec (cubicVeronese s t)) 0 * (B.mulVec (cubicVeronese s t)) 2 ∧
      (B.mulVec (cubicVeronese s t)) 1 * (B.mulVec (cubicVeronese s t)) 2 =
        (B.mulVec (cubicVeronese s t)) 0 * (B.mulVec (cubicVeronese s t)) 3 ∧
      ((B.mulVec (cubicVeronese s t)) 2) ^ 2 =
        (B.mulVec (cubicVeronese s t)) 1 * (B.mulVec (cubicVeronese s t)) 3 := by
  have hpoint (p : MvPolynomial (Fin 4) K) (hp : p ∈ standardTwistedCubicIdeal K) :
      MvPolynomial.aeval (B.mulVec (cubicVeronese s t)) p = 0 := by
    rw [← linearSubstitution_eval]
    apply standardTwistedCubicIdeal_eval_cubicVeronese
    rw [← hB]
    exact Ideal.mem_map_of_mem _ hp
  have h0 := hpoint (standardTwistedCubicGenerators K 0)
    (Ideal.subset_span (Set.mem_range_self 0))
  have h1 := hpoint (standardTwistedCubicGenerators K 1)
    (Ideal.subset_span (Set.mem_range_self 1))
  have h2 := hpoint (standardTwistedCubicGenerators K 2)
    (Ideal.subset_span (Set.mem_range_self 2))
  constructor
  · exact sub_eq_zero.mp (by simpa [standardTwistedCubicGenerators] using h0)
  constructor
  · exact sub_eq_zero.mp (by simpa [standardTwistedCubicGenerators] using h1)
  · exact sub_eq_zero.mp (by simpa [standardTwistedCubicGenerators] using h2)

/-- A standard-ideal-preserving invertible matrix sends every nonzero binary
parameter to another cubic-Veronese point, projectively. -/
theorem exists_scale_cubicVeronese_linearImage_of_standardTwistedCubic
    (B : GL (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map
      (linearSubstitution (B : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K)
    (s t : K) (hst : s ≠ 0 ∨ t ≠ 0) :
    ∃ r u v : K, r ≠ 0 ∧ (u ≠ 0 ∨ v ≠ 0) ∧
      (B : Matrix (Fin 4) (Fin 4) K).mulVec (cubicVeronese s t) = r • cubicVeronese u v := by
  let x := (B : Matrix (Fin 4) (Fin 4) K).mulVec (cubicVeronese s t)
  have hrel := linearSubstitution_preserving_standardTwistedCubic_relations
    (B : Matrix (Fin 4) (Fin 4) K) hB s t
  have hx : x ≠ 0 := by
    intro hx0
    apply cubicVeronese_nonzero s t hst
    have hBunit : IsUnit (B : Matrix (Fin 4) (Fin 4) K) := by
      exact B.isUnit
    have hinj : Function.Injective (B : Matrix (Fin 4) (Fin 4) K).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hBunit
    exact hinj (by simpa [x] using hx0)
  exact exists_scale_cubicVeronese_of_standardTwistedCubic_relations x
    hrel.1 hrel.2.1 hrel.2.2 hx

end PfaffianDescent.QuarticNet

import AllCharacteristics.ProjectiveOverlapLifting
import AllCharacteristics.ProjectiveEquationParameters
import AllCharacteristics.ProjectiveTripleOverlap

/-!
# Independence of the distinguished equation coefficient

A field equation with two nonzero coefficients defines a point of their actual
coefficient overlap. Its restrictions are precisely the two normalized chart
parameters, so the resulting projective classifying morphisms are equal.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R k : Type u} [CommRing R] [Field k] {σ : Type} {d : ℕ}
variable (b : R →+* k) (p : MvPolynomial σ k)
variable (i j : Monomials σ d) (hi : p.coeff i.1 ≠ 0) (hj : p.coeff j.1 ≠ 0)
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => ParameterIdeal R σ d

/-- An overlap lift of one normalized equation parameter restricts to the
other normalized equation parameter on its other side. -/
theorem equationOverlapHom_comp_right (ψ : ChartOverlapRing I₀ i j →+* k)
    (hψ : ψ.comp (chartOverlapLeftMap I₀ i j) = projectiveEquationChartMap b p i hi) :
    ψ.comp (chartOverlapRightMap I₀ i j) = projectiveEquationChartMap b p j hj := by
  apply projectiveChartMap_ext j
  · apply RingHom.ext
    intro r
    change ψ (chartOverlapRightMap I₀ i j (chartBaseMap I₀ j r)) =
      projectiveEquationChartMap b p j hj (chartBaseMap I₀ j r)
    rw [chartOverlapRightMap_baseMap, ← chartOverlapLeftMap_baseMap I₀ i j r]
    change (ψ.comp (chartOverlapLeftMap I₀ i j)) (chartBaseMap I₀ i r) = _
    rw [hψ, projectiveEquationChartMap_baseMap, projectiveEquationChartMap_baseMap]
  · intro m
    have he := congrArg ψ (chartOverlap_coordinate_relation I₀ i j m)
    rw [chartOverlapUnit_inv, map_mul] at he
    change (ψ.comp (chartOverlapLeftMap I₀ i j)) (chartCoordinate I₀ i m) =
      (ψ.comp (chartOverlapLeftMap I₀ i j)) (chartCoordinate I₀ i j) *
        (ψ.comp (chartOverlapRightMap I₀ i j)) (chartCoordinate I₀ j m) at he
    rw [hψ, projectiveEquationChartMap_coordinate, projectiveEquationChartMap_coordinate] at he
    rw [projectiveEquationChartMap_coordinate]
    apply mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hi) hj)
    calc
      _ = (p.coeff i.1)⁻¹ * p.coeff m.1 := he.symm
      _ = ((p.coeff i.1)⁻¹ * p.coeff j.1) * ((p.coeff j.1)⁻¹ * p.coeff m.1) := by
        rw [mul_assoc, ← mul_assoc (p.coeff j.1), mul_inv_cancel₀ hj, one_mul]

/-- The equation defines a point of the actual overlap with both prescribed normalized restrictions. -/
theorem exists_equationOverlapHom :
    ∃ ψ : ChartOverlapRing I₀ i j →+* k,
      ψ.comp (chartOverlapLeftMap I₀ i j) = projectiveEquationChartMap b p i hi ∧
      ψ.comp (chartOverlapRightMap I₀ i j) = projectiveEquationChartMap b p j hj := by
  have hu : IsUnit (projectiveEquationChartMap b p i hi (chartCoordinate I₀ i j)) := by
    rw [projectiveEquationChartMap_coordinate]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero hi) hj)
  obtain ⟨ψ, hψ⟩ := exists_chartOverlap_hom I₀ i j (projectiveEquationChartMap b p i hi) hu
  exact ⟨ψ, hψ, equationOverlapHom_comp_right b p i j hi hj ψ hψ⟩

/-- The equation's projective classifying morphism is independent of its chosen nonzero coefficient. -/
theorem projectiveEquationParameter_independent :
    projectiveEquationParameter b p i hi = projectiveEquationParameter b p j hj := by
  obtain ⟨ψ, hleft, hright⟩ := exists_equationOverlapHom b p i j hi hj
  change Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p i hi)) ≫ chartι I₀ i =
    Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj)) ≫ chartι I₀ j
  rw [← hleft, ← hright, specMap_ringHom_comp, specMap_ringHom_comp,
    Category.assoc, Category.assoc, chartOverlapLeftMap_toProj, chartOverlapRightMap_toProj]

end UniversalHomogeneous
end AllCharacteristics

import AllCharacteristics.ProjectiveClassifyingMap

/-!
# Classifying morphisms under field extension

Normalized coefficient parameters and the coefficient-independent global
classifying morphism commute with every field homomorphism, including
inseparable extensions.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R k L : Type u} [CommRing R] [Field k] [Field L] {σ : Type} {d : ℕ}
variable (b : R →+* k) (α : k →+* L) (p : MvPolynomial σ k)
variable (j : Monomials σ d) (hj : p.coeff j.1 ≠ 0)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Normalized coefficient-chart maps commute with a field homomorphism. -/
theorem projectiveEquationChartMap_fieldChange (hαj : (p.map α).coeff j.1 ≠ 0) :
    α.comp (projectiveEquationChartMap b p j hj) =
      projectiveEquationChartMap (α.comp b) (p.map α) j hαj := by
  apply projectiveChartMap_ext j
  · apply RingHom.ext
    intro r
    change α (projectiveEquationChartMap b p j hj (chartBaseMap (ParameterIdeal R σ d) j r)) = _
    rw [projectiveEquationChartMap_baseMap]
    exact (projectiveEquationChartMap_baseMap (α.comp b) (p.map α) j hαj r).symm
  · intro m
    change α (projectiveEquationChartMap b p j hj (chartCoordinate (ParameterIdeal R σ d) j m)) = _
    rw [projectiveEquationChartMap_coordinate, projectiveEquationChartMap_coordinate,
      map_mul, map_inv₀, coeff_map, coeff_map]

/-- The projective equation parameter commutes with every field homomorphism. -/
theorem projectiveEquationParameter_fieldChange (hαj : (p.map α).coeff j.1 ≠ 0) :
    Spec.map (CommRingCat.ofHom α) ≫ projectiveEquationParameter b p j hj =
      projectiveEquationParameter (α.comp b) (p.map α) j hαj := by
  unfold projectiveEquationParameter
  rw [← Category.assoc, ← specMap_ringHom_comp, projectiveEquationChartMap_fieldChange b α p j hj hαj]

/-- The coefficient-independent classifying map is natural under arbitrary
field extension, without a separability hypothesis. -/
theorem projectiveClassifyingMap_fieldChange (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    (hαne : p.map α ≠ 0) :
    Spec.map (CommRingCat.ofHom α) ≫ projectiveClassifyingMap p hp hne b =
      projectiveClassifyingMap (p.map α) (hp.map α) hαne (α.comp b) := by
  let i := chosenEquationCoefficient p hp hne
  have hi : p.coeff i.1 ≠ 0 := chosenEquationCoefficient_ne_zero p hp hne
  have hαi : (p.map α).coeff i.1 ≠ 0 := by
    rw [coeff_map, map_ne_zero]
    exact hi
  rw [projectiveClassifyingMap_eq_chart p hp hne b i hi,
    projectiveClassifyingMap_eq_chart (p.map α) (hp.map α) hαne (α.comp b) i hαi]
  exact projectiveEquationParameter_fieldChange b α p i hi hαi

end UniversalHomogeneous
end AllCharacteristics

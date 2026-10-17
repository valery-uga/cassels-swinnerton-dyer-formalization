import AllCharacteristics.HomogeneousProjectiveAmbient

/-! Ambient coordinate charts of arbitrary homogeneous projective quotients. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ambient coordinate-chart map of an arbitrary homogeneous quotient. -/
noncomputable def quotientAmbientChartMap
    {R : Type u} {σ : Type} [CommRing R]
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (j : σ) :
    Away (homogeneousSubmodule σ R) (X j) →+* ChartRing I j :=
  gradedAwayMapOfEq (quotientGradedRingHom I)
    (X j) (coordinate I j) (quotientGradedRingHom_coordinate I j)

/-- The ambient chart map preserves each normalized homogeneous coordinate. -/
theorem quotientAmbientChartMap_coordinate
    {R : Type u} {σ : Type} [CommRing R]
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (j i : σ) :
    quotientAmbientChartMap I j
      (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule σ R) (isHomogeneous_X R j)
        (X i) (isHomogeneous_X R i)) =
      chartCoordinate I j i := by
  let 𝒜 := homogeneousSubmodule σ R
  let hxj : X j ∈ 𝒜 1 := isHomogeneous_X R j
  let hxi : X i ∈ 𝒜 1 := isHomogeneous_X R i
  let hyj : coordinate I j ∈ grading I 1 := coordinate_mem I j
  let hyi : coordinate I i ∈ grading I 1 := coordinate_mem I i
  unfold quotientAmbientChartMap chartCoordinate
    AllCharacteristics.GradedChart.normalized
  change (gradedAwayMapOfEq (quotientGradedRingHom I)
    (X j) (coordinate I j) (quotientGradedRingHom_coordinate I j))
      (Away.mk 𝒜 hxj 1 (X i) (by simpa only [one_smul] using hxi)) =
    Away.mk (grading I) hyj 1 (coordinate I i)
      (by simpa only [one_smul] using hyi)
  rw [gradedAwayMapOfEq_mk (quotientGradedRingHom I)
    (X j) (coordinate I j) (quotientGradedRingHom_coordinate I j)
    hxj hyj 1 (X i) hxi]
  cases quotientGradedRingHom_coordinate I i
  rfl

/-- The quotient immersion restricted to a coordinate chart is represented
by the corresponding quotient map on homogeneous-localization rings. -/
theorem chartι_comp_quotientProjMap
    {R : Type u} {σ : Type} [CommRing R]
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (j : σ) :
    chartι I j ≫ quotientProjMap I =
      Spec.map (CommRingCat.ofHom (quotientAmbientChartMap I j)) ≫
        Proj.awayι (homogeneousSubmodule σ R) (X j)
          (isHomogeneous_X R j) (by decide : 0 < 1) := by
  change Proj.awayι (grading I) (coordinate I j) (coordinate_mem I j)
      (by decide : 0 < 1) ≫
        Proj.map (quotientGradedRingHom I)
          (irrelevant_le_map_quotientGradedRingHom I) = _
  exact awayι_comp_map_of_eq (quotientGradedRingHom I)
    (irrelevant_le_map_quotientGradedRingHom I)
    (X j) (coordinate I j)
    (quotientGradedRingHom_coordinate I j)
    (by decide : 0 < 1) (isHomogeneous_X R j) (coordinate_mem I j)

end PfaffianDescent

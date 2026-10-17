import PfaffianDescent.VoisinQuotientNormalizedAmbientChart

/-! Nonvanishing coordinates detected by projective basic opens. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If a normalized point lies in the projective coordinate basic open,
the corresponding evaluated homogeneous coordinate is nonzero. -/
theorem normalizedPointAt_coordinate_ne_zero_of_mem_basicOpen
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (y : Fin 4 → F) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K F) y = 0)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) y) he)
        (Ideal.Quotient.mk I.toIdeal ell) = 1)
    (j : Fin 4)
    (hopen : (linearNormalizedPointAt I y he
      (Ideal.Quotient.mk I.toIdeal ell)
      (polynomial_class_mem_grading I ell hell) hzOne)
        (IsLocalRing.closedPoint F) ∈
      Proj.basicOpen (grading I) (coordinate I j)) : y j ≠ 0 := by
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal ell
  let hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  let g := linearNormalizedPointChartMapAt I y he z hz hzOne
  have hspec : (Spec.map (CommRingCat.ofHom g))
      (IsLocalRing.closedPoint F) ∈
      (Proj.awayι (grading I) z hz (by decide : 0 < 1)) ⁻¹ᵁ
        Proj.basicOpen (grading I) (coordinate I j) := by
    exact hopen
  rw [Proj.awayι_preimage_basicOpen
    (g_deg := coordinate_mem I j) (hm' := (by decide : 0 < 1))] at hspec
  have hnonmem := (PrimeSpectrum.mem_basicOpen _ _).mp hspec
  have hne : g (Away.isLocalizationElem hz (coordinate_mem I j)) ≠ 0 := by
    intro hzero
    apply hnonmem
    change g (Away.isLocalizationElem hz (coordinate_mem I j)) ∈
      (IsLocalRing.closedPoint F).asIdeal
    simpa [hzero]
  have hcoordinate :
      Away.isLocalizationElem hz (coordinate_mem I j) =
        linearChartCoordinate I z hz j := by
    simp [Away.isLocalizationElem, linearChartCoordinate,
      AllCharacteristics.GradedChart.normalized]
  rw [hcoordinate, linearNormalizedPointChartMapAt_coordinate] at hne
  exact hne

/-- The same nonvanishing test after applying the quotient immersion into
ordinary ambient projective space. -/
theorem normalizedPointAt_coordinate_ne_zero_of_ambient_basicOpen
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (y : Fin 4 → F) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K F) y = 0)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) y) he)
        (Ideal.Quotient.mk I.toIdeal ell) = 1)
    (j : Fin 4)
    (hopen : ((linearNormalizedPointAt I y he
      (Ideal.Quotient.mk I.toIdeal ell)
      (polynomial_class_mem_grading I ell hell) hzOne) ≫
        quotientProjMap I) (IsLocalRing.closedPoint F) ∈
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X j)) : y j ≠ 0 := by
  apply normalizedPointAt_coordinate_ne_zero_of_mem_basicOpen
    I y ell hell he hzOne j
  change (linearNormalizedPointAt I y he
      (Ideal.Quotient.mk I.toIdeal ell)
      (polynomial_class_mem_grading I ell hell) hzOne)
        (IsLocalRing.closedPoint F) ∈
    quotientProjMap I ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X j) at hopen
  change (linearNormalizedPointAt I y he
      (Ideal.Quotient.mk I.toIdeal ell)
      (polynomial_class_mem_grading I ell hell) hzOne)
        (IsLocalRing.closedPoint F) ∈
    Proj.map (quotientGradedRingHom I)
      (irrelevant_le_map_quotientGradedRingHom I) ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X j) at hopen
  rw [Proj.map_preimage_basicOpen, quotientGradedRingHom_coordinate] at hopen
  exact hopen

end PfaffianDescent

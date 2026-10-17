import PfaffianDescent.VoisinSelectedAmbientChartTransfer
import PfaffianDescent.VoisinQuotientNormalizedAmbientChart
import PfaffianDescent.VoisinNormalizedPointChartNonzero

/-! Ratios of selected and canonical vectors from their common point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If the selected and canonical normalized vectors define the same
original ambient point and one common coordinate is nonzero, their
coordinate ratios in that chart are identical across the field change. -/
theorem selectedCanonical_normalizedCoordinateRatios_eq
    {K Q F : Type u} [Field K] [Field Q] [Field F]
    [Algebra K F] [Algebra Q F]
    (f : K →+* Q)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → F) (ellx : MvPolynomial (Fin 4) K)
    (hellx : ellx.IsHomogeneous 1)
    (hex : ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K F) x = 0)
    (hxOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K F) x) hex)
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ellx) = 1)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
    (y : Fin 4 → F) (elly : MvPolynomial (Fin 4) Q)
    (helly : elly.IsHomogeneous 1)
    (hey : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap Q F) y = 0)
    (hyOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap Q F) y) hey)
        (Ideal.Quotient.mk I.toIdeal elly) = 1)
    (hpoint :
      (linearNormalizedPointAt I y hey
        (Ideal.Quotient.mk I.toIdeal elly)
        (polynomial_class_mem_grading I elly helly) hyOne ≫
          quotientProjMap I) ≫ ambientCoefficientMap f =
      linearNormalizedPointAt (equationIdeal p hp) x hex
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ellx)
        (polynomial_class_mem_grading (equationIdeal p hp) ellx hellx)
        hxOne ≫ hypersurfaceToAmbient p hp)
    (j : Fin 4) (hxj : x j ≠ 0) :
    ∀ i : Fin 4, (y j)⁻¹ * y i = (x j)⁻¹ * x i := by
  let qQ := linearNormalizedPointAt I y hey
    (Ideal.Quotient.mk I.toIdeal elly)
    (polynomial_class_mem_grading I elly helly) hyOne ≫
      quotientProjMap I
  obtain ⟨gX, hgX, hXcoord⟩ :=
    exists_changedAmbientChart_with_selectedRatios
      f p hp x ellx hellx hex hxOne qQ hpoint j hxj
  have hraw : qQ (IsLocalRing.closedPoint F) ∈ Set.range
      (Proj.awayι (homogeneousSubmodule (Fin 4) Q) (X j)
        (isHomogeneous_X Q j) (by decide : 0 < 1)) := by
    rw [← hgX]
    exact ⟨(Spec.map (CommRingCat.ofHom gX))
      (IsLocalRing.closedPoint F), rfl⟩
  have hopen : qQ (IsLocalRing.closedPoint F) ∈
      Proj.basicOpen (homogeneousSubmodule (Fin 4) Q) (X j) := by
    exact (Proj.opensRange_awayι (homogeneousSubmodule (Fin 4) Q)
      (X j) (isHomogeneous_X Q j) (by decide : 0 < 1)) ▸ hraw
  have hyj : y j ≠ 0 :=
    normalizedPointAt_coordinate_ne_zero_of_ambient_basicOpen
      I y elly helly hey hyOne j hopen
  obtain ⟨gY, hgY, hYcoord⟩ :=
    exists_ambientCoordinateChart_of_quotientNormalizedPointAt
      I y elly helly hey hyOne j hyj
  have hcharts : gX = gY :=
    ambientCoefficientChartMap_eq_of_projective_eq j gX gY
      (hgX.trans hgY.symm)
  intro i
  calc
    (y j)⁻¹ * y i = gY (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) Q) (isHomogeneous_X Q j)
        (X i) (isHomogeneous_X Q i)) := (hYcoord i).symm
    _ = gX (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) Q) (isHomogeneous_X Q j)
        (X i) (isHomogeneous_X Q i)) := by rw [hcharts]
    _ = (x j)⁻¹ * x i := hXcoord i

end PfaffianDescent

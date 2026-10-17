import PfaffianDescent.VoisinNormalizedAmbientCoordinateChart
import PfaffianDescent.VoisinAmbientChartCoefficientComparison

/-! Transfer a selected normalized hypersurface chart across coefficients. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If a point over a changed coefficient field has the ambient image of a
selected normalized hypersurface vector, then it has the same nonvanishing
coordinate chart, with chart values equal to the selected vector's ratios. -/
theorem exists_changedAmbientChart_with_selectedRatios
    {K Q F : Type u} [Field K] [Field Q] [Field F]
    [Algebra K F]
    (f : K →+* Q)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → F) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (he : ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K F) x = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K F) x) he)
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) = 1)
    (qQ : Spec (.of F) ⟶ Proj (homogeneousSubmodule (Fin 4) Q))
    (hpoint : qQ ≫ ambientCoefficientMap f =
      linearNormalizedPointAt (equationIdeal p hp) x he
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
        (polynomial_class_mem_grading (equationIdeal p hp) ell hell)
        hzOne ≫ hypersurfaceToAmbient p hp)
    (j : Fin 4) (hxj : x j ≠ 0) :
    ∃ gQ : Away (homogeneousSubmodule (Fin 4) Q) (X j) →+* F,
      (Spec.map (CommRingCat.ofHom gQ) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) Q) (X j)
          (isHomogeneous_X Q j) (by decide : 0 < 1) = qQ) ∧
      ∀ i : Fin 4,
        gQ (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) Q) (isHomogeneous_X Q j)
          (X i) (isHomogeneous_X Q i)) = (x j)⁻¹ * x i := by
  obtain ⟨gK, hgK, hcoordK⟩ :=
    exists_ambientCoordinateChart_of_linearNormalizedPointAt
      p hp x ell hell he hzOne j hxj
  have hchanged : qQ ≫ ambientCoefficientMap f =
      Spec.map (CommRingCat.ofHom gK) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1) :=
    hpoint.trans hgK.symm
  obtain ⟨gQ, hgQ, hmap⟩ :=
    exists_ambientChartMap_of_coefficientChangedPoint_eq
      f j qQ gK hchanged
  refine ⟨gQ, hgQ, ?_⟩
  intro i
  calc
    gQ (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) Q) (isHomogeneous_X Q j)
        (X i) (isHomogeneous_X Q i)) =
      (gQ.comp (ambientCoefficientChartMap f j))
        (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
          (X i) (isHomogeneous_X K i)) := by
            rw [RingHom.comp_apply, ambientCoefficientChartMap_coordinate]
    _ = (x j)⁻¹ * x i := by rw [hmap, hcoordK]

end PfaffianDescent

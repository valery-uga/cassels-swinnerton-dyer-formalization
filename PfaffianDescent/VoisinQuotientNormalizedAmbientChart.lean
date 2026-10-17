import PfaffianDescent.VoisinQuotientAmbientChart
import PfaffianDescent.VoisinNormalizedPointAtCompatibility

/-! Ambient chart ratios of points normalized in a homogeneous quotient. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A normalized vector in an arbitrary homogeneous quotient, when one
coordinate is nonzero, has an ordinary ambient-chart presentation whose
coordinate functions are exactly the corresponding vector ratios. -/
theorem exists_ambientCoordinateChart_of_quotientNormalizedPointAt
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → F) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K F) x = 0)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) x) he)
        (Ideal.Quotient.mk I.toIdeal ell) = 1)
    (j : Fin 4) (hxj : x j ≠ 0) :
    ∃ g : Away (homogeneousSubmodule (Fin 4) K) (X j) →+* F,
      (Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1) =
        linearNormalizedPointAt I x he
          (Ideal.Quotient.mk I.toIdeal ell)
          (polynomial_class_mem_grading I ell hell) hzOne ≫
          quotientProjMap I) ∧
      ∀ i : Fin 4,
        g (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
          (X i) (isHomogeneous_X K i)) = (x j)⁻¹ * x i := by
  let u : Fˣ := Units.mk0 (x j) hxj
  obtain ⟨gI, hcoord, hpoint⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint
      I x ell hell hzOne he j u rfl
  let g := gI.comp (quotientAmbientChartMap I j)
  refine ⟨g, ?_, ?_⟩
  · calc
      Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
            (isHomogeneous_X K j) (by decide : 0 < 1) =
        (Spec.map (CommRingCat.ofHom gI) ≫
          Spec.map (CommRingCat.ofHom (quotientAmbientChartMap I j))) ≫
          Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
            (isHomogeneous_X K j) (by decide : 0 < 1) := by
              rw [← Spec.map_comp]
              rfl
      _ = (Spec.map (CommRingCat.ofHom gI) ≫ chartι I j) ≫
          quotientProjMap I := by
            calc
              _ = Spec.map (CommRingCat.ofHom gI) ≫
                  (Spec.map (CommRingCat.ofHom
                    (quotientAmbientChartMap I j)) ≫
                    Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
                      (isHomogeneous_X K j) (by decide : 0 < 1)) := by
                        rw [Category.assoc]
              _ = Spec.map (CommRingCat.ofHom gI) ≫
                  (chartι I j ≫ quotientProjMap I) := by
                    rw [chartι_comp_quotientProjMap]
              _ = _ := (Category.assoc _ _ _).symm
      _ = _ := by
        rw [hpoint, linearNormalizedPointAt_mk_eq_linearNormalizedPoint]
  · intro i
    change gI (quotientAmbientChartMap I j
      (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
        (X i) (isHomogeneous_X K i))) = _
    rw [quotientAmbientChartMap_coordinate, hcoord]
    simp [u]

end PfaffianDescent

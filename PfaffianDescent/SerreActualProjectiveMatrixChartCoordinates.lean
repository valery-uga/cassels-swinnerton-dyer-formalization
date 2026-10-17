import PfaffianDescent.SerreActualProjectiveMatrixNormalizedChart

/-! The actual projective matrix map changes normalized regular coordinate
functions by the same matrix on its genuine affine chart. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem projectiveMatrixGradingMap_coordinate
    {K : Type u} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    projectiveMatrixGradingMap M
        (coordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) =
      Ideal.Quotient.mk
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)).toIdeal
        (rectangularLinearCoordinate M i) := by
  change Ideal.Quotient.mk _ (rectangularSubstitution M (X i)) = _
  rw [rectangularSubstitution_X]

theorem projectiveMatrixChart_normalized_coordinates
    {K : Type u} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (i : Fin n) :
    (Away.map (projectiveMatrixGradingMap M) z)
        (linearChartCoordinate
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) z hz i) =
      ((M.map (AllCharacteristics.GradedChart.baseMap
          (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          (z := projectiveMatrixGradingMap M z))).mulVec
        (linearChartCoordinate
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
          (projectiveMatrixGradingMap M z) ((projectiveMatrixGradingMap M).map_mem hz))) i := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  let F := projectiveMatrixGradingMap M
  have hmap := awayMap_polynomialProjectiveMap_normalized I I
    (rectangularSubstitution M) bot_le
    (fun _ _ hp => rectangularSubstitution_homogeneous M hp)
    z (coordinate I i) hz (coordinate_mem I i)
  have heval := eval₂_linearChartCoordinate_eq_fraction I (F z) (F.map_mem hz)
    (rectangularLinearCoordinate M i) (rectangularLinearCoordinate_homogeneous M i)
  have hnorm :
      AllCharacteristics.GradedChart.normalized (grading I) (F.map_mem hz)
        (F (coordinate I i)) (F.map_mem (coordinate_mem I i)) =
      Away.mk (grading I) (F.map_mem hz) 1
        (Ideal.Quotient.mk I.toIdeal (rectangularLinearCoordinate M i))
        (polynomial_class_mem_grading I (rectangularLinearCoordinate M i)
          (rectangularLinearCoordinate_homogeneous M i)) := by
    apply val_injective
    simp only [AllCharacteristics.GradedChart.normalized, Away.val_mk, pow_one]
    exact congrArg
      (fun a => (Localization.mk a ⟨F z, Submonoid.mem_powers (F z)⟩ :
        Localization (.powers (F z)))) (projectiveMatrixGradingMap_coordinate M i)
  exact hmap.trans (hnorm.trans (heval.symm.trans
    (eval₂_rectangularLinearCoordinate M i
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := F z))
      (linearChartCoordinate I (F z) (F.map_mem hz)))))

end PfaffianDescent

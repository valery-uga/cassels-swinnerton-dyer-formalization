import PfaffianDescent.SerreActualProjectiveMatrixEvaluation

/-! Matrix changes of homogeneous coordinates commute with the actual
normalized affine chart maps, including their coefficient maps. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem projectiveMatrixNormalizedChartMap_comp
    {K L : Type u} [Field K] [CommRing L] [Algebra K L] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (x : Fin n → L)
    (z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (hOneX : projectiveMatrixVectorEvaluation x (projectiveMatrixGradingMap M z) = 1)
    (hOneY : projectiveMatrixVectorEvaluation ((M.map (algebraMap K L)).mulVec x) z = 1) :
    (linearNormalizedPointChartMapAt
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) x
      (projectiveMatrixVectorEquations x) (projectiveMatrixGradingMap M z)
      ((projectiveMatrixGradingMap M).map_mem hz) hOneX).comp
        (Away.map (projectiveMatrixGradingMap M) z) =
      linearNormalizedPointChartMapAt
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
        ((M.map (algebraMap K L)).mulVec x)
        (projectiveMatrixVectorEquations _) z hz hOneY := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  let F := projectiveMatrixGradingMap M
  let bx := linearNormalizedPointChartMapAt I x (projectiveMatrixVectorEquations x)
    (F z) (F.map_mem hz) hOneX
  apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates I
    ((M.map (algebraMap K L)).mulVec x) (projectiveMatrixVectorEquations _)
    z hz hOneY (bx.comp (Away.map F z))
  · rw [RingHom.comp_assoc]
    change bx.comp ((Away.map
      (polynomialQuotientGradingMap I I (rectangularSubstitution M) bot_le
        (fun _ _ hp => rectangularSubstitution_homogeneous M hp)) z).comp
          (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) = _
    rw [polynomialQuotientGradingMap_away_base]
    apply RingHom.ext
    intro r
    exact linearNormalizedPointChartMapAt_base I x (projectiveMatrixVectorEquations x)
      (F z) (F.map_mem hz) hOneX r
  · intro i
    change bx ((Away.map F z)
      (AllCharacteristics.GradedChart.normalized (grading I) hz
        (coordinate I i) (coordinate_mem I i))) = _
    rw [show (Away.map F z)
        (AllCharacteristics.GradedChart.normalized (grading I) hz
          (coordinate I i) (coordinate_mem I i)) =
        AllCharacteristics.GradedChart.normalized (grading I) (F.map_mem hz)
          (F (coordinate I i)) (F.map_mem (coordinate_mem I i)) from
      awayMap_polynomialProjectiveMap_normalized I I (rectangularSubstitution M)
        bot_le (fun _ _ hp => rectangularSubstitution_homogeneous M hp)
        z (coordinate I i) hz (coordinate_mem I i)]
    have hnorm := AllCharacteristics.GradedChart.liftCoordinateOne_normalized
      (grading I) (F z) (projectiveMatrixVectorEvaluation x) hOneX
      (F.map_mem hz) (F (coordinate I i)) (F.map_mem (coordinate_mem I i))
    exact hnorm.trans
      ((RingHom.congr_fun (projectiveMatrixVectorEvaluation_comp M x) (coordinate I i)).trans
        (projectiveMatrixVectorEvaluation_coordinate ((M.map (algebraMap K L)).mulVec x) i))

end PfaffianDescent

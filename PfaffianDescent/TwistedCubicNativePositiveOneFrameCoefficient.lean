import PfaffianDescent.TwistedCubicNativePositivePullbackCharts
import PfaffianDescent.ActualPositiveTwistChartSectionCoefficient

/-! SOURCE ONLY. The native O(1) chart-frame coefficient of the actual other
end-coordinate section is the actual cubic power ratio. Thus the ratio used
by the pullback chart map is tied to the genuine positive sheaf coefficient. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Opposite
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)

/-- Actual O(1) section coefficient, on the first curve chart. -/
theorem standardTwistedCubic_positiveOne_endCoordinate_nativeCoefficient_zero :
    actualPositiveTwistChartSectionCoefficient I
      ⟨coordinate I 0, coordinate_mem I 0⟩ 1
      ((positiveGlobalSectionOfHomogeneous (grading I) 1
        ⟨coordinate I 3, coordinate_mem I 3⟩).val
        (op (Proj.basicOpen (grading I) (coordinate I 0)))) =
      (Proj.awayToSection (grading I) (coordinate I 0)).hom
        (chartCoordinate I 0 1 ^ 3) := by
  rw [actualPositiveTwistChartSectionCoefficient_homogeneousFamily]
  change (Proj.awayToSection (grading I) (coordinate I 0)).hom
    (chartCoordinate I 0 3) = _
  rw [standardTwistedCubic_chart_zero_coordinate_three]

/-- Actual O(1) section coefficient, on the last curve chart. -/
theorem standardTwistedCubic_positiveOne_endCoordinate_nativeCoefficient_three :
    actualPositiveTwistChartSectionCoefficient I
      ⟨coordinate I 3, coordinate_mem I 3⟩ 1
      ((positiveGlobalSectionOfHomogeneous (grading I) 1
        ⟨coordinate I 0, coordinate_mem I 0⟩).val
        (op (Proj.basicOpen (grading I) (coordinate I 3)))) =
      (Proj.awayToSection (grading I) (coordinate I 3)).hom
        (chartCoordinate I 3 2 ^ 3) := by
  rw [actualPositiveTwistChartSectionCoefficient_homogeneousFamily]
  change (Proj.awayToSection (grading I) (coordinate I 3)).hom
    (chartCoordinate I 3 0) = _
  rw [standardTwistedCubic_chart_three_coordinate_zero]

end PfaffianDescent.QuarticNet

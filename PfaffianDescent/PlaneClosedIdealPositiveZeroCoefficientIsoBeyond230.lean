import PfaffianDescent.SchemeModuleTensor
import PfaffianDescent.ProjectivePositiveTwist
import PfaffianDescent.VoisinProjectiveCubicCohomology
import AllCharacteristics.HomogeneousProjective

/-! The canonical degree-zero coefficient Iso, not just a numerical
rank comparison. Its hom is the genuine tensor map followed by the actual
right-unit map, with the SAME original ideal factor. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual first coefficient of I_Z tensor O(0) is canonically the
same original untwisted ideal. No coefficient comparison is assumed. -/
def planeClosedIdeal_positiveZeroCoefficientIso_beyond230
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 3) K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] :
    (PfaffianDescent.closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) 0)).X₁ ≅
        IdealSheafDataModule.closedImmersionModule i := by
  change schemeModuleTensor (IdealSheafDataModule.closedImmersionModule i)
    (positiveSheafOfModules (grading I) 0) ≅ _
  exact schemeModuleTensorMapIso (Iso.refl _)
      (positiveZeroTwistIso (grading I) ≪≫ (unitIsoZeroTwist (grading I)).symm) ≪≫
    schemeModuleTensorUnitRightIso (IdealSheafDataModule.closedImmersionModule i)

end PfaffianDescent.Coray

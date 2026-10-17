import PfaffianDescent.ProjectiveLinearCoordinatePositiveTwistInvIso
import PfaffianDescent.TwistedCubicNativeGlobalPositiveThreeIso
import PfaffianDescent.QuarticTwistedCubicGeometricPresentation

/-! SOURCE ONLY. Ground transport uses EXACT existing original curve-to-P1
Iso and its inverse; no second parametrization or native degree certificate. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped MatrixGroups
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native ORIGINAL curve O(1) pulls back to SAME native O_P1(3) under
EXACT existing GroundTwistedCubicPresentation.schemeIsoProjectiveLine inverse.
Its ordinary ground coordinate presentation supplies only the embedded curve;
the native bundle Iso is derived internally. -/
def GroundTwistedCubicPresentation.nativePositiveOnePullbackIso
    {B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)}
    (hB : GroundTwistedCubicPresentation B) :
    (Scheme.Modules.pullback hB.schemeIsoProjectiveLine.inv).obj
      (positiveSheafOfModules (grading B) 1) ≅
    positiveSheafOfModules (grading
      (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))) 3 := by
  let M : GL (Fin 4) K := Classical.choose hB
  have hM : B.toIdeal.map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom =
      standardTwistedCubicIdeal K := Classical.choose_spec hB
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  let I := standardTwistedCubicHomogeneousIdeal (K := K)
  have hBI : I.toIdeal = B.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) K) hdet).toRingHom := hM.symm
  let e := linearCoordinateChangeSchemeIso (M : Matrix (Fin 4) (Fin 4) K) hdet B I hBI
  let v := standardProjectiveLineToTwistedCubic (K := K)
  change (Scheme.Modules.pullback (v ≫ e.inv)).obj
    (positiveSheafOfModules (grading B) 1) ≅ _
  exact (Scheme.Modules.pullbackComp v e.inv).symm.app
      (positiveSheafOfModules (grading B) 1) ≪≫
    (Scheme.Modules.pullback v).mapIso
      (projectiveLinearCoordinatePositiveTwistInvIso
        (M : Matrix (Fin 4) (Fin 4) K) hdet B I hBI 1) ≪≫
    standardTwistedCubicNativePositiveOnePullbackIso (K := K)

/-- Literal bundle assertion for the SAME original ambient embedding and
SAME original ground parametrization, derived from the actual native producer. -/
def GroundTwistedCubicPresentation.nativeAmbientPositiveOnePullbackIso
    {B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)}
    (hB : GroundTwistedCubicPresentation B) :
    (Scheme.Modules.pullback (hB.schemeIsoProjectiveLine.inv ≫ quotientProjMap B)).obj
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 1) ≅
    positiveSheafOfModules (grading
      (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))) 3 :=
  (Scheme.Modules.pullbackComp hB.schemeIsoProjectiveLine.inv (quotientProjMap B)).symm.app
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 1) ≪≫
    (Scheme.Modules.pullback hB.schemeIsoProjectiveLine.inv).mapIso
      (actualAmbientPositiveTwistQuotientIso B 1) ≪≫
    hB.nativePositiveOnePullbackIso

end PfaffianDescent.QuarticNet

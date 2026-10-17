import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoefficientIdealTwistMap
import PfaffianDescent.CubicClosedPointSerreTensorStalkPositiveIso
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K L : Type u} [Field K] [Field L] (g : K →+* L)
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  {D : Scheme.{u}} (i : D ⟶ hypersurface p hp) [IsClosedImmersion i]

/-- The actual coefficient pullback of the original Serre quotient is the
actual ideal of the literal pulled closed immersion twisted by native O(3). -/
def cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistIso :
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) ≅
    closedImmersionIdealTwist
      (pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i)
      (positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) 3) :=
  cubicClosedPointSerreTensorStalk_pullbackPositiveThreeTensorIso (equationIdeal p hp)
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)
    (IdealSheafDataModule.closedImmersionModule i) ≪≫
  schemeModuleTensorMapIso
    (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealIso g p hp i)
    (cubicClosedPointSerreFiniteZeroResidual_coefficientPositiveTwistIso g p hp 3)

theorem cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistIso_hom :
    (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistIso g p hp i).hom =
    cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistMap g p hp i 3 := rfl

theorem cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistIso_inclusion :
    (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistIso g p hp i).hom ≫
      (closedImmersionIdealTwistSequence
        (pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i)
        (positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) 3)).f =
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).map
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).f ≫
      cubicClosedPointSerreFiniteZeroResidual_coefficientTwistedUnitMap g p hp 3 :=
  cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistMap_inclusion g p hp i 3

/-- Retargeting the actual pulled source by its native affine-spectrum
isomorphism keeps the same ideal and the same new cubic. -/
def cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistSourceIso
    {Z : Scheme.{u}}
    (e : Z ≅ pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i) :
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) ≅
    closedImmersionIdealTwist
      (e.hom ≫ pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i)
      (positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) 3) :=
  cubicClosedPointSerreFiniteZeroResidual_coefficientIdealTwistIso g p hp i ≪≫
    schemeModuleTensorMapIso
      (closedImmersionModuleSourceIso e
        (pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i)).symm
      (Iso.refl _)
end PfaffianDescent.ProjectiveNegativeTwist

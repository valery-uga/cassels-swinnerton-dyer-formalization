import PfaffianDescent.CubicPointTraceFieldBaseChangeNegativeTwist
import PfaffianDescent.AffineSourceChartBaseChange
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

def cubicClosedPointSerreFiniteZeroResidual_coefficientIdealIso :
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj
      (IdealSheafDataModule.closedImmersionModule i) ≅
    IdealSheafDataModule.closedImmersionModule
      (pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i) := by
  letI := isIso_flatClosedImmersionIdealBaseChangeHom_general
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i
  exact asIso (closedImmersionIdealBaseChangeHom
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i)

theorem cubicClosedPointSerreFiniteZeroResidual_coefficientIdealIso_toUnit :
    (cubicClosedPointSerreFiniteZeroResidual_coefficientIdealIso g p hp i).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) i) =
    (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
      BundleSectionZeroLocus.pullbackUnitComparison
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) :=
  closedImmersionIdealBaseChangeHom_toUnit _ _
end PfaffianDescent.ProjectiveNegativeTwist

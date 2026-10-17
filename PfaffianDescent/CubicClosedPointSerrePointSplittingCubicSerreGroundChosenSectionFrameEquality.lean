import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionCompositeIso
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionPullbackComp
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalFrame

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The two existing native coefficient frames are the same actual geometric map. -/
theorem pointSplittingCubicSerreGroundChosenSection_coefficientFrame_eq
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
 :
    serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C =
      pointSplittingCubicSerreGroundKernel_coefficientFrame (F := F) p hp e C := by
  unfold serreIncidenceCubicCoefficientGlobalFrame
    pointSplittingCubicSerreGroundKernel_coefficientFrame
  rfl

end PfaffianDescent

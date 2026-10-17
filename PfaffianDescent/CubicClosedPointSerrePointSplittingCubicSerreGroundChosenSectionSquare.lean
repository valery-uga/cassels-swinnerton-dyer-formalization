import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionCompositeApply
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionCombination
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionPullbackComp

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The true section comparison intertwines the actual double pullback map
with the original canonical nine-section combination map. -/
theorem pointSplittingCubicSerreGroundChosenSection_tensor_square
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9) :
    (pointSplittingCubicSerreGroundChosenSection_compositeTensorMap (F := F) (E := E) p hp e C).comp
      (pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv
        (F := F) (E := E) p hp e C).symm.toLinearMap =
    pointSplittingCubicSerreGroundChosenSection_originalCombinationMap (F := F) (E := E) p hp e h9 := by
  let b := Module.finBasisOfFinrankEq K
    (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9
  apply (b.baseChange E).ext
  intro i
  rw [pointSplittingCubicSerreGroundChosenSection_originalCombinationMap, Module.Basis.constr_basis]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Module.Basis.baseChange_apply]
  rw [pointSplittingCubicSerreGroundChosenSection_originalTensor_symm_tmul,
    pointSplittingCubicSerreGroundChosenSection_compositeTensorMap_tmul, one_smul]
  exact pointSplittingCubicSerreGroundChosenSection_pulledSection_comp _ _ _ _ _ _ rfl e.E (b i)

end PfaffianDescent

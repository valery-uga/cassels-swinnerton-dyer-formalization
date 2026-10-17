import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicOriginalNativeMatrixOperator
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundKernelRangeEvaluationFactory
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundKernelData
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelTensorRange
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsApply

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
variable {K E : Type u} [Field K] [Field E]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable [hB : IsIntegral (cubicConfigurationBase p hp 3)]
local instance : IsIntegral (projectiveConfigurationQuotientOpen
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) 3).toScheme := hB
variable [hordered : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
local instance : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 3).left := hordered
variable (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
variable (β : (cubicConfigurationBase p hp 3).functionField →+* E)
variable (hβ : Spec.map (CommRingCat.ofHom β) ≫
    (cubicConfigurationBase p hp 3).fromSpecStalk
      (genericPoint (cubicConfigurationBase p hp 3)) =
    c ≫ configurationQuotientMap (equationIdeal p hp) 3)
variable (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
variable (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫
    cubicConfigurationToBase p hp 3)


open ProjectiveNegativeTwist

/-- Stage the actual native tensor-kernel range theorem before supplying
chart-dependent coordinates and column identities. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_rangeFactory
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (h3 : Module.finrank (cubicConfigurationBase p hp 3).functionField
      (LinearMap.ker (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)) = 3)
 :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  serreIncidenceCubicNativeGroundKernel_rangeEvaluationFactory p hp c β hβ a ha e C h9 h3
    (pointSplittingCubicSerreGroundKernel_originalKernelTensorEquiv p hp c β hβ a ha e C)

end PfaffianDescent

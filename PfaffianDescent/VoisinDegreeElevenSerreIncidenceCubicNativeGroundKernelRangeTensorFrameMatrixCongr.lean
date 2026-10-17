import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundKernelRangeTensorFrameEquality

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
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
variable (β : (cubicConfigurationBase p hp 3).functionField →+* E)
variable (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
variable (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫
    cubicConfigurationToBase p hp 3)
variable {N : (hypersurface p hp).Modules}
variable (e : SerreExtensionData (hypersurface p hp) N)
variable (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
variable (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
variable (h3 : Module.finrank (cubicConfigurationBase p hp 3).functionField
  (LinearMap.ker (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)) = 3)

/-- A change of the exact named frame changes the actual kernel matrix by
congruence alone. This isolates that conversion from the final transitivity. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_originalFrameMatrix_eq_tensorColumnFrameMatrix :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  let bF := (Module.finBasisOfFinrankEq K
    (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9).baseChange F
  congrArg (fun frame => serreIncidenceGroundKernelMatrix
      (serreIncidenceCubicNativeGroundRestriction p hp a ha e C) (bF.map frame)
      (serreIncidenceCubicNativeGroundKernelBasis p hp a ha e C h9 h3))
      (serreIncidenceCubicNativeGroundKernel_tensorColumnNativeFrame_eq_globalFrame
        p hp a e C).symm

end PfaffianDescent

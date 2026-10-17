import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSections
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalFrame
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelLeftInverse
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreKernel

/-! # Actual unordered restriction, transported ground basis, and kernel-frame matrices -/
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

def serreIncidenceCubicNativeGroundRestriction
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :=
  cubicClosedPointSerreDegreeThreeEvaluationMap
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
    (cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subschemeι
    (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C).E

def serreIncidenceCubicNativeGroundBasis
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9) :
    Module.Basis (Fin 9) (cubicConfigurationBase p hp 3).functionField
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C).E) := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  exact serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9

def serreIncidenceCubicNativeGroundKernelBasis
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (h3 : Module.finrank (cubicConfigurationBase p hp 3).functionField
      (LinearMap.ker (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)) = 3) :
    Module.Basis (Fin 3) (cubicConfigurationBase p hp 3).functionField
      (LinearMap.ker (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)) := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : FiniteDimensional F
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C).E) :=
    (serreIncidenceCubicNativeGroundBasis p hp a e C h9).finiteDimensional_of_finite
  exact Module.finBasisOfFinrankEq F _ h3

def serreIncidenceCubicNativeGroundKernelMatrix
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (h3 : Module.finrank (cubicConfigurationBase p hp 3).functionField
      (LinearMap.ker (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)) = 3) :
    Matrix (Fin 9) (Fin 3) (cubicConfigurationBase p hp 3).functionField :=
  serreIncidenceGroundKernelMatrix
    (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)
    (serreIncidenceCubicNativeGroundBasis p hp a e C h9)
    (serreIncidenceCubicNativeGroundKernelBasis p hp a ha e C h9 h3)

end PfaffianDescent

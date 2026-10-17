import PfaffianDescent.SerreActualCoefficientGlobalFrameBridge
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundKernelData
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsApply
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundTensorFrameCoordinates

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

variable {N : (hypersurface p hp).Modules}
variable (e : SerreExtensionData (hypersurface p hp) N)
variable (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
variable (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
variable (h3 : Module.finrank (cubicConfigurationBase p hp 3).functionField
  (LinearMap.ker (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)) = 3)

/-- Name the actual coefficient frame with its literal pullback-module endpoint.
The native restriction views this same module as the pulled Serre middle module;
inferring the endpoint avoids repeatedly reducing that rich Serre datum. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_originalFrame :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C

/-- The checked global-basis formula specialised to the actual ground field.
Its inferred proposition retains the literal module endpoint. The native
basis and originalFrame names denote these exact generic terms. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_basis_eq_originalFrame :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  serreActualCoefficientGlobalBasis_eq_mappedGlobalFrame (F := F) p hp e C h9

/-- The literal native matrix uses precisely the isolated original frame. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_matrix_eq_originalFrame :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  congrArg (fun basis => serreIncidenceGroundKernelMatrix
    (serreIncidenceCubicNativeGroundRestriction p hp a ha e C) basis
    (serreIncidenceCubicNativeGroundKernelBasis p hp a ha e C h9 h3))
    (serreIncidenceCubicNativeGroundKernel_basis_eq_originalFrame p hp a e C h9)

/-- Specialise the checked literal original-section tensor-frame equality
with the native coefficient actions and scalar tower. Both native comparison
names are exact aliases of these terms; no geometry certificate is supplied. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_sectionsTensor_eq_originalFrame :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  serreActualOriginalSectionsTensorEquiv_eq_coefficientGlobalFrame
    (F := F) (E := E) p hp e C

end PfaffianDescent

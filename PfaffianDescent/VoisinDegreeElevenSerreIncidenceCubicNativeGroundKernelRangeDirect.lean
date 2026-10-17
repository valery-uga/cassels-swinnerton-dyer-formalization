import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundKernelRangeTensorNamedColumn
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicOriginalNativeMatrixOperator
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeKernelColumnsRange

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

variable {B : Scheme.{u}} (chart : Fin 3 → C.ι)
variable (marked : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u})) (cB : Spec (.of E) ⟶ B)
variable (hpoint : ∀ i, (cB ≫ marked i) ≫ (C.U (chart i)).ι =
  serreIncidenceCubicOriginalMarkedPoint p hp c i)
variable (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2)))

/-- Exact native ground matrix range equals the literal native evaluation
matrix kernel. Actual basis columns and evaluator operator are supplied
internally, without a range/coordinate/section certificate premise. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_range_direct :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  serreIncidenceNativeKernelColumns_range
    (pointSplittingCubicSerrePulledEvaluation_originalEvaluator p hp c β hβ a ha e.E)
    ((Module.finBasisOfFinrankEq K
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9).baseChange E)
    (serreIncidenceCubicOriginalNativeExactCoordinates p hp c e C chart marked cB hpoint ρ)
    (serreIncidenceCubicNativeGroundKernel_originalTensorBasis p hp c β hβ a ha e C h9 h3)
    (serreIncidenceCubicOriginalNativeMatrix p hp e C h9 chart marked cB ρ)
    ((serreIncidenceCubicNativeGroundKernelMatrix p hp a ha e C h9 h3).map β)
    (serreIncidenceCubicOriginalNativeMatrix_operator p hp c β hβ a ha e C h9
      chart marked cB hpoint ρ)
    (serreIncidenceCubicNativeGroundKernel_originalTensorBasis_named_column
      p hp c β hβ a ha e C h9 h3)

end PfaffianDescent

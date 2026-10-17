import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundKernelRangeDirectFrame
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundKernelRangeTensorFrameMatrixCongr

/-! The exact coefficient frame viewed at the native restriction domain gives
the same native matrix and the same original-section tensor comparison. -/
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

/-- The actual native matrix is the matrix in the same typed native-domain
frame used by the checked tensor-column formula. No coordinate input is added. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_matrix_eq_tensorColumnNativeFrame :=
  (serreIncidenceCubicNativeGroundKernel_matrix_eq_originalFrame p hp a ha e C h9 h3).trans
    (serreIncidenceCubicNativeGroundKernel_originalFrameMatrix_eq_tensorColumnFrameMatrix
      p hp a ha e C h9 h3)

/-- The actual original-section comparison is the tensor comparison of this
same frame, so transported kernel-basis coordinates retain their literal map. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_sectionsTensor_eq_tensorColumnNativeFrame :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  (serreIncidenceCubicNativeGroundKernel_sectionsTensor_eq_originalFrame p hp β a e C).trans
    (congrArg (fun frame => serreIncidenceGroundTensorFrame (E := E) frame)
      (serreIncidenceCubicNativeGroundKernel_tensorColumnNativeFrame_eq_globalFrame
        p hp a e C).symm)

end PfaffianDescent

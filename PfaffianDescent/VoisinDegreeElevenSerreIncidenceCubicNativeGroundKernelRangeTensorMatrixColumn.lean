import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundKernelData
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundTensorMatrixColumns

/-! Native specialisation of the actual tensor-frame matrix-column formula.
The proof endpoint is inferred before composing with the native matrix bridge. -/
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

/-- View the exact coefficient global frame at the actual native restriction
domain. Only this small declaration performs the pulled-Serre middle-module
conversion; the subsequent tensor-column specialisation uses its named type. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_tensorColumnNativeFrame :
    let F : Type u := (cubicConfigurationBase p hp 3).functionField
    letI : Algebra K F := a.hom.toAlgebra
    F ⊗[K] SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E ≃ₗ[F]
      SchemeModuleGlobalSectionsOver (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C).E := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  exact serreIncidenceCubicCoefficientGlobalFrame (F := F) p hp e C

/-- The actual ground frame, original basis, unordered restriction and its
actual kernel basis satisfy the checked generic tensor-column formula. -/
@[irreducible]
def serreIncidenceCubicNativeGroundKernel_originalFrame_tensorMatrixColumn :=
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  serreIncidenceGroundTensorMatrix_column (E := E)
    (serreIncidenceCubicNativeGroundKernel_tensorColumnNativeFrame p hp a e C)
    (Module.finBasisOfFinrankEq K
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9)
    (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)
    (serreIncidenceCubicNativeGroundKernelBasis p hp a ha e C h9 h3)

end PfaffianDescent

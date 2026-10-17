import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsApply
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionNative

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

/-- An actual chosen unordered-kernel section, pulled to the same twice
coefficient cubic, is the original canonical nine-section combination with
its true kernel-tensor coordinates. -/
theorem pointSplittingCubicSerreGroundChosenSection_kernel_section_eq_combination
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (σ : LinearMap.ker (cubicClosedPointSerreDegreeThreeEvaluationMap
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subschemeι
      (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C).E)) :
    let F : Type u := (cubicConfigurationBase p hp 3).functionField
    letI : Algebra K F := a.hom.toAlgebra
    letI : Algebra F E := β.toAlgebra
    letI : Algebra K E := (β.comp a.hom).toAlgebra
    letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    serreActualPulledGlobalSection
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (hypersurfaceToBase ((p.map a.hom).map β) ((hp.map a.hom).map β))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap β (p.map a.hom) (hp.map a.hom))
      (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C).E σ.val ≫
      (pointSplittingCubicSerreGroundChosenSection_compositeModuleIso (F := F) (E := E) p hp e.E).hom =
    pointSplittingCubicSerreGroundChosenSection_originalCombinationMap (F := F) (E := E) p hp e h9
      (pointSplittingCubicSerreGroundKernel_originalKernelTensorEquiv p hp c β hβ a ha e C
        (1 ⊗ₜ[F] σ) : E ⊗[K] SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have h := pointSplittingCubicSerreGroundChosenSection_native_section_eq_combination
    a.hom β p hp e C h9 σ.val
  have hκ := pointSplittingCubicSerreGroundKernel_originalKernelTensorEquiv_tmul
    p hp c β hβ a ha e C (1 : E) σ
  change _ = pointSplittingCubicSerreGroundChosenSection_originalCombinationMap
    (F := F) (E := E) p hp e h9
    (pointSplittingCubicSerreGroundKernel_nativeOriginalSectionsTensorEquiv p hp β a e C
      (1 ⊗ₜ[F] σ.val)) at h
  rw [← hκ] at h
  exact h

end PfaffianDescent

import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSections

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

/-- The actual unordered kernel equivalence retains the literal pure section
inclusion, then applies only the native original-section tensor comparison. -/
theorem pointSplittingCubicSerreGroundKernel_originalKernelTensorEquiv_tmul
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (b : E)
    (σ : LinearMap.ker (cubicClosedPointSerreDegreeThreeEvaluationMap
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subschemeι
      (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C).E)) :
    let F : Type u := (cubicConfigurationBase p hp 3).functionField
    letI : Algebra F E := β.toAlgebra
    letI : Algebra K E := (β.comp a.hom).toAlgebra
    (pointSplittingCubicSerreGroundKernel_originalKernelTensorEquiv p hp c β hβ a ha e C
      (b ⊗ₜ[F] σ) : E ⊗[K] SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) =
    pointSplittingCubicSerreGroundKernel_nativeOriginalSectionsTensorEquiv p hp β a e C
      (b ⊗ₜ[F] (σ : SchemeModuleGlobalSectionsOver
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C).E)) := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  let s := serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C
  let Cs := serreIncidenceCubicCoefficientPulledCover a.hom p hp e C
  change pointSplittingCubicSerreGroundKernel_nativeOriginalSectionsTensorEquiv p hp β a e C
    ((pointSplittingCubicSerre_restriction_kernel_tensor_equiv p hp c β hβ a ha s Cs
      (b ⊗ₜ[F] σ) : E ⊗[F] SchemeModuleGlobalSectionsOver
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) s.E)) = _
  congr 1

end PfaffianDescent

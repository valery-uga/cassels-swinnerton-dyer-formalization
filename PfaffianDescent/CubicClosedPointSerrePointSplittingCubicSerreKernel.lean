import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreRestriction
import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteRestrictionApply
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicCoverProjection
import AllCharacteristics.VoisinGenericCubicPoint
import PfaffianDescent.CubicClosedPointSerrePointSplittingOverIso
import PfaffianDescent.CubicConfigurationOrderedFieldComponents

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
open scoped TensorProduct
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


include c β hβ ha hordered in
/-- Literal unordered generic-three restriction kernel scalar extension,
with native scheme splitting and section comparison derived internally. -/
abbrev pointSplittingCubicSerre_restriction_kernel_tensor_equiv
    {M : (hypersurface (p.map a.hom) (hp.map a.hom)).Modules}
    (s : SerreExtensionData (hypersurface (p.map a.hom) (hp.map a.hom)) M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover s)
    :
    let F : Type u := (cubicConfigurationBase p hp 3).functionField
    letI : Algebra F E := β.toAlgebra
    (E ⊗[F] LinearMap.ker (cubicClosedPointSerreDegreeThreeEvaluationMap
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subschemeι
      (show _ from s.E))) ≃ₗ[E]
      LinearMap.ker (pointSplittingCubicSerreGlobalTripleEvaluator p hp c β hβ a ha s) := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra F E := β.toAlgebra
  let D := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  let base := hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  let d := D.val.subschemeι
  let q := d ≫ base
  letI : IsFinite q := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom q
  let e := pointSplittingCubicCoverIso p hp 3 c β hβ a ha
  have he := pointSplittingCubicCoverIso_hom_snd p hp 3 c β hβ a ha
  have hField := cubicConfigurationGenericFiniteSubscheme_isField p hp 3 a ha (0 : Fin 3)
  exact pointSplittingFiniteSerre_restriction_kernel_tensor_equiv base d s C hField e he

include c β hβ ha hordered in
/-- Exact original global-section coefficient formula for native cubic
unordered restriction-kernel scalar extension. -/
abbrev pointSplittingCubicSerre_restriction_kernel_tensor_equiv_tmul
    {M : (hypersurface (p.map a.hom) (hp.map a.hom)).Modules}
    (s : SerreExtensionData (hypersurface (p.map a.hom) (hp.map a.hom)) M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover s)
    (b : E)
    (σ : LinearMap.ker (cubicClosedPointSerreDegreeThreeEvaluationMap
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subschemeι
      (show _ from s.E))) :
    let F : Type u := (cubicConfigurationBase p hp 3).functionField
    letI : Algebra F E := β.toAlgebra
    (pointSplittingCubicSerre_restriction_kernel_tensor_equiv p hp c β hβ a ha s C
      (b ⊗ₜ[F] σ) : E ⊗[F] SchemeModuleGlobalSectionsOver
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) (show _ from s.E)) =
      b ⊗ₜ[F] (σ : SchemeModuleGlobalSectionsOver
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) (show _ from s.E)) := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra F E := β.toAlgebra
  let D := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  let base := hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  let d := D.val.subschemeι
  let q := d ≫ base
  letI : IsFinite q := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom q
  let e := pointSplittingCubicCoverIso p hp 3 c β hβ a ha
  have he := pointSplittingCubicCoverIso_hom_snd p hp 3 c β hβ a ha
  have hField := cubicConfigurationGenericFiniteSubscheme_isField p hp 3 a ha (0 : Fin 3)
  exact pointSplittingFiniteSerre_restriction_kernel_tensor_equiv_tmul base d s C hField e he b σ

end PfaffianDescent

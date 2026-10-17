import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationFiniteDimension
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicCoverProjection
import AllCharacteristics.VoisinGenericCubicPoint
import PfaffianDescent.CubicClosedPointSerrePointSplittingOverIso
import PfaffianDescent.CubicConfigurationOrderedFieldComponents

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
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


/-- Native actual unordered rank-three support has six Serre restriction
values, with its field and coefficient action derived from the configuration. -/
abbrev pointSplittingCubicSerreFiniteGamma_finrank_six
    {M : (hypersurface (p.map a.hom) (hp.map a.hom)).Modules}
    (s : SerreExtensionData (hypersurface (p.map a.hom) (hp.map a.hom)) M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover s)
    := by
  let D := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  have hField := cubicConfigurationGenericFiniteSubscheme_isField p hp 3 a ha (0 : Fin 3)
  exact cubicClosedPointSerreDegreeThreeEvaluationFiniteDimension_finrank_eq_six
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) s C D hField

end PfaffianDescent

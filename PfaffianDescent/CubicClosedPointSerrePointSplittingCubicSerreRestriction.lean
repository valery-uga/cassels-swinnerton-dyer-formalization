import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteDatumRestriction
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



/-- The actual ordered-component tensor evaluator for the coefficient-changed
cubic, retaining the original unordered coefficient field. -/
def pointSplittingCubicSerreGlobalTripleEvaluator
    {M : (hypersurface (p.map a.hom) (hp.map a.hom)).Modules}
    (s : SerreExtensionData (hypersurface (p.map a.hom) (hp.map a.hom)) M) := by
  letI : Algebra (cubicConfigurationBase p hp 3).functionField E := β.toAlgebra
  let D := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  let base := hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  let d := D.val.subschemeι
  let q := d ≫ base
  letI : IsFinite q := D.property.1
  let e := pointSplittingCubicCoverIso p hp 3 c β hβ a ha
  have he := pointSplittingCubicCoverIso_hom_snd p hp 3 c β hβ a ha
  let δ := fun k : Fin 3 => pointSplittingFiniteComponentPoint q 3 e (ULift.up k)
  let hδ := fun k => pointSplittingFiniteComponentPoint_toBase q 3 e he (ULift.up k)
  exact cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
    base (fun k => δ k ≫ d)
    (fun k => by simpa only [Category.assoc] using hδ k) (show _ from s.E)

/-- Native unordered generic-three restriction onto and kernel dimension
three follow from actual split evaluation; finite field, frame and Gamma
comparisons are all constructed internally. -/
abbrev pointSplittingCubicSerre_restriction_surjective_kernel_three
    {M : (hypersurface (p.map a.hom) (hp.map a.hom)).Modules}
    (s : SerreExtensionData (hypersurface (p.map a.hom) (hp.map a.hom)) M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover s)
    (hglobal : Function.Surjective
      (pointSplittingCubicSerreGlobalTripleEvaluator p hp c β hβ a ha s))
    (hsource : Module.finrank (cubicConfigurationBase p hp 3).functionField
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (show _ from s.E)) = 9) := by
  letI : Algebra (cubicConfigurationBase p hp 3).functionField E := β.toAlgebra
  let D := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  let e := pointSplittingCubicCoverIso p hp 3 c β hβ a ha
  have he := pointSplittingCubicCoverIso_hom_snd p hp 3 c β hβ a ha
  have hField := cubicConfigurationGenericFiniteSubscheme_isField p hp 3 a ha (0 : Fin 3)
  exact pointSplittingFiniteDatumSerre_restriction_surjective_kernel_three
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) D s C hField e he hglobal hsource

end PfaffianDescent

import PfaffianDescent.CubicClosedPointSerrePointSplittingComponents
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
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
variable [hB : IsIntegral (cubicConfigurationBase p hp n)]
local instance : IsIntegral (projectiveConfigurationQuotientOpen
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n).toScheme := hB
variable (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
variable (β : (cubicConfigurationBase p hp n).functionField →+* E)
variable (hβ : Spec.map (CommRingCat.ofHom β) ≫
    (cubicConfigurationBase p hp n).fromSpecStalk
      (genericPoint (cubicConfigurationBase p hp n)) =
    c ≫ configurationQuotientMap (equationIdeal p hp) n)
variable (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
variable (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫
    cubicConfigurationToBase p hp n)

/-- The SAME coefficient-changed actual generic finite configuration splits
at the ordered field lift; neither coefficient field is substituted for the other. -/
def pointSplittingCubicCoverIso :
    (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of E)) ≅
      pullback (cubicConfigurationCoefficientChangedBaseMap p hp n a ha)
        (Spec.map (CommRingCat.ofHom β)) :=
  pointSplittingConfigurationIso (grading (equationIdeal p hp))
    (toBase (equationIdeal p hp)) n c β hβ ≪≫
    pointSplittingPullbackOverIso (cubicConfigurationGenericFiniteBaseMap p hp n)
      (cubicConfigurationCoefficientChangedBaseMap p hp n a ha)
      (Spec.map (CommRingCat.ofHom β))
      (cubicConfigurationGenericFiniteSubschemeIsoGeneric p hp n a ha)
      (cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_toBase p hp n a ha)

end PfaffianDescent

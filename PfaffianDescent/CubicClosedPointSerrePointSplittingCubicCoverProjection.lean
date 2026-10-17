import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicCover
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

/-- Native structural projection after coefficient change, with inferred type. -/
abbrev pointSplittingCubicCoverIso_hom_snd := by
  let f := toBase (equationIdeal p hp)
  let e0 := pointSplittingConfigurationIso (grading (equationIdeal p hp)) f n c β hβ
  let eD := cubicConfigurationGenericFiniteSubschemeIsoGeneric p hp n a ha
  have h0 := pointSplittingConfigurationIso_hom_snd (grading (equationIdeal p hp)) f n c β hβ
  have h := pointSplittingPullbackOverIso_hom_snd
    (cubicConfigurationGenericFiniteBaseMap p hp n)
    (cubicConfigurationCoefficientChangedBaseMap p hp n a ha)
    (Spec.map (CommRingCat.ofHom β)) eD
    (cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_toBase p hp n a ha)
  exact (congrArg (fun v => e0.hom ≫ v) h).trans h0

/-- The native split cover retains the SAME coefficient-changed labeled point. -/
abbrev pointSplittingCubicCoverIso_component_fst (i : Fin n) := by
  let f := toBase (equationIdeal p hp)
  let e0 := pointSplittingConfigurationIso (grading (equationIdeal p hp)) f n c β hβ
  let eD := cubicConfigurationGenericFiniteSubschemeIsoGeneric p hp n a ha
  have h0 := pointSplittingConfigurationIso_component_fst
    (grading (equationIdeal p hp)) f n c β hβ i
  have h := pointSplittingPullbackOverIso_hom_fst
    (cubicConfigurationGenericFiniteBaseMap p hp n)
    (cubicConfigurationCoefficientChangedBaseMap p hp n a ha)
    (Spec.map (CommRingCat.ofHom β)) eD
    (cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_toBase p hp n a ha)
  have h1 := congrArg (fun v => Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of E))
    (ULift.up i) ≫ e0.hom ≫ v) h
  have h2 := congrArg (fun v => v ≫ eD.inv) h0
  have h2' : (Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of E)) (ULift.up i) ≫
      e0.hom ≫ pullback.fst (cubicConfigurationGenericFiniteBaseMap p hp n)
        (Spec.map (CommRingCat.ofHom β))) ≫ eD.inv = _ := h2
  exact h1.trans (by simpa only [Category.assoc] using h2')

end PfaffianDescent

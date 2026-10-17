import PfaffianDescent.CubicFiniteFieldDatumSerreExtension
import PfaffianDescent.VoisinGenericCubicPoint

/-! # Serre construction on the actual generic degree-eleven configuration

Smoothness, nonvanishing, characteristic zero and the field property of the
generic finite datum are all derived from the original smooth cubic and its
finite etale rank-eleven datum. No trace or transitivity assumption remains.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- The actual generic unordered rank-eleven datum has a Serre sequence
with nonzero connecting product. Its coefficient-field and closed-point
inputs are constructed, rather than supplied separately. -/
theorem cubicGenericDegreeElevenSerreExtension_exists_sequence
    (K : Type u) [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
    [Etale (D₀.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 11) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 11 D₀
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 11).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 11 ≫
        cubicConfigurationToBase p hp 11),
    let P := p.map a.hom
    let hP := hp.map a.hom
    let X := hypersurface P hP
    let T := positiveSheafOfModules (grading (equationIdeal P hP)) 3
    let D := cubicConfigurationGenericFiniteSubscheme p hp 11 a ha
    let i := finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D
    letI : IsClosedImmersion i := finiteSubschemeDatumSpecMap_isClosedImmersion
      (hypersurfaceToBase P hP) D
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal P hP) 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal P hP) 3
    ∃ e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T),
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} X
          (closedImmersionIdealTwist i T) e (schemeModules_hasExt X))
        (show 1 + 1 = 2 by omega) ≠ 0 := by
  letI : IsIntegral (cubicConfigurationBase p hp 11) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 11 D₀
  intro a ha
  let F := (cubicConfigurationBase p hp 11).functionField
  letI : CharZero F := charZero_of_injective_ringHom a.hom.injective
  let P := p.map a.hom
  let hP := hp.map a.hom
  letI : Smooth (hypersurfaceToBase P hP) := smooth_hypersurfaceToBase_map a.hom p hp
  have hP0 : P ≠ 0 := cubicConfigurationCoefficientChange_ne_zero p hp 11 a hp0
  let D := cubicConfigurationGenericFiniteSubscheme p hp 11 a ha
  let i := finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D
  letI : IsClosedImmersion i := finiteSubschemeDatumSpecMap_isClosedImmersion
    (hypersurfaceToBase P hP) D
  letI : HasExt.{u} (hypersurface P hP).Modules := schemeModules_hasExt _
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal P hP) 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal P hP) 3
  have hField : IsField Γ(D.val.subscheme, ⊤) :=
    cubicConfigurationGenericFiniteSubscheme_isField_of_smooth p hp hp0 11 D₀
      ⟨0, by decide⟩ a ha
  obtain ⟨e, he, _⟩ := cubicFiniteFieldDatumSerreExtension_exists_sequence F P hP hP0 D hField
  exact ⟨e, he⟩

set_option backward.isDefEq.respectTransparency false in
/-- The literal ideal of the actual generic rank-eleven configuration has
a nonzero positive-three section. The original datum is used only to
construct the configuration base and its transitive generic field point. -/
theorem cubicGenericDegreeElevenSerreQuotientSection_exists_nonzero
    (K : Type u) [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
    [Etale (D₀.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 11) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 11 D₀
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 11).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 11 ≫
        cubicConfigurationToBase p hp 11),
    ∃ t : (closedImmersionIdealTwist
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
          (cubicConfigurationGenericFiniteSubscheme p hp 11 a ha))
        (positiveSheafOfModules (grading (equationIdeal (p.map a.hom) (hp.map a.hom))) 3)).sections,
      t ≠ SerreExtensionData.zeroSection _ := by
  letI : IsIntegral (cubicConfigurationBase p hp 11) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 11 D₀
  intro a ha
  let F := (cubicConfigurationBase p hp 11).functionField
  letI : CharZero F := charZero_of_injective_ringHom a.hom.injective
  let P := p.map a.hom
  let hP := hp.map a.hom
  letI : Smooth (hypersurfaceToBase P hP) := smooth_hypersurfaceToBase_map a.hom p hp
  have hP0 : P ≠ 0 := cubicConfigurationCoefficientChange_ne_zero p hp 11 a hp0
  let D := cubicConfigurationGenericFiniteSubscheme p hp 11 a ha
  have hField : IsField Γ(D.val.subscheme, ⊤) :=
    cubicConfigurationGenericFiniteSubscheme_isField_of_smooth p hp hp0 11 D₀
      ⟨0, by decide⟩ a ha
  exact cubicFiniteFieldDatumSerreQuotientSection_exists_nonzero F P hP hP0 D hField

end PfaffianDescent.ProjectiveNegativeTwist

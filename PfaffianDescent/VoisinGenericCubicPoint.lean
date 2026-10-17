import AllCharacteristics.VoisinGenericCubicPoint
import PfaffianDescent.VoisinGenericCubicResidual

/-!
# Transitivity of the generic configuration on a smooth cubic

These entrypoints derive ordered-configuration integrality from the original
smooth cubic and a finite étale datum. Thus the one-point and all-or-none
results require no additional generic-incidence hypothesis in Voisin's
characteristic-zero setting.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The generic configuration arising from a nonempty finite étale datum
on a smooth cubic is a single closed point over the configuration function
field. Its coordinate algebra is a field. -/
theorem cubicConfigurationGenericFiniteSubscheme_isField_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)] (i : Fin n) :
    letI : IsIntegral (cubicConfigurationBase p hp n) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp n).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n),
      IsField Γ((cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme, ⊤) := by
  letI : IsIntegral (cubicConfigurationBase p hp n) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D
  intro a ha
  letI : IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left :=
    isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D
  exact cubicConfigurationGenericFiniteSubscheme_isField p hp n a ha i

/-- Voisin's all-or-none assertion for any closed subscheme defined over
the generic configuration field, proved from the smooth-cubic input. -/
theorem genericCubicClosedSubscheme_isEmpty_pullback_or_factors_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)] (i : Fin n) :
    letI : IsIntegral (cubicConfigurationBase p hp n) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp n).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n)
      (C : Scheme.{u}) (j : C ⟶ hypersurface (p.map a.hom) (hp.map a.hom)),
      IsClosedImmersion j →
      IsEmpty (pullback j (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subschemeι :
        Scheme.{u}) ∨
        ∃ h : (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme ⟶ C,
          h ≫ j = (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subschemeι := by
  letI : IsIntegral (cubicConfigurationBase p hp n) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D
  intro a ha C j hj
  letI : IsClosedImmersion j := hj
  letI : IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left :=
    isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D
  exact cubicConfigurationGenericFiniteSubscheme_isEmpty_pullback_or_factors p hp n a ha i j

end PfaffianDescent

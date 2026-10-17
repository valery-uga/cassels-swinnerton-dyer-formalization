import PfaffianDescent.VoisinActualDegreeFourFromCanonicalFinite

/-! Apply the actual degree-four construction to every finite canonical
presentation in a family over an unordered configuration base. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- At each coefficient map, choose an actual generic presentation with a
finite canonical intrinsic ordered fiber. -/
def ActualCanonicalFiniteFamily
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i] : Prop :=
  ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8),
    ∃ hz : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField),
      ∃ w : ActualGenericEightPresentation p hp a ha i hz,
        IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
          (p.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
            (orderedFamilyConfigurationOver
              (hypersurfaceToBase p hp) 8).hom)).hom))
          (hp.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
            (orderedFamilyConfigurationOver
              (hypersurfaceToBase p hp) 8).hom)).hom))
          (w.canonicalVectors p hp a ha i hz)))

theorem ActualCanonicalFiniteFamily.exists_degreeFourComplement
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [Infinite (cubicConfigurationBase p hp 8).functionField]
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (hdata : ActualCanonicalFiniteFamily p hp i)
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8) :
    let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    Nonempty (DegreeFourTripleComplement (A := Γ(D.val.subscheme, ⊤))
      (p.map a.hom) (hp.map a.hom)) := by
  dsimp only
  obtain ⟨hz, w, hfin⟩ := hdata a ha
  letI := hfin
  exact w.exists_degreeFourComplement_of_canonicalFinite p hp a ha i hz

end PfaffianDescent

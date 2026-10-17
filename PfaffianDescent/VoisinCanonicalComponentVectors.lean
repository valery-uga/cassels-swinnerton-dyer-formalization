import PfaffianDescent.VoisinCanonicalComponentMarkedPoint

/-! Canonical component vectors represent the ordered marked points. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized vector obtained by evaluating geometric generic-eight
coordinates at a labeled component represents the canonical marked point
after the coefficient change back to the original ambient space. -/
theorem GeometricDetectingEightCoordinates.canonicalComponentVector_markedPoint
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
      cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : configurationQuotientMap (equationIdeal cubic hcubic) 8 z =
      (cubicConfigurationBase cubic hcubic 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase cubic hcubic 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase cubic hcubic 8).functionField))
    (d :
      let Q := cubicConfigurationBase cubic hcubic 8
      let O := (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).left
      let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
      let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
      let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
      letI : IsFinite pD := D.property.1
      letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
      letI := finiteSchemeCoefficientAlgebra pD
      letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
      GeometricDetectingEightCoordinates
        (fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
          cubic hcubic a ha z hz i)
        (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient (cubic.map a.hom) (hcubic.map a.hom)))
    (i : Fin 8) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField]
      O.residueField z := fun k =>
        quadraticOrderedLiftCoefficientChangedComponentAlgHom
          cubic hcubic a ha z hz k
    let I : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q.functionField) := ⊥
    let zc : CoordinateRing I := Ideal.Quotient.mk I.toIdeal d.ell
    let hzc : zc ∈ grading I 1 :=
      polynomial_class_mem_grading I d.ell d.ellHomogeneous
    let y : Fin 4 → O.residueField z := fun r => φ i (d.x r)
    let he : ∀ q ∈ I.toIdeal,
      (eval₂Hom (algebraMap Q.functionField (O.residueField z)) y) q = 0 := by
        intro q hq
        exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
    ∃ (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap Q.functionField (O.residueField z)) y) he) zc = 1),
      (linearNormalizedPointAt I y he zc hzc hzOne ≫ quotientProjMap I) ≫
        ambientCoefficientMap a.hom =
      O.fromSpecResidueField z ≫
        @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _
          (hypersurfaceToBase cubic hcubic) hsep 8
          (hypersurfaceToAmbient cubic hcubic) i := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField]
      O.residueField z := fun k =>
    quadraticOrderedLiftCoefficientChangedComponentAlgHom cubic hcubic a ha z hz k
  let j := D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
    hypersurfaceToAmbient (cubic.map a.hom) (hcubic.map a.hom)
  let marked := O.fromSpecResidueField z ≫
    @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _
      (hypersurfaceToBase cubic hcubic) hsep 8
      (hypersurfaceToAmbient cubic hcubic) i
  have hmarked :
      (Spec.map (CommRingCat.ofHom (φ i).toRingHom) ≫ j) ≫
        ambientCoefficientMap a.hom = marked :=
    quadraticOrderedLift_componentAmbientPoint_eq_markedPoint
      cubic hcubic a ha z hz i
  exact d.componentVector_ambientPoint φ j i
    (ambientCoefficientMap a.hom) marked hmarked

end PfaffianDescent

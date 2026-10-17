import PfaffianDescent.VoisinGeometricComponentVectorComposition
import PfaffianDescent.VoisinGenericQuadraticEvaluation

/-! The canonical component of the finite generic scheme is the ordered marked point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ambient immersion of the generic finite scheme sends its
`i`-th residue-field component to the corresponding ordered marked point. -/
theorem quadraticOrderedLift_componentAmbientPoint_eq_markedPoint
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
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let φ := quadraticOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
        hypersurfaceToAmbient p' hp') ≫ ambientCoefficientMap a.hom =
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z ≫
        @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _
          (hypersurfaceToBase cubic hcubic) hsep 8
          (hypersurfaceToAmbient cubic hcubic) i := by
  dsimp only
  exact quadraticOrderedLiftCoefficientChangedComponentAlgHom_chart_toMarkedPoint
    cubic hcubic a ha z hz i _ rfl

end PfaffianDescent

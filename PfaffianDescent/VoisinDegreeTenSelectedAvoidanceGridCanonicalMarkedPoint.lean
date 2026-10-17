import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridComponentExtension
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericCoefficients
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_canonicalSixteen_extendedComponent_actualMarkedPoint
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 16).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    (z : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 16 z =
      (cubicConfigurationBase p hp 16).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 16))
        (IsLocalRing.closedPoint (cubicConfigurationBase p hp 16).functionField))
    (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left)
    (g : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left.residueField z →+* E)
    (hg : Spec.map (CommRingCat.ofHom g) ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left.fromSpecResidueField z = c) :
    let Q := cubicConfigurationBase p hp 16
    let O := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
    let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom p hp z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    letI : Algebra Q.functionField E := (g.comp b).toAlgebra
    let j := D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
      hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)
    ∀ k : Fin 16,
      Spec.map (CommRingCat.ofHom (voisinDegreeTenSelectedAvoidance_extendComponent g
        (cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom p hp a ha z hz k)).toRingHom) ≫
          (j ≫ ambientCoefficientMap a.hom) = c ≫
        @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) _ 16
          (hypersurfaceToAmbient p hp) k := by
  dsimp only
  let Q := cubicConfigurationBase p hp 16
  let O := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
  let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom p hp z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  letI : Algebra Q.functionField E := (g.comp b).toAlgebra
  let j := D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
    hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)
  intro k
  have hmarked := cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom_chart_toMarkedPoint
    p hp a ha z hz k (j ≫ ambientCoefficientMap a.hom) (by rfl)
  have hmarkedE := voisinDegreeTenSelectedAvoidance_extendedComponent_exactMarkedPoint g
    (cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom p hp a ha z hz k)
    (j ≫ ambientCoefficientMap a.hom) _ hmarked
  refine hmarkedE.trans ?_
  rw [← Category.assoc, hg]

end PfaffianDescent

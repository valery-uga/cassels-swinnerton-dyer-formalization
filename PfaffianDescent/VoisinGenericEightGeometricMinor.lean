import PfaffianDescent.VoisinGenericEightGeometricCoordinates
import PfaffianDescent.VoisinGenericEightComponentSpan
import PfaffianDescent.VoisinSplitQuadraticMinorFromComponentSpan

/-! The actual generic eight-point embedding has a unit quadratic minor. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A geometric detecting presentation together with a unit quadratic
evaluation minor for the same four coordinate functions. -/
structure GeometricEightMinorData
    {Q A L : Type u} [Field Q] [CommRing A] [Algebra Q A]
    [Field L] [Algebra Q L]
    (φ : Fin 8 → A →ₐ[Q] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) Q)) where
  coords : GeometricDetectingEightCoordinates φ j
  m : Fin 8 ↪ Monomials (Fin 4) 2
  minorUnit : IsUnit (eightPointQuadraticEvaluationMinor m
    (fun k r => φ k (coords.x r))).det

/-- A selected invertible quadratic evaluation minor can be chosen while
retaining the normalized chart map of the actual finite rank-eight scheme. -/
theorem exists_cubicConfigurationGenericEight_geometricUnitQuadraticMinor_of_noCommon
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [Infinite (cubicConfigurationBase p hp 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 8 z =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField))
    (hno : QuadraticEightNoCommonResidueFieldEquationAt p hp z) :
    let Q := cubicConfigurationBase p hp 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left
    let p' := p.map a.hom
    let hp' := hp.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom p hp z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField]
      O.residueField z := fun k =>
        quadraticOrderedLiftCoefficientChangedComponentAlgHom p hp a ha z hz k
    Nonempty (GeometricEightMinorData φ
      (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
        hypersurfaceToAmbient p' hp')) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let p' := p.map a.hom
  let hp' := hp.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom p hp z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField]
      O.residueField z := fun k =>
    quadraticOrderedLiftCoefficientChangedComponentAlgHom p hp a ha z hz k
  obtain ⟨d⟩ :=
    exists_cubicConfigurationGenericEight_geometricQuadraticCoordinates_of_noCommon
      p hp a ha z hz hno
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 8 := by
    apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)
  have hspan := cubicConfigurationGenericEight_componentSpan_eq_top
    p hp a ha z hz
  obtain ⟨m, hm⟩ :=
    d.exists_unitQuadraticMinor φ
      (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
        hypersurfaceToAmbient p' hp') hA hspan
  exact ⟨⟨d, m, hm⟩⟩

end PfaffianDescent

import PfaffianDescent.VoisinActualEightPresentation
import PfaffianDescent.VoisinGenericEightGeometricMinor

/-! A geometric actual eight-point presentation has an invertible
quadratic evaluation minor on its canonical component vectors. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ActualGenericEightPresentation.exists_canonical_unitQuadraticMinor
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (hz : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField))
    (w : ActualGenericEightPresentation p hp a ha i hz) :
    let F := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left.residueField (i (genericPoint U))
    ∃ m : Fin 8 ↪ Monomials (Fin 4) 2,
      IsUnit (eightPointQuadraticEvaluationMinor (R := F) m
        (w.canonicalVectors p hp a ha i hz)).det := by
  dsimp only
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom p hp
    (i (genericPoint U)) hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
    b.toAlgebra
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField]
      O.residueField (i (genericPoint U)) := fun k =>
    quadraticOrderedLiftCoefficientChangedComponentAlgHom
      p hp a ha (i (genericPoint U)) hz k
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 8 := by
    apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)
  have hspan := cubicConfigurationGenericEight_componentSpan_eq_top
    p hp a ha (i (genericPoint U)) hz
  obtain ⟨m, hm⟩ :=
    w.d.exists_unitQuadraticMinor φ
      (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
        hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)) hA hspan
  exact ⟨m, hm⟩

end PfaffianDescent

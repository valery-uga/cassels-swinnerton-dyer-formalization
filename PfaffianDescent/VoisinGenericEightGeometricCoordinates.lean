import PfaffianDescent.VoisinGenericQuadraticDetection
import PfaffianDescent.FiniteSubschemeCompleteIntersection
import PfaffianDescent.VoisinSplitQuadraticMinorFromComponentSpan

/-! Keep the actual embedding with the generic eight-point coordinates. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A quadratic-detecting presentation whose normalized point is a specified
geometric immersion, rather than an arbitrary four-coordinate algebra map. -/
structure GeometricDetectingEightCoordinates
    {Q A L : Type u} [Field Q] [CommRing A] [Algebra Q A]
    [Field L] [Algebra Q L]
    (φ : Fin 8 → A →ₐ[Q] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) Q)) where
  ell : MvPolynomial (Fin 4) Q
  ellHomogeneous : ell.IsHomogeneous 1
  x : Fin 4 → A
  he : ∀ q ∈ (⊥ : HomogeneousIdeal
    (homogeneousSubmodule (Fin 4) Q)).toIdeal,
    (eval₂Hom (algebraMap Q A) x) q = 0
  ellOne : (Ideal.Quotient.lift
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)).toIdeal
    (eval₂Hom (algebraMap Q A) x) he)
      (Ideal.Quotient.mk
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)).toIdeal ell) = 1
  evalSurjective : Function.Surjective (eval₂Hom (algebraMap Q A) x)
  detects : ∀ c : Fin 8 → Q,
    (∀ k, MvPolynomial.eval₂ (algebraMap Q L)
      (fun t => φ k (x t))
      (homogeneousFrameMap 2 (quadraticEightFrame Q) c).1 = 0) → c = 0
  point_eq : linearNormalizedPointAt
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
      x he
      (Ideal.Quotient.mk
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)).toIdeal ell)
      (polynomial_class_mem_grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
        ell ellHomogeneous) ellOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)) = j

/-- Frame detection on a rank-eight algebra makes quadratic restriction
surjective for the very same geometric coordinates. -/
theorem GeometricDetectingEightCoordinates.quadraticSurjective
    {Q A L : Type u} [Field Q] [CommRing A] [Algebra Q A]
    [FiniteDimensional Q A] [Field L] [Algebra Q L]
    (φ : Fin 8 → A →ₐ[Q] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) Q))
    (d : GeometricDetectingEightCoordinates φ j)
    (hA : Module.finrank Q A = 8) :
    Function.Surjective (homogeneousSectionRestriction (K := Q) d.x 2) :=
  quadraticSectionRestriction_surjective_of_embedding_evaluations
    d.x hA φ d.detects

/-- The same geometric coordinates admit a unit quadratic evaluation
minor when the labeled component values span all eight positions. -/
theorem GeometricDetectingEightCoordinates.exists_unitQuadraticMinor
    {Q A L : Type u} [Field Q] [CommRing A] [Algebra Q A]
    [FiniteDimensional Q A] [Field L] [Algebra Q L]
    (φ : Fin 8 → A →ₐ[Q] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) Q))
    (d : GeometricDetectingEightCoordinates φ j)
    (hA : Module.finrank Q A = 8)
    (hspan : Submodule.span L
      (Set.range (fun t : A => fun k : Fin 8 => φ k t)) = ⊤) :
    ∃ m : Fin 8 ↪ Monomials (Fin 4) 2,
      IsUnit (eightPointQuadraticEvaluationMinor m
        (fun k r => φ k (d.x r))).det := by
  exact exists_unit_eightPointQuadraticEvaluationMinor_of_componentSpan
    φ d.x (d.quadraticSurjective φ j hA) hspan

/-- The generic finite rank-eight algebra has quadratic-detecting
coordinates that still represent its actual ambient projective immersion. -/
theorem exists_cubicConfigurationGenericEight_geometricQuadraticCoordinates_of_noCommon
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
    Nonempty (GeometricDetectingEightCoordinates φ
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
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p' hp') := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  obtain ⟨ell, hell, x, he, hellOne, hxsurj, _, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_ambient_chart p' hp' D.val.subschemeι
  refine ⟨{
    ell := ell
    ellHomogeneous := hell
    x := x
    he := he
    ellOne := hellOne
    evalSurjective := hxsurj
    detects := ?_
    point_eq := hpoint }⟩
  exact quadraticOrderedLift_normalizedAmbientChart_detects
    p hp a ha z hz hno ell hell x he hellOne hpoint

end PfaffianDescent

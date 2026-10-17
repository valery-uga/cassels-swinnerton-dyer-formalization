import PfaffianDescent.VoisinGenericEightGeometricCoordinates

/-! Retain the cubic equation alongside normalized detecting coordinates. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Detecting coordinates on a rank-eight algebra that still retain the
ambient cubic equation satisfied by those same coordinates. -/
structure GeometricDetectingCubicCoordinates
    {F A L : Type u} [Field F] [CommRing A] [Algebra F A]
    [Field L] [Algebra F L]
    (p : MvPolynomial (Fin 4) F)
    (φ : Fin 8 → A →ₐ[F] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) F))
    extends GeometricDetectingEightCoordinates φ j where
  cubicVanish : p.eval₂ (algebraMap F A) x = 0

/-- Package a normalized chart after its geometric and quadratic detection
proofs have been established. -/
noncomputable def geometricDetectingCubicCoordinates_of_chart
    {F A L : Type u} [Field F] [CommRing A] [Algebra F A]
    [Field L] [Algebra F L]
    (p : MvPolynomial (Fin 4) F)
    (φ : Fin 8 → A →ₐ[F] L)
    (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) F))
    (ell : MvPolynomial (Fin 4) F) (hell : ell.IsHomogeneous 1)
    (x : Fin 4 → A)
    (he : ∀ q ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) F)).toIdeal,
      (eval₂Hom (algebraMap F A) x) q = 0)
    (hellOne : (Ideal.Quotient.lift
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)).toIdeal
      (eval₂Hom (algebraMap F A) x) he)
        (Ideal.Quotient.mk
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) F)).toIdeal ell) = 1)
    (hxsurj : Function.Surjective (eval₂Hom (algebraMap F A) x))
    (hpoint : linearNormalizedPointAt
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
        x he
        (Ideal.Quotient.mk
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) F)).toIdeal ell)
        (polynomial_class_mem_grading
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
          ell hell) hellOne ≫
          quotientProjMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) = j)
    (hdetect : ∀ c : Fin 8 → F,
      (∀ k, MvPolynomial.eval₂ (algebraMap F L)
        (fun t => φ k (x t))
        (homogeneousFrameMap 2 (quadraticEightFrame F) c).1 = 0) → c = 0)
    (hpx : p.eval₂ (algebraMap F A) x = 0) :
    GeometricDetectingCubicCoordinates p φ j :=
  { ell := ell
    ellHomogeneous := hell
    x := x
    he := he
    ellOne := hellOne
    evalSurjective := hxsurj
    detects := hdetect
    point_eq := hpoint
    cubicVanish := hpx }

/-- The actual generic rank-eight algebra has one normalized detecting chart
which also retains the cubic vanishing equation. -/
theorem exists_cubicConfigurationGenericEight_geometricCubicCoordinates_of_noCommon
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
    Nonempty (GeometricDetectingCubicCoordinates p' φ
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
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField]
      O.residueField z := fun k =>
    quadraticOrderedLiftCoefficientChangedComponentAlgHom
      p hp a ha z hz k
  obtain ⟨ell, hell, x, he, hellOne, hxsurj, hpx, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_ambient_chart p' hp' D.val.subschemeι
  have hdetect := quadraticOrderedLift_normalizedAmbientChart_detects
    p hp a ha z hz hno ell hell x he hellOne hpoint
  exact ⟨geometricDetectingCubicCoordinates_of_chart
    p' φ (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
      hypersurfaceToAmbient p' hp')
    ell hell x he hellOne hxsurj hpoint hdetect hpx⟩

end PfaffianDescent

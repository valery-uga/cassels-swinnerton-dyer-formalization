import PfaffianDescent.VoisinGenericCubicSixteenSurjectivity

/-!
# Cubic rank on every normalized chart of the generic sixteen-point scheme
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On any normalized ambient chart for the actual generic sixteen-point
scheme, cubic equations modulo the surface equation have dimension three. -/
theorem cubicSixteenOrderedLift_normalizedAmbientChart_cubicVanishingModuloEquation_finrank_three
    {K : Type u} [Field K]
    {m : ℕ}
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (e : Fin m ≃ Monomials (Fin 4) 3)
    (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt cubic hcubic e frame hframe z) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    ∀ (ell : MvPolynomial (Fin 4) Q.functionField)
      (hell : ell.IsHomogeneous 1)
      (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (he : ∀ q ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal,
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) q = 0)
      (hellOne : (Ideal.Quotient.lift
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) he)
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell) = 1),
      linearNormalizedPointAt
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField))
          x he
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell)
          (polynomial_class_mem_grading
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)) ell hell)
          hellOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField)) =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient p' hp' →
      (hpx : p'.eval₂
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0) →
      cubicVanishingSectionsModuloEquationFinrank p' hp' x hpx = 3 := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
  intro ell hell x he hellOne hpoint hpx
  have hdet := cubicSixteenOrderedLift_normalizedAmbientChart_detectsFrame
    cubic hcubic a ha z hz e frame hframe hno ell hell x he hellOne hpoint
  have hA : finrank Q.functionField Γ(D.val.subscheme, ⊤) = 16 :=
    cubicConfigurationGenericSixteen_coefficientFinrank cubic hcubic a ha
  have hsurj := sixteen_cubicEvaluation_surjective_of_residue_detection
    hA x (fun j => (frame j).1.map a.hom) φ hdet
  have hr : ∀ j, ((frame j).1.map a.hom).IsHomogeneous 3 := by
    intro j
    exact (frame j).property.map a.hom
  have hfull := cubicSectionRestriction_surjective_of_frameEvaluation
    x (fun j => (frame j).1.map a.hom) hr hsurj
  exact cubic_degree_sixteen_vanishing_sections_finrank_eq_three_of_surjective
    (cubic.map a.hom) (hcubic.map a.hom) x hpx hA hfull

end PfaffianDescent

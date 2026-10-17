import PfaffianDescent.VoisinGenericCubicSixteenEvaluation

/-!
# Surjectivity of generic sixteen-point cubic evaluation

The normalized chart and residue-field detection live in the preceding
module.  Here the finite rank calculation is kept separate so that Lean can
check the final dimension argument at unchanged elaboration limits.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual generic length-sixteen finite scheme has a coefficient
algebra of dimension sixteen over the configuration function field. -/
theorem cubicConfigurationGenericSixteen_coefficientFinrank
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    finrank Q.functionField Γ(D.val.subscheme, ⊤) = 16 := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  apply (finiteSchemeCoefficient_finrank pD).trans
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
  exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)


/-- The actual generic rank-sixteen cubic configuration admits a normalized
chart whose chosen cubic frame surjects onto its coefficient algebra. -/
theorem exists_cubicConfigurationGenericSixteen_surjectiveCubicFrameEvaluation_of_noCommon
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
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
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3)
    (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt
      cubic hcubic e frame hframe z) :
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
    let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    ∃ x : Fin 4 → Γ(D.val.subscheme, ⊤),
      Function.Surjective (eval₂Hom
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) ∧
      Function.Surjective (Fintype.linearCombination Q.functionField
        (fun j => MvPolynomial.eval₂
          (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x
          ((frame j).1.map a.hom))) := by
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
  have hdet : Nonempty (DetectingCubicSixteenFrameCoordinates
      Q.functionField Γ(D.val.subscheme, ⊤) (O.residueField z)
      φ (fun j => (frame j).1.map a.hom)) := by
    exact exists_cubicConfigurationGenericSixteen_detectingCubicFrameCoordinates_of_noCommon
      cubic hcubic a ha z hz e frame hframe hno
  obtain ⟨d⟩ := hdet
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 16 :=
    cubicConfigurationGenericSixteen_coefficientFinrank cubic hcubic a ha
  exact ⟨d.x, d.evalSurjective, d.frameEvaluation_surjective hA⟩

/-- On a prime cubic surface, the actual generic length-sixteen subscheme
admits a sixteen-dimensional cubic frame whose evaluation is surjective.
The ordered point and its incidence avoidance are constructed internally. -/
theorem exists_cubicConfigurationGenericSixteen_surjectiveCubicFrameEvaluation
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    ∃ (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3),
      LinearIndependent K frame ∧
      ∃ x : Fin 4 → Γ(D.val.subscheme, ⊤),
        Function.Surjective (eval₂Hom
          (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) ∧
        Function.Surjective (Fintype.linearCombination Q.functionField
          (fun j => MvPolynomial.eval₂
            (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x
            ((frame j).1.map a.hom))) := by
  dsimp only
  have hgeneric :
      let O := (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).left
      let Q₀ := (projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme
      let π := projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16
      let η := Q₀.fromSpecStalk (genericPoint Q₀)
        (IsLocalRing.closedPoint Q₀.functionField)
      ∃ (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
        (hframe : LinearIndependent K frame) (z : O),
        π z = η ∧
        HomogeneousSixteenNoCommonResidueFieldEquationAt
          cubic hcubic e frame hframe z := by
    exact exists_orderedPointOver_genericSixteen_with_noCommonCubicEquation
      cubic hcubic hcubic_ne hcubic_prime e
  obtain ⟨frame, hframe, z, hz, hno⟩ := hgeneric
  have hsurj :=
    exists_cubicConfigurationGenericSixteen_surjectiveCubicFrameEvaluation_of_noCommon
      cubic hcubic a ha z hz e frame hframe hno
  exact ⟨frame, hframe, hsurj⟩


/-- The cubic equations vanishing on the actual generic length-sixteen
subscheme form a four-dimensional space. -/
theorem exists_cubicConfigurationGenericSixteen_cubicRestrictionKernel_finrank_four
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    ∃ x : Fin 4 → Γ(D.val.subscheme, ⊤),
      finrank Q.functionField (LinearMap.ker
        (homogeneousSectionRestriction (K := Q.functionField) x 3)) = 4 := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  have hgeneric :
      let Q := cubicConfigurationBase cubic hcubic 16
      let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
      let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
      letI : IsFinite pD := D.property.1
      letI := finiteSchemeCoefficientAlgebra pD
      ∃ (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3),
        LinearIndependent K frame ∧
        ∃ x : Fin 4 → Γ(D.val.subscheme, ⊤),
          Function.Surjective (eval₂Hom
            (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) ∧
          Function.Surjective (Fintype.linearCombination Q.functionField
            (fun j => MvPolynomial.eval₂
              (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x
              ((frame j).1.map a.hom))) := by
    exact exists_cubicConfigurationGenericSixteen_surjectiveCubicFrameEvaluation
      cubic hcubic hcubic_ne hcubic_prime a ha e
  obtain ⟨frame, hframe, x, hxsurj, hframeSurj⟩ := hgeneric
  have hr : ∀ j, ((frame j).1.map a.hom).IsHomogeneous 3 := by
    intro j
    exact (frame j).property.map a.hom
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 16 :=
    cubicConfigurationGenericSixteen_coefficientFinrank cubic hcubic a ha
  exact ⟨x, cubicSectionRestriction_kernel_finrank_eq_four_of_frameEvaluation
    x (fun j => (frame j).1.map a.hom) hr hA hframeSurj⟩


/-- On the generic length-sixteen scheme, the cubic vanishing system has
dimension three modulo the defining surface equation. -/
theorem exists_cubicConfigurationGenericSixteen_cubicVanishingModuloEquation_finrank_three_of_noCommon
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
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
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3)
    (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt
      cubic hcubic e frame hframe z) :
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
    let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (hpx : (cubic.map a.hom).eval₂
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0),
      cubicVanishingSectionsModuloEquationFinrank
        (cubic.map a.hom) (hcubic.map a.hom) x hpx = 3 := by
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
  have hdet : Nonempty (DetectingCubicSixteenFrameCoordinatesOnCubic
      Q.functionField Γ(D.val.subscheme, ⊤) (O.residueField z)
      (cubic.map a.hom) φ (fun j => (frame j).1.map a.hom)) := by
    exact exists_cubicConfigurationGenericSixteen_detectingCubicFrameCoordinatesOnCubic_of_noCommon
      cubic hcubic a ha z hz e frame hframe hno
  obtain ⟨d⟩ := hdet
  have hr : ∀ j, ((frame j).1.map a.hom).IsHomogeneous 3 := by
    intro j
    exact (frame j).property.map a.hom
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 16 :=
    cubicConfigurationGenericSixteen_coefficientFinrank cubic hcubic a ha
  exact ⟨d.data.x, d.cubicZero,
    d.vanishingModuloCubic_finrank_eq_three
      (cubic.map a.hom) (hcubic.map a.hom) hr hA⟩


/-- The generic length-sixteen subscheme has precisely three cubic
vanishing sections modulo the defining cubic, with no ordered-point
or incidence witness in the statement. -/
theorem exists_cubicConfigurationGenericSixteen_cubicVanishingModuloEquation_finrank_three
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (hpx : (cubic.map a.hom).eval₂
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0),
      cubicVanishingSectionsModuloEquationFinrank
        (cubic.map a.hom) (hcubic.map a.hom) x hpx = 3 := by
  dsimp only
  have hgeneric :
      let O := (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).left
      let Q₀ := (projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme
      let π := projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16
      let η := Q₀.fromSpecStalk (genericPoint Q₀)
        (IsLocalRing.closedPoint Q₀.functionField)
      ∃ (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
        (hframe : LinearIndependent K frame) (z : O),
        π z = η ∧
        HomogeneousSixteenNoCommonResidueFieldEquationAt
          cubic hcubic e frame hframe z := by
    exact exists_orderedPointOver_genericSixteen_with_noCommonCubicEquation
      cubic hcubic hcubic_ne hcubic_prime e
  obtain ⟨frame, hframe, z, hz, hno⟩ := hgeneric
  exact exists_cubicConfigurationGenericSixteen_cubicVanishingModuloEquation_finrank_three_of_noCommon
    cubic hcubic a ha z hz e frame hframe hno

end PfaffianDescent

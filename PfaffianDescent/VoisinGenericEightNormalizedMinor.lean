import PfaffianDescent.VoisinGenericEightSelectedMinor
/-! The selected generic minor comes from coordinates on the cubic. -/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective AllCharacteristics.UniversalHomogeneous
universe u
/-- Choose one normalized presentation for which the cubic vanishes and
the ordered quadratic evaluation has a unit minor. -/
theorem exists_cubicConfigurationGenericEight_normalizedUnitQuadraticMinor_of_noCommon
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    [Infinite (cubicConfigurationBase cubic hcubic 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
      cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (hno : QuadraticEightNoCommonResidueFieldEquationAt cubic hcubic z) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let p := cubic.map a.hom
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (ell : MvPolynomial (Fin 4) Q.functionField)
      (m : Fin 8 ↪ Monomials (Fin 4) 2),
      ell.IsHomogeneous 1 ∧
      ell.eval₂ (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0 ∧
      Function.Surjective (eval₂Hom
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) ∧
      Function.Surjective (homogeneousSectionRestriction (K := Q.functionField) x 2) ∧
      IsUnit (eightPointQuadraticEvaluationMinor m
        (fun i j => φ i (x j))).det := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let p := cubic.map a.hom
  let hp := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
  let hnormalized :=
    cubicConfigurationGenericEight_normalizedQuadraticPencilBasis_of_noCommon
      cubic hcubic a ha z hz hno
  let N := Classical.choice hnormalized
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 8 := by
    apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)
  have hquad : Function.Surjective
      (homogeneousSectionRestriction (K := Q.functionField) N.x 2) :=
    (quadric_degree_eight_restriction_surjective_iff_kernel_finrank_eq_two
      N.x hA).2 N.kernelFinrank
  have hspan := cubicConfigurationGenericEight_componentSpan_eq_top
    cubic hcubic a ha z hz
  have hminor := exists_unit_eightPointQuadraticEvaluationMinor_of_componentSpan
    φ N.x hquad hspan
  let m := Classical.choose hminor
  have hm := Classical.choose_spec hminor
  exact ⟨N.x, N.ell, m, N.ellHomogeneous, N.ellEvaluation,
    N.cubicEvaluation, N.evalSurjective, hquad, hm⟩

end PfaffianDescent

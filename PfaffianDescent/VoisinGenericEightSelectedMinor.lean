import PfaffianDescent.VoisinGenericEightComponentSpan
import PfaffianDescent.VoisinFiniteAlgebraQuadraticSplitKernel

/-! The actual generic eight-point algebra admits a selected unit quadratic minor. -/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective AllCharacteristics.UniversalHomogeneous
universe u
/-- Under the generic no-common-incidence condition, the actual finite
algebra admits quadratic coordinates with a selected unit evaluation minor. -/
theorem exists_cubicConfigurationGenericEight_unitQuadraticMinor_of_noCommon
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
      (m : Fin 8 ↪ Monomials (Fin 4) 2),
      Function.Surjective (homogeneousSectionRestriction (K := Q.functionField) x 2) ∧
      IsUnit (eightPointQuadraticEvaluationMinor m
        (fun i j => φ i (x j))).det := by
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
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
  let hcoord :=
    exists_cubicConfigurationGenericEight_quadraticRestriction_surjective_of_noCommon
      cubic hcubic a ha z hz hno
  let x := Classical.choose hcoord
  have hquad := (Classical.choose_spec hcoord).2
  have hspan :=
    cubicConfigurationGenericEight_componentSpan_eq_top cubic hcubic a ha z hz
  have hminor :=
    exists_unit_eightPointQuadraticEvaluationMinor_of_componentSpan
      φ x hquad hspan
  let m := Classical.choose hminor
  have hm := Classical.choose_spec hminor
  exact ⟨x, m, hquad, hm⟩

end PfaffianDescent

import PfaffianDescent.VoisinGenericEightVanishingPencilProjective
import PfaffianDescent.FiniteSubschemeCompleteIntersection

/-! The generic eight-point algebra embeds in its chosen cubic–quadric–quadric intersection. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

/-- A finite algebra embedded in a cubic--two-quadrics intersection over its
coefficient field, with its structure map fixed. -/
structure CubicQuadraticTripleEmbedding
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3) where
  q : Fin 2 → homogeneousSubmodule (Fin 4) F 2
  j : Spec (.of A) ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal
    p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2)
  closed : IsClosedImmersion j
  toBase_eq : j ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal
    p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2) =
    Spec.map (CommRingCat.ofHom (algebraMap F A))

/-- The same normalized coordinates used for the ordered projective comparison
give an actual closed immersion of the unordered generic eight-point algebra
into the triple intersection cut out by the cubic and its vanishing pencil. -/
theorem exists_cubicConfigurationGenericEight_tripleIntersectionEmbedding_of_noCommon
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
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    let p := cubic.map a.hom
    let hp := hcubic.map a.hom
    Nonempty (CubicQuadraticTripleEmbedding
      (A := Γ(D.val.subscheme, ⊤)) p hp) := by
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
  let p := cubic.map a.hom
  let hp := hcubic.map a.hom
  have hdata :=
    exists_cubicConfigurationGenericEight_normalizedUnitQuadraticMinor_of_noCommon
      cubic hcubic a ha z hz hno
  let x := Classical.choose hdata
  let h1 := Classical.choose_spec hdata
  let ell := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let m := Classical.choose h2
  let h3 := Classical.choose_spec h2
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 8 := by
    apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)
  have hpair := exists_rankEight_independentVanishingHomogeneousQuadrics x hA
  let q := Classical.choose hpair
  have hqzero := (Classical.choose_spec hpair).2
  obtain ⟨j, hj, hjbase⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2 x ell
      h3.1 h3.2.1 h3.2.2.2.1 h3.2.2.1
      (hqzero 0) (hqzero 1)
  exact ⟨⟨q, j, hj, hjbase⟩⟩

end PfaffianDescent

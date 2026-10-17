import PfaffianDescent.VoisinGenericEightTripleEmbedding
import PfaffianDescent.VoisinFiniteAlgebraPencilProjectiveOverBase

/-! The generic triple-intersection embedding and ordered projective comparison use one pencil. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

/-- The same cubic and quadratic pencil contain the finite algebra and give
the ordered projective base-change comparison. -/
structure CubicQuadraticTripleEmbeddedComparison
    {F A L : Type u} [Field F] [CommRing A] [Algebra F A]
    [Field L] [Algebra F L]
    (φ : Fin 8 → A →ₐ[F] L)
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3) where
  x : Fin 4 → A
  embedding : CubicQuadraticTripleEmbedding (A := A) p hp
  projectiveComparison : TripleProjectiveComparisonOverBase
    p (embedding.q 0).1 (embedding.q 1).1
    hp (embedding.q 0).2 (embedding.q 1).2
    (intrinsicEightPointTripleHomogeneousIdeal
      (p.map (algebraMap F L)) (hp.map (algebraMap F L))
      (fun i j => φ i (x j)))

/-- The actual generic eight-point algebra and the ordered projective
intersection are compared using exactly the pair of quadrics defining the
closed immersion. -/
theorem exists_cubicConfigurationGenericEight_embeddedProjectiveComparison_of_noCommon
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
    Nonempty (CubicQuadraticTripleEmbeddedComparison φ
      (cubic.map a.hom) (hcubic.map a.hom)) := by
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
  have hq := Classical.choose_spec hpair
  obtain ⟨j, hj, hjbase⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2 x ell
      h3.1 h3.2.1 h3.2.2.2.1 h3.2.2.1
      (hq.2 0) (hq.2 1)
  have hjoint := cubicConfigurationGenericEight_componentJointInjective_of_noCommon
    cubic hcubic a ha z hz hno
  let C := quadraticHomogeneousPair_intrinsicProjectiveComparisonOverBase
    φ hjoint x q hq.1 hq.2 m h3.2.2.2.2.2 p hp
  exact ⟨⟨x, ⟨q, j, hj, hjbase⟩, C⟩⟩

end PfaffianDescent

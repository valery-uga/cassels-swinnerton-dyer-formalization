import PfaffianDescent.VoisinGenericEightProjectiveComparison
/-! An ordered generic lift with the projective pullback comparison exists. -/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective AllCharacteristics.UniversalHomogeneous
universe u
/-- The generic unordered eight-point configuration admits an ordered lift
whose intrinsic intersection is the pullback of an unordered pencil family. -/
theorem exists_orderedGenericEight_intrinsicProjectiveBaseChangeIso
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
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
    : let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let π := projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8
    let U := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8).toScheme
    let η := U.fromSpecStalk (genericPoint U)
      (IsLocalRing.closedPoint U.functionField)
    ∃ z : O, ∃ hz : π z = η,
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
    let p := cubic.map a.hom
    let hp := hcubic.map a.hom
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (m : Fin 8 ↪ Monomials (Fin 4) 2)
      (q : Fin 2 → homogeneousSubmodule (Fin 4) Q.functionField 2),
      Nonempty (scheme (intrinsicEightPointTripleHomogeneousIdeal
        (p.map (algebraMap Q.functionField (O.residueField z)))
        (hp.map (algebraMap Q.functionField (O.residueField z)))
        (fun i j => φ i (x j))) ≅
      pullback (relativeTripleIntersectionToBase
        p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2)
        (Spec.map (CommRingCat.ofHom
          (algebraMap Q.functionField (O.residueField z))))) := by
  dsimp only
  obtain ⟨z, hz, hno⟩ :=
    exists_orderedPointOver_genericEight_with_noCommonQuadraticEightEquation
      cubic hcubic hcubic_ne hcubic_prime
  exact ⟨z, hz,
    exists_cubicConfigurationGenericEight_intrinsicProjectiveBaseChangeIso_of_noCommon
      cubic hcubic a ha z hz hno⟩

end PfaffianDescent

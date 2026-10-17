import PfaffianDescent.VoisinGenericEightNormalizedProjective
/-! A pair of quadrics vanishing on the generic eight-point algebra
realizes the projective pullback comparison. -/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective AllCharacteristics.UniversalHomogeneous
universe u
/-- One normalized presentation simultaneously retains cubic vanishing,
a vanishing quadratic pair, a unit minor, and the projective comparison. -/
theorem exists_cubicConfigurationGenericEight_normalizedVanishingPencilProjectiveIso_of_noCommon
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
    let p := cubic.map a.hom
    let hp := hcubic.map a.hom
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (ell : MvPolynomial (Fin 4) Q.functionField)
      (m : Fin 8 ↪ Monomials (Fin 4) 2)
      (q : Fin 2 → homogeneousSubmodule (Fin 4) Q.functionField 2),
      ell.IsHomogeneous 1 ∧
      ell.eval₂ (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0 ∧
      Function.Surjective (eval₂Hom
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) ∧
      Function.Surjective (homogeneousSectionRestriction (K := Q.functionField) x 2) ∧
      IsUnit (eightPointQuadraticEvaluationMinor m
        (fun i j => φ i (x j))).det ∧
      (∀ i : Fin 2, (q i).1.eval₂
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0) ∧
      Nonempty (scheme (intrinsicEightPointTripleHomogeneousIdeal
        (p.map (algebraMap Q.functionField (O.residueField z)))
        (hp.map (algebraMap Q.functionField (O.residueField z)))
        (fun i j => φ i (x j))) ≅
      pullback (relativeTripleIntersectionToBase
        p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2)
        (Spec.map (CommRingCat.ofHom
          (algebraMap Q.functionField (O.residueField z))))) := by
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
  have hnormalized :=
    exists_cubicConfigurationGenericEight_normalizedUnitQuadraticMinor_of_noCommon
      cubic hcubic a ha z hz hno
  let x := Classical.choose hnormalized
  let hE := Classical.choose_spec hnormalized
  let ell := Classical.choose hE
  let hM := Classical.choose_spec hE
  let m := Classical.choose hM
  have hd := Classical.choose_spec hM
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 8 := by
    apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)
  have hjoint := cubicConfigurationGenericEight_componentJointInjective_of_noCommon
    cubic hcubic a ha z hz hno
  have hpair := exists_rankEight_independentVanishingHomogeneousQuadrics x hA
  let q := Classical.choose hpair
  have hqzero := Classical.choose_spec hpair
  have hprojective : Nonempty (scheme (intrinsicEightPointTripleHomogeneousIdeal
        (p.map (algebraMap Q.functionField (O.residueField z)))
        (hp.map (algebraMap Q.functionField (O.residueField z)))
        (fun i j => φ i (x j))) ≅
      pullback (relativeTripleIntersectionToBase
        p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2)
        (Spec.map (CommRingCat.ofHom
          (algebraMap Q.functionField (O.residueField z))))) :=
    ⟨quadraticHomogeneousPair_intrinsicProjectiveBaseChangeIso
      φ hjoint x q hqzero.1 hqzero.2 m hd.2.2.2.2.2 p hp⟩
  exact ⟨x, ell, m, q, hd.1, hd.2.1, hd.2.2.1,
    hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2, hqzero.2, hprojective⟩

end PfaffianDescent

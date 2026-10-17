import PfaffianDescent.VoisinDegreeEightHilbertCriterion
import PfaffianDescent.VoisinDegreeEightFixedCurveScheme
import PfaffianDescent.VoisinGenericDegreeEightFixedCurveDichotomy

/-!
# The fixed divisor extracted from a normalized quadratic pencil

This file connects failure of regularity for the canonical basis of the
generic quadratic pencil directly to the scheme-theoretic fixed divisor used
in Voisin's all-or-none argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On a smooth cubic, failure of regularity for the canonical basis of a
normalized pencil produces a nonempty prime divisor contained in every
quadric of that pencil.  The associated prime is supplied directly by the
canonical-basis obstruction, so no coordinate-uniform no-common-curve
premise is needed. -/
theorem exists_degreeEightDivisorFixedSubschemeData_of_normalizedPencil_not_regular
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    [FiniteDimensional K Γ(D₈.val.subscheme, ⊤)]
    (d : NormalizedQuadraticPencilBasisData
      K Γ(D₈.val.subscheme, ⊤) p)
    (hnot : ¬ d.HasCanonicalRegularPair) :
    ∃ (q : MvPolynomial (Fin 4) K)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hCp : p ∈ C.toIdeal),
      DegreeEightDivisorFixedSubschemeData p hp D₈ d.x q C hCp := by
  let q := (quadraticVanishingPencilBasis d.x d.kernelFinrank 0).1.1
  have hq : q.IsHomogeneous 2 := (d.basisData 0).1
  have hqvan : q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) d.x = 0 :=
    (d.basisData 0).2
  have hq0 : q ≠ 0 := by
    intro hzero
    apply (quadraticVanishingPencilBasis_linearIndependent
      d.x d.kernelFinrank).ne_zero 0
    apply Subtype.ext
    apply Subtype.ext
    exact hzero
  have hpprime : Prime p := (Ideal.span_singleton_prime hne).mp
    (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne)
  have hrel : IsRelPrime p q :=
    isRelPrime_of_prime_homogeneous_degree_lt hp hq hpprime hq0 (by decide)
  obtain ⟨P, hP, _hq₁P, hcontains⟩ :=
    d.exists_associatedPrime_containing_pencil_of_not_regular hnot
  let C := cubicQuadricHomogeneousCore p q P
  have hminimal := quotientAssociatedPrime_mem_minimalPrimes_of_prime_cubic
    p q hp hq hpprime hrel P hP
  obtain ⟨hCprime, hCrel, _, hspan⟩ :=
    cubicQuadricHomogeneousCore_profile_of_associatedMinimal
      p q hp hq P hP hminimal
  have hCp : p ∈ C.toIdeal := hspan (Ideal.subset_span (by simp))
  have hW : homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) d.x 2 ≤
      Submodule.restrictScalars K C.toIdeal := by
    intro r hr
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨r,
        (mem_homogeneousVanishingPolynomialSubmodule_iff
          (K := K) (A := Γ(D₈.val.subscheme, ⊤))
          (sigma := Fin 4) d.x 2 r).mp hr |>.1⟩)
    exact hcontains r hr
  have hheight : C.toIdeal.height = 2 :=
    cubicQuadricHomogeneousCore_height_eq_two_of_associatedMinimal_of_smooth_cubic
      p q hp hne hq P hP hminimal hrel
  have hdivisor : (C.toIdeal.map (Ideal.Quotient.mk
      (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))))).height = 1 :=
    cubicQuadricHomogeneousCore_quotientByCubic_height_eq_one_of_associatedMinimal_of_smooth_cubic
      p q hp hne hq P hP hminimal hrel
  have hcomponent :=
    cubicQuadricHomogeneousCore_mem_minimalPrimes_span_pair_of_associatedMinimal
      p q hp hq P hP hminimal
  refine ⟨q, C, hCp, hq, hqvan, hq0, hrel, hCprime, hCrel,
    hheight, hdivisor, hcomponent, hspan,
    homogeneousPrime_Proj_nonempty C hCprime hCrel,
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp, ?_⟩
  intro r hrW
  have hr : r.IsHomogeneous 2 :=
    (mem_homogeneousVanishingPolynomialSubmodule_iff
      (K := K) (A := Γ(D₈.val.subscheme, ⊤))
      (sigma := Fin 4) d.x 2 r).mp hrW |>.1
  have hCr : r ∈ C.toIdeal := hW hrW
  exact ⟨hr, hCr,
    homogeneousFixedCurveToHypersurface_closedImmersion r hr C hCr⟩

/-- On the generic cubic, failure of canonical regularity produces the full
fixed-divisor dichotomy object directly.  The fixed divisor comes from the
canonical associated-prime witness, while generic irreducibility supplies
the all-or-none alternative for the rank-eight configuration. -/
theorem nonempty_genericDegreeEightFixedCurveDichotomyData_of_normalizedPencil_not_regular
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Q := cubicConfigurationBase p hp 8
      let p' := p.map a.hom
      let hp' := hp.map a.hom
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : IsFinite
          (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp') := Dη.property.1
      letI := finiteSchemeCoefficientAlgebra
        (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp')
      letI : Module.Finite Q.functionField Γ(Dη.val.subscheme, ⊤) :=
        finiteSchemeCoefficient_finite
          (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp')
      ∀ d : NormalizedQuadraticPencilBasisData
          Q.functionField Γ(Dη.val.subscheme, ⊤) p',
        ¬ d.HasCanonicalRegularPair →
          Nonempty (DegreeEightFixedCurveDichotomyData p' hp' Dη) := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 8 a
  have hpη0 : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  letI : IsFinite
      (Dη.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := Dη.property.1
  letI := finiteSchemeCoefficientAlgebra
    (Dη.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  haveI : Module.Finite B.functionField Γ(Dη.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (Dη.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  intro d hnot
  obtain ⟨q, C, hCp, hfixed⟩ :=
    exists_degreeEightDivisorFixedSubschemeData_of_normalizedPencil_not_regular
      (p.map a.hom) (hp.map a.hom) hpη0 Dη d hnot
  have hall := genericDegreeEightFixedCurve_all_or_none_of_smooth
    p hp hne D₈ a ha C hCp
  exact ⟨⟨d.x, q, C, hCp, d.evalSurjective, hfixed, hall⟩⟩

end PfaffianDescent

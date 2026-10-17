import PfaffianDescent.VoisinDegreeTenRestrictionKernelEtale
import PfaffianDescent.VoisinQuadraticRestrictionKernelUniversalFamily
import PfaffianDescent.VoisinDegreeTenResidualEnd

/-!
# Restriction-kernel endpoint for Voisin's degree-eight residual

This file joins the mixed cubic--quadric--quadric universal family to the
actual rank-eight finite datum.  Properness of the singular-member locus
selects an étale quadric over the ground field.  Since that intersection
contains the positive-rank datum, it is nonempty; the mixed-degree regularity
theorem then proves that the selected quadric is a non-zero-divisor modulo the
cubic and first quadric.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A normalized chart of the rank-eight datum on which the full quadratic
restriction kernel has a proper singular-member locus. -/
def DegreeEightQuadraticRestrictionKernelProperChart
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (z : CoordinateRing (equationIdeal p hp))
    (hz : z ∈ grading (equationIdeal p hp) 1)
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) s = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) he) z = 1),
    Function.Surjective
        (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
      linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
        D₈.val.subscheme.isoSpec.inv ≫ D₈.val.subschemeι ∧
      cubicTwoQuadricRestrictionKernelSingularParameterLocus
        p q hp hq x ≠ Set.univ

/-- The exact remaining quadratic geometric input permits the first quadric
and its normalized rank-eight chart to be chosen together. -/
def DegreeEightQuadraticRestrictionKernelProperPairExists
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
    IsRelPrime p q ∧
      DegreeEightQuadraticRestrictionKernelProperChart p q hp hq D₈

/-- The geometric content of the final quadratic choice, with the elementary
relative-primality condition removed.  It asks for a nonzero quadric through
the rank-eight datum whose complete restriction kernel has a proper
singular-member locus, while retaining the normalized chart of the actual
datum.  On a smooth cubic, homogeneity and the degree inequality prove that
this quadric is relatively prime to the cubic. -/
def DegreeEightQuadraticRestrictionKernelProperMemberExists
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (z : CoordinateRing (equationIdeal p hp))
    (hz : z ∈ grading (equationIdeal p hp) 1)
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) s = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) he) z = 1),
    Function.Surjective
        (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
        D₈.val.subscheme.isoSpec.inv ≫ D₈.val.subschemeι ∧
      ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧
        cubicTwoQuadricRestrictionKernelSingularParameterLocus
          p q hp hq x ≠ Set.univ

/-- For a smooth cubic, the proper-member condition already supplies the
previous proper-pair interface.  Primality of the smooth cubic equation and
the strict degree inequality `2 < 3` make every nonzero homogeneous quadric
in the condition relatively prime to the cubic. -/
theorem
    DegreeEightQuadraticRestrictionKernelProperPairExists.of_smooth_cubic
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hmember : DegreeEightQuadraticRestrictionKernelProperMemberExists
      p hp D₈) :
    DegreeEightQuadraticRestrictionKernelProperPairExists p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hpoint,
      q, hq, hqvan, hq0, hproper⟩ := hmember
  have hpprime : Prime p :=
    (Ideal.span_singleton_prime hp0).mp
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  have hrel : IsRelPrime p q :=
    isRelPrime_of_prime_homogeneous_degree_lt hp hq hpprime hq0 (by decide)
  exact ⟨q, hq, hrel, z, hz, x, he, hzOne,
    hxsurj, hqvan, hpoint, hproper⟩

/-- Properness of the actual quadratic restriction-kernel bad locus produces
the embedded regular transverse cubic--quadric--quadric intersection required
by Voisin's final residual construction. -/
theorem
    nonempty_degreeEightTransverseQuadricIntersectionEmbeddingData_of_restrictionKernelProperChart
    {K : Type u} [Field K] [Infinite K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hrel : IsRelPrime p q)
    (hproper : DegreeEightQuadraticRestrictionKernelProperChart
      p q hp hq D₈) :
    Nonempty (DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, hsing⟩ := hproper
  obtain ⟨r, hr, hrvan, _hrne, hetale⟩ :=
    exists_restrictionKernel_quadric_etale_of_singularParameterLocus_ne_univ
      p q hp hq x hsing
  let chart :=
    show
      ∃ (z : CoordinateRing (equationIdeal p hp))
        (hz : z ∈ grading (equationIdeal p hp) 1)
        (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
        (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
          (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) s = 0)
        (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
          (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) he) z = 1),
        Function.Surjective
            (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
          q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
          r.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
          linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
            D₈.val.subscheme.isoSpec.inv ≫ D₈.val.subschemeι
      from ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hrvan, hpoint⟩
  let j : D₈.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart
      p q r hp hq hr 8 D₈ chart
  have hD : Nonempty D₈.val.subscheme :=
    finiteSubschemeDatum_subscheme_nonempty_of_pos
      (hypersurfaceToBase p hp) D₈ (by norm_num)
  have hX : Nonempty
      (scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) :=
    Nonempty.map j hD
  have hregular : ∀ F : MvPolynomial (Fin 4) K,
      r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
    intro F hF
    exact tripleCompleteIntersection_third_regular_of_etale_of_nonempty_degrees
      p q r hp hq hr (by norm_num) (by norm_num) hetale hX F hF
  exact ⟨
    DegreeEightTransverseQuadricIntersectionEmbeddingData.ofNormalizedChart
      p q r hp hq hr D₈ hrel hregular chart hetale⟩

/-- The direct degree-eight endpoint: a proper restriction-kernel bad locus
gives the disjoint finite étale residual of degree four. -/
theorem
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_restrictionKernelProperChart
    {K : Type u} [Field K] [Infinite K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hp0 : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hrel : IsRelPrime p q)
    (hproper : DegreeEightQuadraticRestrictionKernelProperChart
      p q hp hq D₈) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  obtain ⟨T⟩ :=
    nonempty_degreeEightTransverseQuadricIntersectionEmbeddingData_of_restrictionKernelProperChart
      p q hp hq D₈ hrel hproper
  let R := degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
    p hp hp0 D₈ T
  exact ⟨R,
    degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_cycle_degree
      p hp hp0 D₈ T,
    degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_toBase_etale
      p hp hp0 D₈ T,
    degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
      p hp hp0 D₈ T⟩

/-- Choosing a first quadric together with a proper restriction-kernel bad
locus is sufficient for the complete degree-eight-to-four residual step. -/
theorem
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_restrictionKernelProperPair
    {K : Type u} [Field K] [Infinite K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hpair : DegreeEightQuadraticRestrictionKernelProperPairExists p hp D₈) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  obtain ⟨q, hq, hrel, hproper⟩ := hpair
  exact
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_restrictionKernelProperChart
      p q hp hq hp0 D₈ hrel hproper

/-- On a smooth cubic, the remaining degree-eight endpoint assumes only the
existence of a nonzero first quadric with proper restriction-kernel bad
locus.  Relative primality is derived rather than included as geometric
input. -/
theorem
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_restrictionKernelProperMember
    {K : Type u} [Field K] [Infinite K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hmember : DegreeEightQuadraticRestrictionKernelProperMemberExists
      p hp D₈) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  exact
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_restrictionKernelProperPair
      p hp hp0 D₈
        (.of_smooth_cubic p hp hp0 D₈ hmember)

end PfaffianDescent

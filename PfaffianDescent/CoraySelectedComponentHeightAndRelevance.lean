import PfaffianDescent.CoraySmoothCurveHilbert
import PfaffianDescent.CorayProjectiveIntersectionChartDimension
import PfaffianDescent.VoisinDegreeEightFixedCurveScheme

/-!
# Actual selected minimal component: codimension and projective relevance

The SAME original cubic/q minimal prime has height two. Both the upper
bound and the strict prime chain are derived from the actual equations.
Projective relevance follows from that height; it is not supplied as an
input. This establishes no component degree, Cartier, genus, Euler,
normalization-constant, or geometric-integrality conclusion.
SOURCE ONLY / UNVERIFIED. Root owns all compiler and audit checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual minimal component of the original smooth cubic/q has
homogeneous height two, with no height premise and no degree restriction. -/
theorem selectedProjectiveMinimalComponent_homogeneous_height_eq_two
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    C.toIdeal.height = 2 := by
  have hminimal : C.toIdeal ∈
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes := by
    simpa only [projectiveIntersectionIdeal_toIdeal] using hCmin
  have hheight := PfaffianDescent.homogeneousPrime_height_le_two_of_mem_minimalPrimes_span_pair
    p q C hminimal
  exact PfaffianDescent.homogeneousPrime_height_eq_two_of_span_pair_of_isRelPrime
    p q C (PfaffianDescent.principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
    hminimal.isPrime hminimal.le
    (isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot) hheight

/-- The SAME actual homogeneous minimal component is projectively relevant.
No point, irrelevance exclusion, genus, or integrality certificate is input. -/
theorem selectedProjectiveMinimalComponent_homogeneous_relevant
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C := by
  exact PfaffianDescent.homogeneousIdeal_relevant_of_height_le_two C
    (selectedProjectiveMinimalComponent_homogeneous_height_eq_two
      p q hp hp0 n hq hnot C hCmin).le

end PfaffianDescent.Coray

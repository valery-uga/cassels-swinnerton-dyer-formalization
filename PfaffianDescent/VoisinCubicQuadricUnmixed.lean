import PfaffianDescent.VoisinRegularLocalDepth
import PfaffianDescent.VoisinRegularSequenceCriteria
import PfaffianDescent.VoisinDegreeEightHomogeneousCurve
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Unmixed cubic--quadric intersections

The complete-intersection depth argument discharges the associated-prime
minimality premise in the degree-eight fixed-curve construction. In particular,
the selected quadric section need not be reduced or irreducible.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

/-- A prime cubic and a relatively-prime quadric cut out an unmixed complete
intersection, including when their intersection is nonreduced. -/
theorem quotientAssociatedPrime_mem_minimalPrimes_of_prime_cubic
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hpprime : Prime p) (hrel : IsRelPrime p q)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hP : P ∈ associatedPrimes
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    P ∈ minimalPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))) := by
  have hreg := cubic_quadric_isRegular_of_prime_of_isRelPrime p q hp hq hpprime hrel
  have hpair : Ideal.ofList [p, q] = Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
    simp only [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq, Ideal.span_insert]
  have h := regularRing_quotient_ofList_associatedPrime_mem_minimalPrimes
    (MvPolynomial (Fin 4) K) [p, q] hreg.toIsWeaklyRegular
  rw [hpair] at h
  exact h P hP

/-- Primality of the cubic supplies the previously explicit unmixedness
certificate for every admissible quadric. -/
theorem CubicQuadricQuotientAssociatedPrimesMinimal.of_prime_cubic
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hpprime : Prime p) :
    CubicQuadricQuotientAssociatedPrimesMinimal p := by
  intro q hq _ hrel P hP
  exact quotientAssociatedPrime_mem_minimalPrimes_of_prime_cubic p q hp hq hpprime hrel P hP

/-- Smoothness of the nonzero cubic suffices for the unmixedness input to
Voisin's fixed-curve argument. -/
theorem CubicQuadricQuotientAssociatedPrimesMinimal.of_smooth_cubic
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    CubicQuadricQuotientAssociatedPrimesMinimal p :=
  .of_prime_cubic p hp ((Ideal.span_singleton_prime hp0).mp
    (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0))

end PfaffianDescent

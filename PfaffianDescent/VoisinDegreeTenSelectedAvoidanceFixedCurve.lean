import PfaffianDescent.VoisinDegreeEightFixedCurveScheme
import PfaffianDescent.VoisinCubicQuadricUnmixed

/-! # The actual fixed curve of a failed selected cubic system

For two relatively prime cubics on a smooth cubic surface, the quotient is
an unmixed complete intersection. If its actual cubic vanishing system fails
associated-component avoidance, the offending associated prime gives a
relevant homogeneous prime of height two containing the whole system.
This constructs the fixed curve required by the generic geometric argument.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- A relatively prime cubic pair is unmixed, including when its projective
intersection is nonreduced. -/
theorem voisinDegreeTenSelectedAvoidance_associatedPrime_minimal
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hpprime : Prime p) (hrel : IsRelPrime p q)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _)))
    (hP : P ∈ associatedPrimes
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _))) :
    P ∈ minimalPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _)) := by
  have hreg := homogeneous_pair_isRegular_of_prime_of_isRelPrime
    hp hq (by decide) (by decide) hpprime hrel
  have hpair : Ideal.ofList [p, q] = Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
    simp only [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq, Ideal.span_insert]
  have h := regularRing_quotient_ofList_associatedPrime_mem_minimalPrimes
    (MvPolynomial (Fin 4) K) [p, q] hreg.toIsWeaklyRegular
  rw [hpair] at h
  exact h P hP

/-- The homogeneous prime obtained from a selected cubic associated
component contains both equations and is a genuine projective curve. -/
theorem voisinDegreeTenSelectedAvoidance_homogeneousCore_profile
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hpprime : Prime p) (hrel : IsRelPrime p q)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _)))
    (hP : P ∈ associatedPrimes
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _))) :
    (cubicQuadricHomogeneousCore p q P).toIdeal.IsPrime ∧
      ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤
        cubicQuadricHomogeneousCore p q P ∧
      (cubicQuadricHomogeneousCore p q P).toIdeal.height = 2 ∧
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤
        (cubicQuadricHomogeneousCore p q P).toIdeal := by
  let C := cubicQuadricHomogeneousCore p q P
  have hminimal := voisinDegreeTenSelectedAvoidance_associatedPrime_minimal
    p q hp hq hpprime hrel P hP
  have hheight : C.toIdeal.height ≤ 2 :=
    cubicQuadricHomogeneousCore_height_le_two_of_quotientMinimal p q P hminimal
  have hprime : C.toIdeal.IsPrime :=
    cubicQuadricHomogeneousCore_isPrime_of_associatedPrime p q P hP
  have hspanI := (associatedPrimeComap_isPrime_and_contains_span p q P hP).1
  have hpC : p ∈ C.toIdeal := Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    (SetLike.isHomogeneousElem_coe ⟨p, hp⟩) (hspanI (Ideal.subset_span (by simp)))
  have hqC : q ∈ C.toIdeal := Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    (SetLike.isHomogeneousElem_coe ⟨q, hq⟩) (hspanI (Ideal.subset_span (by simp)))
  have hspan : Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal := by
    apply Ideal.span_le.mpr
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact hpC
    · exact hqC
  exact ⟨hprime, homogeneousIdeal_relevant_of_height_le_two C hheight,
    homogeneousPrime_height_eq_two_of_span_pair_of_isRelPrime p q C
      ((Ideal.span_singleton_prime hpprime.ne_zero).mpr hpprime) hprime hspan hrel hheight,
    hspan⟩

set_option backward.isDefEq.respectTransparency false in
/-- Failure of the literal cubic-kernel avoidance at the selected first
cubic constructs an actual nonempty prime fixed curve in the surface. -/
theorem voisinDegreeTenSelectedAvoidance_exists_fixedCurve_of_failure
    {K A : Type u} [Field K] [Infinite K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : Fin 4 → A) (q : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3) (hrel : IsRelPrime p q)
    (hfailure : ¬ ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _))
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _)),
      ∃ r ∈ homogeneousVanishingPolynomialSubmodule
        (K := K) (A := A) (sigma := Fin 4) x 3,
        Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) r ∉ P) :
    ∃ (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
      (hCp : p ∈ C.toIdeal),
      C.toIdeal.IsPrime ∧
      ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C ∧
      C.toIdeal.height = 2 ∧
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
      homogeneousVanishingPolynomialSubmodule
          (K := K) (A := A) (sigma := Fin 4) x 3 ≤
        Submodule.restrictScalars K C.toIdeal ∧
      Nonempty (scheme C) ∧
      IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  classical
  push_neg at hfailure
  obtain ⟨P, hP, hcontains⟩ := hfailure
  let C := cubicQuadricHomogeneousCore p q P
  have hpprime : Prime p := (Ideal.span_singleton_prime hp0).mp
    (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  obtain ⟨hprime, hCrel, hheight, hspan⟩ :=
    voisinDegreeTenSelectedAvoidance_homogeneousCore_profile p q hp hq hpprime hrel P hP
  have hCp : p ∈ C.toIdeal := hspan (Ideal.subset_span (by simp))
  have hW : homogeneousVanishingPolynomialSubmodule
      (K := K) (A := A) (sigma := Fin 4) x 3 ≤
      Submodule.restrictScalars K C.toIdeal := by
    intro r hr
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨r,
        (mem_homogeneousVanishingPolynomialSubmodule_iff
          (K := K) (A := A) (sigma := Fin 4) x 3 r).mp hr |>.1⟩)
    exact hcontains r hr
  exact ⟨C, hCp, hprime, hCrel, hheight, hspan, hW,
    homogeneousPrime_scheme_nonempty C hprime hCrel,
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp⟩

end PfaffianDescent

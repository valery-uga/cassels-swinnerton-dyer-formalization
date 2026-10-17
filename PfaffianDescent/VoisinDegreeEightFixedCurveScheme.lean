import PfaffianDescent.VoisinDegreeEightHomogeneousCurve
import PfaffianDescent.VoisinCubicQuadricUnmixed
import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.ProjectiveClosedPointCoordinates
import PfaffianDescent.AlgebraVectorHomogeneous
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The fixed-curve subscheme in Voisin's degree-eight argument

The homogeneous prime obtained from a failed no-common-curve condition is not
merely a pointwise obstruction: it defines a closed projective subscheme of
the cubic surface.  This file records that scheme-theoretic bridge, leaving
the later task of spreading these curves in a family separate.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-two system through a finite homogeneous datum has trivial
intersection with the principal ideal of a cubic equation.  This is the
polynomial realization of quadratic sections on the cubic surface required
by the generic fixed/moving incidence argument. -/
theorem homogeneousVanishingQuadrics_separate_cubic_equation
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → A) :
    ∀ r ∈ homogeneousVanishingPolynomialSubmodule
      (K := K) (A := A) (sigma := Fin 4) x 2,
      r ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → r = 0 := by
  intro r hr hrspan
  have hrhom : r.IsHomogeneous 2 :=
    (mem_homogeneousVanishingPolynomialSubmodule_iff
      (K := K) (A := A) (sigma := Fin 4) x 2 r).mp hr |>.1
  have hspanPair : r ∈ Ideal.span ({p, (0 : MvPolynomial (Fin 4) K)} : Set _) := by
    simpa using hrspan
  obtain ⟨a, ha⟩ := homogeneous_mem_span_succ_degree_pair_eq_smul
    (d := 2) hp (MvPolynomial.isHomogeneous_zero (Fin 4) K 2)
      hrhom hspanPair
  rw [ha, smul_zero]

/-- A homogeneous ideal contained in a minimal component of a cubic--quadric
intersection has height at most two.  The extracted homogeneous core is an
instance of this statement. -/
theorem homogeneousIdeal_height_le_two_of_le_minimalPrime_span_pair
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hminimal : I ∈ (Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K))).minimalPrimes)
    (hC : C.toIdeal ≤ I) :
    C.toIdeal.height ≤ 2 := by
  exact (Ideal.height_mono hC).trans
    (ideal_height_le_two_of_mem_minimalPrimes_span_pair p q I hminimal)

/-- A prime component containing a relatively-prime cubic--quadric pair is
genuinely codimension two as soon as the usual two-generator upper bound is
available.  This removes the possible divisor (height-one) ambiguity from the
fixed curve extracted on a smooth cubic surface. -/
theorem homogeneousPrime_height_eq_two_of_span_pair_of_isRelPrime
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hCprime : C.toIdeal.IsPrime)
    (hspan : Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal)
    (hrel : IsRelPrime p q)
    (hheight : C.toIdeal.height ≤ 2) : C.toIdeal.height = 2 := by
  let P : Ideal (MvPolynomial (Fin 4) K) := Ideal.span ({p} : Set _)
  letI : P.IsPrime := by simpa only [P] using hpprime
  letI : C.toIdeal.IsPrime := hCprime
  have hpC : P ≤ C.toIdeal := by
    dsimp only [P]
    apply Ideal.span_le.mpr
    rintro r rfl
    exact hspan (Ideal.subset_span (by simp))
  have hqC : q ∈ C.toIdeal := hspan (Ideal.subset_span (by simp))
  have hp0 : p ≠ 0 := by
    intro hp0
    have hqunit : IsUnit q := isRelPrime_zero_left.mp (by simpa [hp0] using hrel)
    exact hCprime.ne_top (C.toIdeal.eq_top_of_isUnit_mem hqC hqunit)
  have hPCne : P ≠ C.toIdeal := by
    intro hPC
    have hqP : q ∈ P := by rw [hPC]; exact hqC
    have hpdivq : p ∣ q := by
      simpa only [P] using (Ideal.mem_span_singleton.mp hqP)
    have hpunit : IsUnit p := hrel (d := p) dvd_rfl hpdivq
    apply hpprime.ne_top
    rw [Ideal.span_singleton_eq_top]
    exact hpunit
  have hbotP : (⊥ : Ideal (MvPolynomial (Fin 4) K)) < P := by
    apply bot_lt_iff_ne_bot.mpr
    simpa only [P] using (Ideal.span_singleton_eq_bot.not.mpr hp0)
  have hPC : P < C.toIdeal := lt_of_le_of_ne hpC hPCne
  have hPheight : (1 : ℕ∞) ≤ P.height := by
    simpa only [Ideal.height_bot, zero_add] using
      (Ideal.height_add_one_le_of_lt_of_isPrime hbotP)
  have hCheight : P.height + 1 ≤ C.toIdeal.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hPC
  have htwo : (2 : ℕ∞) ≤ C.toIdeal.height := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ P.height + 1 := by
        simpa only [add_comm] using add_le_add_right hPheight (1 : ℕ∞)
      _ ≤ C.toIdeal.height := hCheight
  exact le_antisymm hheight htwo

/-- The homogeneous ideal underlying a quotient associated component. -/
noncomputable def cubicQuadricHomogeneousCore
    {K : Type u} [Field K] (p q : MvPolynomial (Fin 4) K)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
  (P.comap (Ideal.Quotient.mk (Ideal.span ({p, q} : Set
    (MvPolynomial (Fin 4) K))))).homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin 4) K)

theorem cubicQuadricHomogeneousCore_isPrime_of_associatedPrime
    {K : Type u} [Field K] [Infinite K] (p q : MvPolynomial (Fin 4) K)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hP : P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    (cubicQuadricHomogeneousCore p q P).toIdeal.IsPrime := by
  exact (associatedPrimeComap_isPrime_and_contains_span p q P hP).2.homogeneousCore

theorem cubicQuadricHomogeneousCore_height_le_two_of_quotientMinimal
    {K : Type u} [Field K] (p q : MvPolynomial (Fin 4) K)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hP : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes) :
    (cubicQuadricHomogeneousCore p q P).toIdeal.height ≤ 2 := by
  apply homogeneousIdeal_height_le_two_of_le_minimalPrime_span_pair p q
    (P.comap (Ideal.Quotient.mk (Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K)))))
  · exact comap_mem_minimalPrimes_span_pair_of_quotient_mem_minimalPrimes p q P hP
  · exact Ideal.toIdeal_homogeneousCore_le
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) _

theorem cubicQuadricHomogeneousCore_profile_of_associatedMinimal
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hassoc : P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hminimal : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes) :
    (cubicQuadricHomogeneousCore p q P).toIdeal.IsPrime ∧
    ¬ HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤
        cubicQuadricHomogeneousCore p q P ∧
    (cubicQuadricHomogeneousCore p q P).toIdeal.height ≤ 2 ∧
    Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤
      (cubicQuadricHomogeneousCore p q P).toIdeal := by
  let I := P.comap (Ideal.Quotient.mk (Ideal.span
    ({p, q} : Set (MvPolynomial (Fin 4) K))))
  let C := cubicQuadricHomogeneousCore p q P
  have hspanI := (associatedPrimeComap_isPrime_and_contains_span p q P hassoc).1
  have hprime := cubicQuadricHomogeneousCore_isPrime_of_associatedPrime p q P hassoc
  have hpC : p ∈ C.toIdeal := Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    (SetLike.isHomogeneousElem_coe ⟨p, hp⟩) (hspanI (Ideal.subset_span (by simp)))
  have hqC : q ∈ C.toIdeal := Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    (SetLike.isHomogeneousElem_coe ⟨q, hq⟩) (hspanI (Ideal.subset_span (by simp)))
  refine ⟨hprime, ?_, cubicQuadricHomogeneousCore_height_le_two_of_quotientMinimal p q P hminimal, ?_⟩
  · exact homogeneousIdeal_relevant_of_height_le_two C
      (cubicQuadricHomogeneousCore_height_le_two_of_quotientMinimal p q P hminimal)
  · rw [Ideal.span_le]
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact hpC
    · exact hqC

/-- For a quotient-minimal associated component, taking the homogeneous core
loses no equations: the core is the ambient minimal prime itself.  Thus the
projective fixed curve is represented by the actual cubic--quadric component,
rather than by a smaller auxiliary homogeneous ideal. -/
theorem cubicQuadricHomogeneousCore_eq_associatedPrimeComap_of_associatedMinimal
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hassoc : P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hminimal : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes) :
    (cubicQuadricHomogeneousCore p q P).toIdeal =
      P.comap (Ideal.Quotient.mk (Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K)))) := by
  let C := cubicQuadricHomogeneousCore p q P
  let I := P.comap (Ideal.Quotient.mk (Ideal.span
    ({p, q} : Set (MvPolynomial (Fin 4) K))))
  obtain ⟨hCprime, _, _, hspan⟩ :=
    cubicQuadricHomogeneousCore_profile_of_associatedMinimal
      p q hp hq P hassoc hminimal
  have hminimalI : I ∈ (Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) K))).minimalPrimes :=
    comap_mem_minimalPrimes_span_pair_of_quotient_mem_minimalPrimes
      p q P hminimal
  have hCI : C.toIdeal ≤ I := by
    exact Ideal.toIdeal_homogeneousCore_le
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) _
  apply le_antisymm hCI
  exact hminimalI.2 ⟨hCprime, hspan⟩ hCI

/-- The homogeneous core of a quotient-minimal associated component is a
minimal prime of the cubic--quadric ideal itself. -/
theorem cubicQuadricHomogeneousCore_mem_minimalPrimes_span_pair_of_associatedMinimal
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hassoc : P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hminimal : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes) :
    (cubicQuadricHomogeneousCore p q P).toIdeal ∈
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes := by
  rw [cubicQuadricHomogeneousCore_eq_associatedPrimeComap_of_associatedMinimal
    p q hp hq P hassoc hminimal]
  exact comap_mem_minimalPrimes_span_pair_of_quotient_mem_minimalPrimes
    p q P hminimal

/-- After passing to the cubic coordinate ring, an extracted minimal
cubic--quadric component has height at most one.  This is the algebraic
height bound underlying its interpretation as a divisor on the cubic. -/
theorem cubicQuadricHomogeneousCore_quotientByCubic_height_le_one_of_associatedMinimal
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hassoc : P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hminimal : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes) :
    ((cubicQuadricHomogeneousCore p q P).toIdeal.map
      (Ideal.Quotient.mk (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))))).height ≤ 1 := by
  apply Ideal.map_height_le_one_of_mem_minimalPrimes
  rw [← Ideal.span_insert]
  exact cubicQuadricHomogeneousCore_mem_minimalPrimes_span_pair_of_associatedMinimal
    p q hp hq P hassoc hminimal

/-- On a prime cubic, a relatively-prime quadric makes the extracted
component a genuine height-one prime in the cubic coordinate ring.  Thus it
has exactly the algebraic codimension of a divisor on the cubic. -/
theorem cubicQuadricHomogeneousCore_quotientByCubic_height_eq_one_of_associatedMinimal
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hassoc : P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hminimal : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hrel : IsRelPrime p q) :
    ((cubicQuadricHomogeneousCore p q P).toIdeal.map
      (Ideal.Quotient.mk (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))))).height = 1 := by
  let I : Ideal (MvPolynomial (Fin 4) K) := Ideal.span ({p} : Set _)
  let f := Ideal.Quotient.mk I
  let C := cubicQuadricHomogeneousCore p q P
  letI : I.IsPrime := by simpa only [I] using hpprime
  letI : IsDomain (MvPolynomial (Fin 4) K ⧸ I) := Ideal.Quotient.isDomain I
  have hqC : q ∈ C.toIdeal := by
    obtain ⟨_, _, _, hspan⟩ :=
      cubicQuadricHomogeneousCore_profile_of_associatedMinimal p q hp hq P hassoc hminimal
    exact hspan (Ideal.subset_span (by simp))
  have hq0 : f q ≠ 0 := by
    intro hqzero
    have hqI : q ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hqzero
    have hpdivq : p ∣ q := by
      simpa only [I] using (Ideal.mem_span_singleton.mp hqI)
    have hpunit : IsUnit p := hrel (d := p) dvd_rfl hpdivq
    exact hpprime.ne_top (by rw [Ideal.span_singleton_eq_top]; exact hpunit)
  apply le_antisymm
  · simpa only [I, f, C] using
      cubicQuadricHomogeneousCore_quotientByCubic_height_le_one_of_associatedMinimal
        p q hp hq P hassoc hminimal
  · apply le_trans (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hq0))
    apply Ideal.height_mono
    rw [Ideal.span_le]
    intro r hr
    simp only [Set.mem_singleton_iff] at hr
    subst r
    exact Ideal.mem_map_of_mem f hqC

/-- On a prime cubic, the homogeneous associated component extracted from a
relatively-prime quadric section has exact height two. -/
theorem cubicQuadricHomogeneousCore_height_eq_two_of_associatedMinimal_of_prime_cubic
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hassoc : P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hminimal : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hrel : IsRelPrime p q) :
    (cubicQuadricHomogeneousCore p q P).toIdeal.height = 2 := by
  obtain ⟨hCprime, _, hheight, hspan⟩ :=
    cubicQuadricHomogeneousCore_profile_of_associatedMinimal
      p q hp hq P hassoc hminimal
  exact homogeneousPrime_height_eq_two_of_span_pair_of_isRelPrime
    p q (cubicQuadricHomogeneousCore p q P) hpprime hCprime hspan hrel hheight

/-- The exact-height conclusion in the smooth-cubic setting of Voisin's
degree-eight argument. -/
theorem cubicQuadricHomogeneousCore_height_eq_two_of_associatedMinimal_of_smooth_cubic
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (hq : q.IsHomogeneous 2)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hassoc : P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hminimal : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes)
    (hrel : IsRelPrime p q) :
    (cubicQuadricHomogeneousCore p q P).toIdeal.height = 2 := by
  apply cubicQuadricHomogeneousCore_height_eq_two_of_associatedMinimal_of_prime_cubic
    p q hp hq P hassoc hminimal
  · exact principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne
  · exact hrel

/-- In Voisin's smooth-cubic setting, the minimal component is a height-one
prime in the cubic coordinate ring, i.e. an algebraic divisor on the cubic. -/
theorem cubicQuadricHomogeneousCore_quotientByCubic_height_eq_one_of_associatedMinimal_of_smooth_cubic
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (hq : q.IsHomogeneous 2)
    (P : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hassoc : P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K))))
    (hminimal : P ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K ⧸ Ideal.span
      ({p, q} : Set (MvPolynomial (Fin 4) K)))).minimalPrimes)
    (hrel : IsRelPrime p q) :
    ((cubicQuadricHomogeneousCore p q P).toIdeal.map
      (Ideal.Quotient.mk (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))))).height = 1 := by
  apply cubicQuadricHomogeneousCore_quotientByCubic_height_eq_one_of_associatedMinimal
    p q hp hq P hassoc hminimal
  · exact principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne
  · exact hrel

/-- A homogeneous ideal containing a homogeneous equation contains its
principal homogeneous equation ideal. -/
theorem equationIdeal_le_homogeneousIdeal_of_mem_of_isHomogeneous
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K} {d : ℕ}
    {C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hp : p.IsHomogeneous d) (hCp : p ∈ C.toIdeal) :
    (equationIdeal p hp).toIdeal ≤ C.toIdeal := by
  apply Ideal.span_le.mpr
  rintro x rfl
  exact hCp

/-- A homogeneous ideal containing the cubic equation contains its equation
ideal. -/
theorem equationIdeal_le_homogeneousIdeal_of_mem
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K}
    {C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hp : p.IsHomogeneous 3) (hCp : p ∈ C.toIdeal) :
    (equationIdeal p hp).toIdeal ≤ C.toIdeal :=
  equationIdeal_le_homogeneousIdeal_of_mem_of_isHomogeneous hp hCp

/-- The projective subscheme defined by a homogeneous ideal containing a
homogeneous equation, regarded as a subscheme of that equation's
hypersurface.  This is the scheme-theoretic meaning of a common component
of a homogeneous linear system. -/
noncomputable def homogeneousFixedCurveToHypersurface
    {K : Type u} [Field K] (r : MvPolynomial (Fin 4) K) {d : ℕ}
    (hr : r.IsHomogeneous d)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCr : r ∈ C.toIdeal) :
    scheme C ⟶ hypersurface r hr :=
  schemeQuotientMap (equationIdeal r hr) C
    (equationIdeal_le_homogeneousIdeal_of_mem_of_isHomogeneous hr hCr)

/-- A homogeneous component contained in a hypersurface is a closed
projective subscheme of that hypersurface. -/
theorem homogeneousFixedCurveToHypersurface_closedImmersion
    {K : Type u} [Field K] (r : MvPolynomial (Fin 4) K) {d : ℕ}
    (hr : r.IsHomogeneous d)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCr : r ∈ C.toIdeal) :
    IsClosedImmersion (homogeneousFixedCurveToHypersurface r hr C hCr) := by
  exact schemeQuotientMap_closedImmersion (equationIdeal r hr) C
    (equationIdeal_le_homogeneousIdeal_of_mem_of_isHomogeneous hr hCr)

/-- Every realization of the fixed component inside a hypersurface has the
same ambient projective map.  This identifies the component simultaneously
inside all members of a homogeneous linear system. -/
theorem homogeneousFixedCurveToHypersurface_comp_hypersurfaceToAmbient
    {K : Type u} [Field K] (r : MvPolynomial (Fin 4) K) {d : ℕ}
    (hr : r.IsHomogeneous d)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCr : r ∈ C.toIdeal) :
    homogeneousFixedCurveToHypersurface r hr C hCr ≫ hypersurfaceToAmbient r hr =
      quotientProjMap C := by
  unfold homogeneousFixedCurveToHypersurface hypersurfaceToAmbient quotientProjMap
    schemeQuotientMap
  let F := quotientGradedRingHom (equationIdeal r hr)
  let G := gradedQuotientMap (equationIdeal r hr) C
    (equationIdeal_le_homogeneousIdeal_of_mem_of_isHomogeneous hr hCr)
  have hGF : G.comp F = quotientGradedRingHom C := by
    ext x
    rfl
  have hcomp := Proj.map_comp F G
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal r hr))
    (gradedSurjective_irrelevant_le G
      (gradedQuotientMap_surjective (equationIdeal r hr) C
        (equationIdeal_le_homogeneousIdeal_of_mem_of_isHomogeneous hr hCr)))
  calc
    _ = Proj.map G (gradedSurjective_irrelevant_le G
        (gradedQuotientMap_surjective (equationIdeal r hr) C
          (equationIdeal_le_homogeneousIdeal_of_mem_of_isHomogeneous hr hCr))) ≫
        Proj.map F (irrelevant_le_map_quotientGradedRingHom (equationIdeal r hr)) := by
      rfl
    _ = Proj.map (G.comp F) (HomogeneousIdeal.irrelevant_le_map_comp
        (irrelevant_le_map_quotientGradedRingHom (equationIdeal r hr))
        (gradedSurjective_irrelevant_le G
          (gradedQuotientMap_surjective (equationIdeal r hr) C
            (equationIdeal_le_homogeneousIdeal_of_mem_of_isHomogeneous hr hCr)))) :=
      hcomp.symm
    _ = _ := by cases hGF; rfl

/-- The projective closed subscheme defined by a homogeneous ideal containing
the cubic equation, regarded as a subscheme of the cubic surface. -/
noncomputable def homogeneousFixedCurveToCubic
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal) :
    scheme C ⟶ hypersurface p hp :=
  schemeQuotientMap (equationIdeal p hp) C
    (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)

/-- The fixed-curve morphism is a genuine closed immersion into the cubic
surface. -/
theorem homogeneousFixedCurveToCubic_closedImmersion
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal) :
    IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  exact schemeQuotientMap_closedImmersion (equationIdeal p hp) C
    (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)

/-- The fixed subscheme has the expected ambient projective realization. -/
theorem homogeneousFixedCurveToCubic_comp_hypersurfaceToAmbient
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal) :
    homogeneousFixedCurveToCubic p hp C hCp ≫ hypersurfaceToAmbient p hp =
      quotientProjMap C := by
  unfold homogeneousFixedCurveToCubic hypersurfaceToAmbient quotientProjMap schemeQuotientMap
  let F := quotientGradedRingHom (equationIdeal p hp)
  let G := gradedQuotientMap (equationIdeal p hp) C
    (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)
  have hGF : G.comp F = quotientGradedRingHom C := by
    ext x
    rfl
  have hcomp := Proj.map_comp F G
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp))
    (gradedSurjective_irrelevant_le G
      (gradedQuotientMap_surjective (equationIdeal p hp) C
        (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)))
  calc
    _ = Proj.map G (gradedSurjective_irrelevant_le G
        (gradedQuotientMap_surjective (equationIdeal p hp) C
          (equationIdeal_le_homogeneousIdeal_of_mem hp hCp))) ≫
        Proj.map F (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp)) := by rfl
    _ = Proj.map (G.comp F) (HomogeneousIdeal.irrelevant_le_map_comp
        (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp))
        (gradedSurjective_irrelevant_le G
          (gradedQuotientMap_surjective (equationIdeal p hp) C
            (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)))) := hcomp.symm
    _ = _ := by cases hGF; rfl

/-- A relevant homogeneous prime has a nonempty projective quotient: the
zero ideal of its domain quotient is a relevant homogeneous prime. -/
noncomputable def homogeneousPrimeQuotientProjectivePoint
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C) :
    ProjectiveSpectrum (grading C) := by
  letI : IsDomain (CoordinateRing C) :=
    (Ideal.Quotient.isDomain_iff_prime C.toIdeal).mpr hprime
  refine ⟨⊥, Ideal.isPrime_bot, ?_⟩
  intro hbot
  apply hrelevant
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn a ha
  have hq : Ideal.Quotient.mk C.toIdeal a = 0 := by
    apply hbot
    exact HomogeneousIdeal.mem_irrelevant_of_mem (grading C) hn
      ⟨a, ha, rfl⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mp hq

/-- The projective scheme cut out by a relevant homogeneous prime is nonempty. -/
theorem homogeneousPrime_Proj_nonempty
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C) :
    Nonempty (ProjectiveSpectrum (grading C)) :=
  ⟨homogeneousPrimeQuotientProjectivePoint C hprime hrelevant⟩

/-- The relevant prime component has an actual point of its projective scheme,
not only a point of its homogeneous prime spectrum. -/
theorem homogeneousPrime_scheme_nonempty
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C) :
    Nonempty (scheme C) := by
  change Nonempty (ProjectiveSpectrum (grading C))
  exact homogeneousPrime_Proj_nonempty C hprime hrelevant

/-- Over an algebraically closed field, a relevant homogeneous prime has an
actual rational projective point.  Compactness supplies a closed point of the
nonempty projective scheme, and the algebraically-closed-point equivalence
turns that closed point into a section over the ground field. -/
theorem homogeneousPrime_scheme_has_rationalPoint
    {K : Type u} [Field K] [IsAlgClosed K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C) :
    ∃ q : Spec (.of K) ⟶ scheme C, q ≫ toBase C = 𝟙 _ := by
  letI : Nonempty (scheme C) :=
    homogeneousPrime_scheme_nonempty C hprime hrelevant
  letI : CompactSpace (scheme C) :=
    QuasiCompact.compactSpace_of_compactSpace (toBase C)
  obtain ⟨x, -, hx⟩ :=
    (isClosed_univ : IsClosed (Set.univ : Set (scheme C))).exists_closed_singleton
      Set.univ_nonempty
  exact ⟨pointOfClosedPoint (toBase C) x hx,
    pointOfClosedPoint_comp (toBase C) x hx⟩

/-- Coordinate form of the preceding rational-point theorem.  It produces a
nonzero normalized affine-cone representative annihilating the entire fixed
curve ideal; this is the input used by the two-point separation argument. -/
theorem homogeneousPrime_exists_normalized_coordinates
    {K : Type u} [Field K] [IsAlgClosed K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C) :
    ∃ (j : Fin 4) (x : Fin 4 → K), x j = 1 ∧
      Function.Surjective (eval₂Hom (algebraMap K K) x) ∧
      ∀ f ∈ C.toIdeal, f.eval₂ (algebraMap K K) x = 0 := by
  obtain ⟨q, hq⟩ := homogeneousPrime_scheme_has_rationalPoint C hprime hrelevant
  letI : IsClosedImmersion q := isClosedImmersion_of_comp_eq_id (toBase C) q hq
  have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) =
      𝟙 (Spec (.of K)) := by
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  exact closed_projective_point_generating_coordinates C q (hq.trans hid.symm)

/-- A coordinate section of a homogeneous prime has a homogeneous minimal
prime above it.  The proof takes an ordinary minimal prime and observes that
its homogeneous core is the same prime by minimality. -/
theorem homogeneousPrime_exists_minimal_coordinate_section
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime) (j : Fin 4) :
    ∃ P : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K),
      P.toIdeal.IsPrime ∧ C ≤ P ∧ X j ∈ P.toIdeal ∧
      P.toIdeal ∈ (C.toIdeal ⊔ Ideal.span ({X j} : Set _)).minimalPrimes := by
  let D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    ⟨Ideal.span ({X j} : Set (MvPolynomial (Fin 4) K)),
      Ideal.homogeneous_span _ _ (by
        intro f hf
        simp only [Set.mem_singleton_iff] at hf
        subst f
        exact SetLike.isHomogeneousElem_coe ⟨X j, isHomogeneous_X K j⟩)⟩
  let J := C ⊔ D
  have hJle : J ≤ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) := by
    apply sup_le
    · exact homogeneousIdeal_le_irrelevant_of_ne_top C hCprime.ne_top
    · intro f hf
      change f ∈ Ideal.span ({X j} : Set (MvPolynomial (Fin 4) K)) at hf
      refine Ideal.span_le.mpr ?_ hf
      rintro _ rfl
      exact HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
        (isHomogeneous_X K j)
  have hJproper : J.toIdeal ≠ ⊤ := by
    apply ne_top_of_le_ne_top (RingHom.ker_ne_top
      (GradedRing.projZeroRingHom
        (MvPolynomial.homogeneousSubmodule (Fin 4) K)))
    exact (show J.toIdeal ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 4) K)).toIdeal from hJle)
  obtain ⟨P₀, hP₀⟩ := Ideal.nonempty_minimalPrimes hJproper
  let P := P₀.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  have hJP : J ≤ P := by
    exact (Ideal.homogeneousCore.gc _ J P₀).mp hP₀.1.2
  have hPcore : P.toIdeal = P₀ := by
    apply le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
    exact hP₀.2 ⟨hP₀.isPrime.homogeneousCore,
      show J.toIdeal ≤ P.toIdeal from hJP⟩
      (Ideal.toIdeal_homogeneousCore_le _ _)
  refine ⟨P, hP₀.isPrime.homogeneousCore, ?_, ?_, ?_⟩
  · exact le_trans le_sup_left hJP
  · exact (le_trans le_sup_right hJP)
      (Ideal.subset_span (Set.mem_singleton _))
  · simpa [J, D, hPcore] using hP₀

/-- A surjective ring map preserves strict containment between ideals that
contain its kernel. -/
lemma ideal_map_lt_map_of_surjective_of_ker_le
    {R S F : Type*} [CommRing R] [CommRing S]
    [FunLike F R S] [RingHomClass F R S]
    (f : F) (hf : Function.Surjective f) {I J : Ideal R}
    (hker : RingHom.ker f ≤ I) (h : I < J) :
    I.map f < J.map f := by
  apply lt_of_le_of_ne (Ideal.map_mono h.le)
  intro heq
  apply h.ne
  have hc := congrArg (Ideal.comap f) heq
  rw [Ideal.comap_map_of_surjective f hf,
    Ideal.comap_map_of_surjective f hf,
    ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr hker,
    sup_eq_left.mpr (hker.trans h.le)] at hc
  exact hc

/-- A height-two homogeneous prime curve in projective three-space has a
relevant prime hyperplane section avoiding any chosen point normalized in
the cutting coordinate.  If the section prime were irrelevant, the chosen
point ideal would give two strict prime steps in the quotient by the curve,
contradicting the relative principal-ideal height bound. -/
theorem homogeneousPrime_exists_relevant_coordinate_section
    {K : Type u} [Field K] [Infinite K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime) (hCheight : C.toIdeal.height = 2)
    (j : Fin 4) (x : Fin 4 → K) (hxj : x j = 1)
    (hzero : ∀ f ∈ C.toIdeal, f.eval₂ (algebraMap K K) x = 0) :
    ∃ P : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K),
      P.toIdeal.IsPrime ∧ C ≤ P ∧ X j ∈ P.toIdeal ∧
      (¬ HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ P) ∧
      P.toIdeal ∈ (C.toIdeal ⊔ Ideal.span ({X j} : Set _)).minimalPrimes := by
  obtain ⟨P, hPprime, hCP, hXj, hPminimal⟩ :=
    homogeneousPrime_exists_minimal_coordinate_section C hCprime j
  refine ⟨P, hPprime, hCP, hXj, ?_, hPminimal⟩
  intro hirrP
  let Q := algebraVectorHomogeneousIdeal (K := K) x
  have hx0 : x ≠ 0 := by
    intro hx
    have := congrFun hx j
    simp [hxj] at this
  have hCQ : C ≤ Q :=
    homogeneousIdeal_le_algebraVectorHomogeneousIdeal_of_forall_eval_zero C x hzero
  have hQheight : (3 : ℕ∞) ≤ Q.toIdeal.height := by
    change (3 : ℕ∞) ≤ (vectorLineIdeal x).toIdeal.height
    exact three_le_height_vectorLineIdeal_of_eq_one x j hxj
  have hCQne : C ≠ Q := by
    intro h
    have hbad : (3 : ℕ∞) ≤ 2 := by
      rw [← hCheight, h]
      exact hQheight
    norm_num at hbad
  have hCQlt : C < Q := lt_of_le_of_ne hCQ hCQne
  have hQirr : Q < HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    algebraVectorHomogeneousIdeal_lt_irrelevant_of_ne_zero x hx0
  have hPirrel : P ≤ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    homogeneousIdeal_le_irrelevant_of_ne_top P hPprime.ne_top
  have hPeq : P = HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    le_antisymm hPirrel hirrP
  have hQP : Q < P := by simpa [hPeq] using hQirr
  let f := Ideal.Quotient.mk C.toIdeal
  have hkerC : RingHom.ker f ≤ C.toIdeal := by
    simpa only [f, Ideal.mk_ker] using (le_refl C.toIdeal)
  have hmapCQ : C.toIdeal.map f < Q.toIdeal.map f :=
    ideal_map_lt_map_of_surjective_of_ker_le f
      Ideal.Quotient.mk_surjective hkerC hCQlt
  have hmapQP : Q.toIdeal.map f < P.toIdeal.map f :=
    ideal_map_lt_map_of_surjective_of_ker_le f
      Ideal.Quotient.mk_surjective (hkerC.trans hCQ) hQP
  letI : C.toIdeal.IsPrime := hCprime
  letI : Q.toIdeal.IsPrime := by
    change (vectorLineIdeal x).toIdeal.IsPrime
    infer_instance
  letI : P.toIdeal.IsPrime := hPprime
  letI : (C.toIdeal.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerC
  letI : (Q.toIdeal.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hkerC.trans hCQ)
  letI : (P.toIdeal.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hkerC.trans hCP)
  have hQone : (1 : ℕ∞) ≤ (Q.toIdeal.map f).height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hmapCQ
    simpa [f, Ideal.map_quotient_self, Ideal.height_bot] using h
  have hPtwo : (2 : ℕ∞) ≤ (P.toIdeal.map f).height := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (Q.toIdeal.map f).height + 1 := by
        simpa [add_comm] using add_le_add_left hQone 1
      _ ≤ (P.toIdeal.map f).height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hmapQP
  have hPle : (P.toIdeal.map f).height ≤ 1 :=
    homogeneousPrime_hyperplaneSection_quotient_height_le_one C P j hPminimal
  have hbad : (2 : ℕ∞) ≤ 1 := hPtwo.trans hPle
  norm_num at hbad

/-- A relevant prime lying over the fixed-curve ideal and containing a
coordinate hyperplane supplies a second point of the curve, projectively
distinct from a point normalized in that coordinate.  The remaining
hyperplane-section task is therefore purely the construction of such a
height-three relevant prime. -/
theorem homogeneousPrime_extension_exists_distinct_normalized_coordinates
    {K : Type u} [Field K] [IsAlgClosed K]
    (C P : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCP : C ≤ P) (j : Fin 4) (hXj : X j ∈ P.toIdeal)
    (hprime : P.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ P)
    (x : Fin 4 → K) (hxj : x j = 1) :
    ∃ (k : Fin 4) (y : Fin 4 → K), y k = 1 ∧
      (∀ f ∈ C.toIdeal, f.eval₂ (algebraMap K K) y = 0) ∧
      ∀ a : K, y ≠ a • x := by
  obtain ⟨k, y, hyk, -, hyP⟩ :=
    homogeneousPrime_exists_normalized_coordinates P hprime hrelevant
  have hyj : y j = 0 := by
    have := hyP (X j) hXj
    simpa [Algebra.algebraMap_self] using this
  refine ⟨k, y, hyk, ?_, ?_⟩
  · intro f hf
    exact hyP f (hCP hf)
  · intro a hya
    have haj : a = 0 := by
      have hcoord := congrFun hya j
      simpa [hyj, hxj] using hcoord.symm
    subst a
    have hyzero : y = 0 := by simpa using hya
    have hcoord := congrFun hyzero k
    simpa [hyk] using hcoord

/-- Every relevant height-two homogeneous prime in projective three-space
contains two projectively distinct rational points over an algebraically
closed field, presented by normalized affine-cone coordinates. -/
theorem homogeneousPrime_exists_two_distinct_normalized_coordinates
    {K : Type u} [Field K] [IsAlgClosed K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C)
    (hheight : C.toIdeal.height = 2) :
    ∃ (j : Fin 4) (x : Fin 4 → K) (k : Fin 4) (y : Fin 4 → K),
      x j = 1 ∧
      (∀ f ∈ C.toIdeal, f.eval₂ (algebraMap K K) x = 0) ∧
      y k = 1 ∧
      (∀ f ∈ C.toIdeal, f.eval₂ (algebraMap K K) y = 0) ∧
      ∀ a : K, y ≠ a • x := by
  obtain ⟨j, x, hxj, -, hxC⟩ :=
    homogeneousPrime_exists_normalized_coordinates C hprime hrelevant
  obtain ⟨P, hPprime, hCP, hXj, hPrelevant, -⟩ :=
    homogeneousPrime_exists_relevant_coordinate_section
      C hprime hheight j x hxj hxC
  obtain ⟨k, y, hyk, hyC, hdistinct⟩ :=
    homogeneousPrime_extension_exists_distinct_normalized_coordinates
      C P hCP j hXj hPprime hPrelevant x hxj
  exact ⟨j, x, k, y, hxj, hxC, hyk, hyC, hdistinct⟩

/-- If the cubic--quadric quotient has no embedded associated components,
failure of the degree-eight no-common-curve condition yields a relevant
height-at-most-two projective fixed subscheme of the cubic surface. -/
theorem degreeEight_exists_heightTwoFixedSubscheme_of_not_noCommonCurveComponent
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hunmixed : CubicQuadricQuotientAssociatedPrimesMinimal p) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 →
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 → q ≠ 0 → IsRelPrime p q →
        ∃ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
          (hCp : p ∈ C.toIdeal), C.toIdeal.IsPrime ∧
          ¬ HomogeneousIdeal.irrelevant
              (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C ∧
          C.toIdeal.height ≤ 2 ∧
          Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
          homogeneousVanishingPolynomialSubmodule
              (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
            Submodule.restrictScalars K C.toIdeal ∧
          Nonempty (ProjectiveSpectrum (grading C)) ∧
          IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hwitness⟩ :=
    degreeEight_exists_associatedPrime_commonCurveWitness_of_not_noCommonCurveComponent
      p hp D₈ hcommon
  refine ⟨x, hx, ?_⟩
  intro q hq hqvan hq0 hrel
  obtain ⟨P, hP, hcontains⟩ := hwitness q hq hqvan hq0 hrel
  let C := cubicQuadricHomogeneousCore p q P
  obtain ⟨hprime, hCrel, hheight, hspan⟩ :=
    cubicQuadricHomogeneousCore_profile_of_associatedMinimal p q hp hq P hP
      (hunmixed q hq hq0 hrel P hP)
  have hCp : p ∈ C.toIdeal := hspan (Ideal.subset_span (by simp))
  have hW : homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
      Submodule.restrictScalars K C.toIdeal := by
    intro r hr
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨r,
        (mem_homogeneousVanishingPolynomialSubmodule_iff
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 r).mp hr |>.1⟩)
    exact hcontains r hr
  exact ⟨C, hCp, hprime, hCrel, hheight, hspan, hW,
    homogeneousPrime_Proj_nonempty C hprime hCrel,
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp⟩

/-- A reduced cubic--quadric quotient supplies the unmixedness required by
the height-two fixed-subsheme bridge.  This is the version ready for a
geometric reducedness argument for the selected quadratic system. -/
theorem degreeEight_exists_heightTwoFixedSubscheme_of_not_noCommonCurveComponent_of_isReduced
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hreduced : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 → q ≠ 0 →
      IsRelPrime p q → IsReduced (MvPolynomial (Fin 4) K ⧸ Ideal.span
        ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 →
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 → q ≠ 0 → IsRelPrime p q →
        ∃ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
          (hCp : p ∈ C.toIdeal), C.toIdeal.IsPrime ∧
          ¬ HomogeneousIdeal.irrelevant
              (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C ∧
          C.toIdeal.height ≤ 2 ∧
          Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
          homogeneousVanishingPolynomialSubmodule
              (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
            Submodule.restrictScalars K C.toIdeal ∧
          Nonempty (ProjectiveSpectrum (grading C)) ∧
          IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  exact degreeEight_exists_heightTwoFixedSubscheme_of_not_noCommonCurveComponent
    p hp D₈ hcommon
    (CubicQuadricQuotientAssociatedPrimesMinimal.of_isReduced p hreduced)

/-- One reduced cubic--quadric member through the failed degree-eight system
is enough to extract the fixed projective curve.  Such a member may still be
reducible, so this hypothesis is compatible with Voisin's fixed-plus-moving
decomposition. -/
theorem degreeEight_exists_heightTwoFixedSubscheme_of_not_noCommonCurveComponent_of_reducedSection
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hreducedSection :
      letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
      letI := finiteSchemeCoefficientAlgebra
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
        ∃ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 ∧
          q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧ q ≠ 0 ∧
          IsRelPrime p q ∧
          IsReduced (MvPolynomial (Fin 4) K ⧸ Ideal.span
            ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
      (q : MvPolynomial (Fin 4) K)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hCp : p ∈ C.toIdeal),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      q.IsHomogeneous 2 ∧
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧ q ≠ 0 ∧ IsRelPrime p q ∧
      C.toIdeal.IsPrime ∧
      ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C ∧
      C.toIdeal.height ≤ 2 ∧
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
      homogeneousVanishingPolynomialSubmodule
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
        Submodule.restrictScalars K C.toIdeal ∧
      Nonempty (ProjectiveSpectrum (grading C)) ∧
      IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hwitness⟩ :=
    degreeEight_exists_associatedPrime_commonCurveWitness_of_not_noCommonCurveComponent
      p hp D₈ hcommon
  obtain ⟨q, hq, hqvan, hq0, hrel, hIreduced⟩ := hreducedSection x hx
  obtain ⟨P, hP, hcontains⟩ := hwitness q hq hqvan hq0 hrel
  let C := cubicQuadricHomogeneousCore p q P
  have hminimal := quotientAssociatedPrime_mem_minimalPrimes_of_span_pair_isReduced
    p q P hIreduced hP
  obtain ⟨hCprime, hCrel, hheight, hspan⟩ :=
    cubicQuadricHomogeneousCore_profile_of_associatedMinimal p q hp hq P hP hminimal
  have hCp : p ∈ C.toIdeal := hspan (Ideal.subset_span (by simp))
  have hW : homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
      Submodule.restrictScalars K C.toIdeal := by
    intro r hr
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨r,
        (mem_homogeneousVanishingPolynomialSubmodule_iff
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 r).mp hr |>.1⟩)
    exact hcontains r hr
  exact ⟨x, q, C, hCp, hx, hq, hqvan, hq0, hrel, hCprime, hCrel, hheight, hspan, hW,
    homogeneousPrime_Proj_nonempty C hCprime hCrel,
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp⟩


section

variable {K : Type u} [Field K] [Infinite K]

/-- Failure of Voisin's degree-eight no-common-curve condition gives an
actual homogeneous projective fixed subscheme of the cubic surface for every
admissible first quadric.  Its ideal contains the full quadratic system
through the datum.  Projective relevance and the proof that these subschemes
spread in divisor families remain separate geometric tasks. -/
theorem degreeEight_exists_fixedSubschemeClosedImmersion_of_not_noCommonCurveComponent
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ∀ (q : MvPolynomial (Fin 4) K) (_hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
        q ≠ 0 → IsRelPrime p q →
        ∃ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
          (hCp : p ∈ C.toIdeal), C.toIdeal.IsPrime ∧
          Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
          homogeneousVanishingPolynomialSubmodule
              (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
            Submodule.restrictScalars K C.toIdeal ∧
          IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hcurve⟩ :=
    degreeEight_exists_homogeneousPrimeCurveIdealWitness_of_not_noCommonCurveComponent
      p hp D₈ hcommon
  refine ⟨x, hx, ?_⟩
  intro q hq hqvan hq0 hrel
  obtain ⟨C, hprime, hspan, hW⟩ := hcurve q hq hqvan hq0 hrel
  have hCp : p ∈ C.toIdeal :=
    hspan (Ideal.subset_span (by simp))
  exact ⟨C, hCp, hprime, hspan, hW,
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp⟩

/-- With the available relevance control, the fixed subscheme obtained from
the obstruction has a relevant prime homogeneous ideal.  This retains the
precise nonemptiness condition needed to regard it as a projective curve
candidate, rather than discarding it when passing to the closed immersion. -/
theorem degreeEight_exists_relevantFixedSubschemeClosedImmersion_of_not_noCommonCurveComponent
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hrelevant : DegreeEightHomogeneousCurveWitnessesRelevant p hp D₈) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ∀ (q : MvPolynomial (Fin 4) K) (_hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
        q ≠ 0 → IsRelPrime p q →
        ∃ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
          (hCp : p ∈ C.toIdeal), C.toIdeal.IsPrime ∧
          ¬ HomogeneousIdeal.irrelevant
              (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C ∧
          Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
          homogeneousVanishingPolynomialSubmodule
              (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
            Submodule.restrictScalars K C.toIdeal ∧
          IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hcurve⟩ :=
    degreeEight_exists_homogeneousPrimeCurveIdealWitness_of_not_noCommonCurveComponent
      p hp D₈ hcommon
  refine ⟨x, hx, ?_⟩
  intro q hq hqvan hq0 hrel
  obtain ⟨C, hprime, hspan, hW⟩ := hcurve q hq hqvan hq0 hrel
  have hCp : p ∈ C.toIdeal :=
    hspan (Ideal.subset_span (by simp))
  have hCrel : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C :=
    hrelevant x hx q hq hqvan hq0 hrel C hprime hspan hW
  exact ⟨C, hCp, hprime, hCrel, hspan, hW,
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp⟩


/-- In the smooth-cubic setting of Voisin's degree-eight argument, one
reduced cubic--quadric member through a failed quadratic system produces an
actual codimension-two projective fixed subscheme.  The equality of heights
rules out the spurious divisor alternative before the later spreading-to-a-
family argument. -/
theorem degreeEight_exists_exactHeightTwoFixedSubscheme_of_not_noCommonCurveComponent_of_reducedSection_on_smoothCubic
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hreducedSection :
      letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
      letI := finiteSchemeCoefficientAlgebra
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
        ∃ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 ∧
          q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧ q ≠ 0 ∧
          IsRelPrime p q ∧
          IsReduced (MvPolynomial (Fin 4) K ⧸ Ideal.span
            ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
      (q : MvPolynomial (Fin 4) K)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hCp : p ∈ C.toIdeal),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      q.IsHomogeneous 2 ∧
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧ q ≠ 0 ∧ IsRelPrime p q ∧
      C.toIdeal.IsPrime ∧
      ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C ∧
      C.toIdeal.height = 2 ∧
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
      homogeneousVanishingPolynomialSubmodule
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
        Submodule.restrictScalars K C.toIdeal ∧
      Nonempty (ProjectiveSpectrum (grading C)) ∧
      IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, q, C, hCp, hx, hq, hqvan, hq0, hrel, hCprime, hCrel,
    hheight, hspan, hW, hnonempty, himm⟩ :=
    degreeEight_exists_heightTwoFixedSubscheme_of_not_noCommonCurveComponent_of_reducedSection
      p hp D₈ hcommon hreducedSection
  have hheightEq : C.toIdeal.height = 2 :=
    homogeneousPrime_height_eq_two_of_span_pair_of_isRelPrime p q C
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne)
      hCprime hspan hrel hheight
  exact ⟨x, q, C, hCp, hx, hq, hqvan, hq0, hrel, hCprime, hCrel,
    hheightEq, hspan, hW, hnonempty, himm⟩

/-- In the smooth degree-eight setting, a reduced selected member turns a
failed no-common-curve condition into a nonempty fixed projective subscheme
whose ideal is codimension two in projective space and codimension one in the
cubic coordinate ring.  The latter is the concrete divisor conclusion needed
before the fixed/moving-family argument. -/
theorem degreeEight_exists_divisorFixedSubscheme_of_not_noCommonCurveComponent_of_reducedSection_on_smoothCubic
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hreducedSection :
      letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
      letI := finiteSchemeCoefficientAlgebra
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
        ∃ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 ∧
          q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧ q ≠ 0 ∧
          IsRelPrime p q ∧
          IsReduced (MvPolynomial (Fin 4) K ⧸ Ideal.span
            ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
      (q : MvPolynomial (Fin 4) K)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hCp : p ∈ C.toIdeal),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      q.IsHomogeneous 2 ∧
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧ q ≠ 0 ∧ IsRelPrime p q ∧
      C.toIdeal.IsPrime ∧
      ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C ∧
      C.toIdeal.height = 2 ∧
      ((C.toIdeal.map (Ideal.Quotient.mk
        (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))))).height = 1) ∧
      C.toIdeal ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes ∧
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
      homogeneousVanishingPolynomialSubmodule
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
        Submodule.restrictScalars K C.toIdeal ∧
      Nonempty (ProjectiveSpectrum (grading C)) ∧
      IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hwitness⟩ :=
    degreeEight_exists_associatedPrime_commonCurveWitness_of_not_noCommonCurveComponent
      p hp D₈ hcommon
  obtain ⟨q, hq, hqvan, hq0, hrel, hIreduced⟩ := hreducedSection x hx
  obtain ⟨P, hP, hcontains⟩ := hwitness q hq hqvan hq0 hrel
  let C := cubicQuadricHomogeneousCore p q P
  have hminimal := quotientAssociatedPrime_mem_minimalPrimes_of_span_pair_isReduced
    p q P hIreduced hP
  obtain ⟨hCprime, hCrel, hheight, hspan⟩ :=
    cubicQuadricHomogeneousCore_profile_of_associatedMinimal p q hp hq P hP hminimal
  have hCp : p ∈ C.toIdeal := hspan (Ideal.subset_span (by simp))
  have hW : homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
      Submodule.restrictScalars K C.toIdeal := by
    intro r hr
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨r,
        (mem_homogeneousVanishingPolynomialSubmodule_iff
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 r).mp hr |>.1⟩)
    exact hcontains r hr
  have hheightEq : C.toIdeal.height = 2 :=
    cubicQuadricHomogeneousCore_height_eq_two_of_associatedMinimal_of_smooth_cubic
      p q hp hne hq P hP hminimal hrel
  have hdivisor : (C.toIdeal.map (Ideal.Quotient.mk
      (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))))).height = 1 :=
    cubicQuadricHomogeneousCore_quotientByCubic_height_eq_one_of_associatedMinimal_of_smooth_cubic
      p q hp hne hq P hP hminimal hrel
  have hcomponent : C.toIdeal ∈
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes :=
    cubicQuadricHomogeneousCore_mem_minimalPrimes_span_pair_of_associatedMinimal
      p q hp hq P hP hminimal
  exact ⟨x, q, C, hCp, hx, hq, hqvan, hq0, hrel, hCprime, hCrel,
    hheightEq, hdivisor, hcomponent, hspan, hW,
    homogeneousPrime_Proj_nonempty C hCprime hCrel,
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp⟩

/-- The complete scheme-theoretic profile of the fixed divisor extracted
from a failed degree-eight quadratic system.  The final clause says that the
same projective divisor is a closed subscheme of every quadric in the full
vanishing system, so it is a literal common fixed component rather than only
an ideal-theoretic containment. -/
def DegreeEightDivisorFixedSubschemeData
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal) : Prop :=
  q.IsHomogeneous 2 ∧
  q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧ q ≠ 0 ∧ IsRelPrime p q ∧
  C.toIdeal.IsPrime ∧
  ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C ∧
  C.toIdeal.height = 2 ∧
  (C.toIdeal.map (Ideal.Quotient.mk
    (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))))).height = 1 ∧
  C.toIdeal ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes ∧
  Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal ∧
  Nonempty (ProjectiveSpectrum (grading C)) ∧
  IsClosedImmersion (homogeneousFixedCurveToCubic p hp C hCp) ∧
  ∀ r ∈ homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2,
    ∃ (hr : r.IsHomogeneous 2) (hCr : r ∈ C.toIdeal),
      IsClosedImmersion (homogeneousFixedCurveToHypersurface r hr C hCr)

/-- In Voisin's smooth degree-eight situation, failure of the no-common-curve
condition and one reduced cubic--quadric member produce a nonempty divisor on
the cubic that is scheme-theoretically contained in every quadric through the
finite datum. -/
theorem exists_degreeEightDivisorFixedSubschemeData_of_not_noCommonCurveComponent_of_reducedSection_on_smoothCubic
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈)
    (hreducedSection :
      letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
      letI := finiteSchemeCoefficientAlgebra
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
        ∃ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 ∧
          q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧ q ≠ 0 ∧
          IsRelPrime p q ∧
          IsReduced (MvPolynomial (Fin 4) K ⧸ Ideal.span
            ({p, q} : Set (MvPolynomial (Fin 4) K)))) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
      (q : MvPolynomial (Fin 4) K)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hCp : p ∈ C.toIdeal),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, q, C, hCp, hx, hq, hqvan, hq0, hrel, hCprime, hCrel,
    hheight, hdivisor, hcomponent, hspan, hW, hnonempty, himm⟩ :=
    degreeEight_exists_divisorFixedSubscheme_of_not_noCommonCurveComponent_of_reducedSection_on_smoothCubic
      p hp hne D₈ hcommon hreducedSection
  refine ⟨x, q, C, hCp, hx, hq, hqvan, hq0, hrel, hCprime, hCrel,
    hheight, hdivisor, hcomponent, hspan, hnonempty, himm, ?_⟩
  intro r hrW
  have hr : r.IsHomogeneous 2 :=
    (mem_homogeneousVanishingPolynomialSubmodule_iff
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 r).mp hrW |>.1
  have hCr : r ∈ C.toIdeal := hW hrW
  exact ⟨hr, hCr,
    homogeneousFixedCurveToHypersurface_closedImmersion r hr C hCr⟩

/-- On a smooth cubic, failure of the degree-eight no-common-curve condition
produces a nonempty common prime divisor. Complete-intersection unmixedness
supplies the associated-prime minimality; no reduced-section hypothesis is
needed. The generic fixed/moving-family argument remains a separate step. -/
theorem exists_degreeEightDivisorFixedSubschemeData_of_not_noCommonCurveComponent_on_smoothCubic
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcommon : ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
      (q : MvPolynomial (Fin 4) K)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hCp : p ∈ C.toIdeal),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hwitness⟩ :=
    degreeEight_exists_associatedPrime_commonCurveWitness_of_not_noCommonCurveComponent
      p hp D₈ hcommon
  have hsections : 2 ≤ Module.finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) := by
    apply quadric_degree_eight_vanishing_sections_finrank x
    apply (finiteSchemeCoefficient_finrank
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D₈.property.2.2.2 (IsLocalRing.closedPoint K)
  have hpprime : Prime p := (Ideal.span_singleton_prime hne).mp
    (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne)
  obtain ⟨q, hq, hqvan, hq0, hrel⟩ :=
    exists_quadric_section_data_isRelPrime_of_prime_cubic p hp hpprime x hsections
  obtain ⟨P, hP, hcontains⟩ := hwitness q hq hqvan hq0 hrel
  let C := cubicQuadricHomogeneousCore p q P
  have hminimal := quotientAssociatedPrime_mem_minimalPrimes_of_prime_cubic
    p q hp hq hpprime hrel P hP
  obtain ⟨hCprime, hCrel, _, hspan⟩ :=
    cubicQuadricHomogeneousCore_profile_of_associatedMinimal p q hp hq P hP hminimal
  have hCp : p ∈ C.toIdeal := hspan (Ideal.subset_span (by simp))
  have hW : homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
      Submodule.restrictScalars K C.toIdeal := by
    intro r hr
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (SetLike.isHomogeneousElem_coe ⟨r,
        (mem_homogeneousVanishingPolynomialSubmodule_iff
          (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 r).mp hr |>.1⟩)
    exact hcontains r hr
  have hheight : C.toIdeal.height = 2 :=
    cubicQuadricHomogeneousCore_height_eq_two_of_associatedMinimal_of_smooth_cubic
      p q hp hne hq P hP hminimal hrel
  have hdivisor : (C.toIdeal.map (Ideal.Quotient.mk
      (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))))).height = 1 :=
    cubicQuadricHomogeneousCore_quotientByCubic_height_eq_one_of_associatedMinimal_of_smooth_cubic
      p q hp hne hq P hP hminimal hrel
  have hcomponent := cubicQuadricHomogeneousCore_mem_minimalPrimes_span_pair_of_associatedMinimal
    p q hp hq P hP hminimal
  refine ⟨x, q, C, hCp, hx, hq, hqvan, hq0, hrel, hCprime, hCrel,
    hheight, hdivisor, hcomponent, hspan,
    homogeneousPrime_Proj_nonempty C hCprime hCrel,
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp, ?_⟩
  intro r hrW
  have hr : r.IsHomogeneous 2 :=
    (mem_homogeneousVanishingPolynomialSubmodule_iff
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 r).mp hrW |>.1
  have hCr : r ∈ C.toIdeal := hW hrW
  exact ⟨hr, hCr, homogeneousFixedCurveToHypersurface_closedImmersion r hr C hCr⟩


end

end PfaffianDescent

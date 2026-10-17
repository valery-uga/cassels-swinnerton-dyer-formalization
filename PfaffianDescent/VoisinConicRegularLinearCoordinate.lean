import PfaffianDescent.VoisinRegularSequenceCriteria
import PfaffianDescent.HomogeneousProjection
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import PfaffianDescent.ProjectiveIdealCancellation

/-!
# A regular projective coordinate for a plane conic

A nonzero quadratic in three variables cannot be divisible by all three
coordinate variables. Since each coordinate is prime, at least one is
relatively prime to the quadratic. This elementary fact is a component of
the saturation proof for possibly reducible plane conics.
-/

namespace PfaffianDescent

open MvPolynomial

universe u

/-- One standard coordinate is relatively prime to any nonzero homogeneous
quadratic in three variables. -/
theorem exists_coordinate_relprime_homogeneous_quadratic
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0) :
    ∃ i : Fin 3, IsRelPrime (X i : MvPolynomial (Fin 3) K) q := by
  by_contra h
  push Not at h
  have h0 : (X 0 : MvPolynomial (Fin 3) K) ∣ q := by
    by_contra hn
    exact (h 0) (isRelPrime_of_prime_not_dvd (X_prime (i := (0 : Fin 3)) (R := K)) hn)
  have h1 : (X 1 : MvPolynomial (Fin 3) K) ∣ q := by
    by_contra hn
    exact (h 1) (isRelPrime_of_prime_not_dvd (X_prime (i := (1 : Fin 3)) (R := K)) hn)
  have h2 : (X 2 : MvPolynomial (Fin 3) K) ∣ q := by
    by_contra hn
    exact (h 2) (isRelPrime_of_prime_not_dvd (X_prime (i := (2 : Fin 3)) (R := K)) hn)
  obtain ⟨a, ha⟩ := h0
  have h1a : (X 1 : MvPolynomial (Fin 3) K) ∣ a := by
    have hd : (X 1 : MvPolynomial (Fin 3) K) ∣ X 0 * a := by
      simpa only [ha] using h1
    exact ((X_prime (i := (0 : Fin 3)) (R := K)).left_dvd_or_dvd_right_of_dvd_mul hd).resolve_left
      (by simp)
  obtain ⟨b, hb⟩ := h1a
  have h2b : (X 2 : MvPolynomial (Fin 3) K) ∣ b := by
    have hd : (X 2 : MvPolynomial (Fin 3) K) ∣ X 0 * (X 1 * b) := by
      simpa only [ha, hb] using h2
    have hd' : (X 2 : MvPolynomial (Fin 3) K) ∣ X 1 * b :=
      ((X_prime (i := (0 : Fin 3)) (R := K)).left_dvd_or_dvd_right_of_dvd_mul hd).resolve_left (by simp)
    exact ((X_prime (i := (1 : Fin 3)) (R := K)).left_dvd_or_dvd_right_of_dvd_mul hd').resolve_left
      (by simp)
  obtain ⟨c, hc⟩ := h2b
  have hprod : ((X 0 * X 1 * X 2 : MvPolynomial (Fin 3) K)).IsHomogeneous 3 := by
    simpa only [Nat.reduceAdd, mul_assoc] using
      ((MvPolynomial.isHomogeneous_X K (0 : Fin 3)).mul
        (MvPolynomial.isHomogeneous_X K (1 : Fin 3))).mul
        (MvPolynomial.isHomogeneous_X K (2 : Fin 3))
  have hrev : c * (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) K) =
      (X 0 : MvPolynomial (Fin 3) K) * (X 1 * (X 2 * c)) := by ring
  have hc0 : c = 0 :=
    eq_zero_of_mul_homogeneous_lt hprod (by simp)
      (by simpa only [hrev, ha, hb, hc] using hq) (by decide)
  apply hq0
  simp [ha, hb, hc, hc0]

/-- Multiplication by some standard projective coordinate is injective on
the quotient by any nonzero plane quadratic, including a reducible or
nonreduced quadratic. -/
theorem exists_regular_coordinate_mod_homogeneous_quadratic
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0) :
    ∃ i : Fin 3, ∀ x : MvPolynomial (Fin 3) K,
      X i * x ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)) →
        x ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)) := by
  obtain ⟨i, hi⟩ := exists_coordinate_relprime_homogeneous_quadratic q hq hq0
  exact ⟨i, regular_mod_span_singleton_of_isRelPrime hi.symm⟩

/-- The coordinate chart supplied above detects all elements of the
quadratic coordinate ring, including nilpotents in a double conic. -/
theorem exists_injective_coordinate_localization_mod_homogeneous_quadratic
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0) :
    ∃ i : Fin 3, Function.Injective
      (algebraMap
        (MvPolynomial (Fin 3) K ⧸ Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)))
        (Localization (Submonoid.powers
          (Ideal.Quotient.mk (Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)))
            (X i : MvPolynomial (Fin 3) K))))) := by
  let I : Ideal (MvPolynomial (Fin 3) K) := Ideal.span ({q} : Set _)
  obtain ⟨i, hi⟩ := exists_regular_coordinate_mod_homogeneous_quadratic q hq hq0
  refine ⟨i, ?_⟩
  have hreg : Ideal.Quotient.mk I (X i : MvPolynomial (Fin 3) K) ∈
      nonZeroDivisors (MvPolynomial (Fin 3) K ⧸ I) :=
    quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal I (X i) hi
  have hM : Submonoid.powers (Ideal.Quotient.mk I (X i : MvPolynomial (Fin 3) K)) ≤
      nonZeroDivisors (MvPolynomial (Fin 3) K ⧸ I) := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact (nonZeroDivisors (MvPolynomial (Fin 3) K ⧸ I)).pow_mem hreg n
  exact IsLocalization.injective _ hM

/-- A polynomial whose class vanishes on each standard coordinate
localization belongs to the quadratic ideal. This includes nonreduced
plane conics, since the argument detects nilpotent classes as well. -/
theorem mem_quadratic_ideal_of_all_coordinate_localizations_zero
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    (f : MvPolynomial (Fin 3) K)
    (hzero : ∀ i : Fin 3,
      algebraMap
        (MvPolynomial (Fin 3) K ⧸ Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)))
        (Localization (Submonoid.powers
          (Ideal.Quotient.mk (Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)))
            (X i : MvPolynomial (Fin 3) K))))
        (Ideal.Quotient.mk (Ideal.span ({q} : Set (MvPolynomial (Fin 3) K))) f) = 0) :
    f ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)) := by
  obtain ⟨i, hi⟩ :=
    exists_injective_coordinate_localization_mod_homogeneous_quadratic q hq hq0
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hi
  simpa using hzero i

/-- The plane quadratic quotient has no element annihilated by every
projective coordinate. This is the irrelevant-socle condition for its
homogeneous ideal, valid even for a double line. -/
theorem quadratic_quotient_no_irrelevant_annihilator
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0) :
    ∀ x : MvPolynomial (Fin 3) K ⧸
        Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)),
      (∀ i : Fin 3,
        Ideal.Quotient.mk
          (Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)))
          (X i : MvPolynomial (Fin 3) K) * x = 0) → x = 0 := by
  let I : Ideal (MvPolynomial (Fin 3) K) := Ideal.span ({q} : Set _)
  obtain ⟨i, hi⟩ := exists_regular_coordinate_mod_homogeneous_quadratic q hq hq0
  have hreg : Ideal.Quotient.mk I (X i : MvPolynomial (Fin 3) K) ∈
      nonZeroDivisors (MvPolynomial (Fin 3) K ⧸ I) :=
    quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal I (X i) hi
  intro x hx
  exact (mem_nonZeroDivisors_iff.mp hreg).1 x (hx i)

/-- The regular-coordinate statement also covers the degenerate equation
`q = 0`, whose projective quotient is the whole plane. This case appears
when an ambient quadratic is a multiple of the plane equation. -/
theorem exists_regular_coordinate_mod_homogeneous_quadratic_any
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 2) :
    ∃ i : Fin 3, ∀ x : MvPolynomial (Fin 3) K,
      X i * x ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)) →
        x ∈ Ideal.span ({q} : Set (MvPolynomial (Fin 3) K)) := by
  by_cases hq0 : q = 0
  · refine ⟨0, ?_⟩
    intro x hx
    have hxzero : (X 0 : MvPolynomial (Fin 3) K) * x = 0 := by
      simpa [hq0] using hx
    have : x = 0 := (mul_eq_zero.mp hxzero).resolve_left (by simp)
    simpa [hq0] using this
  · exact exists_regular_coordinate_mod_homogeneous_quadratic q hq hq0

end PfaffianDescent

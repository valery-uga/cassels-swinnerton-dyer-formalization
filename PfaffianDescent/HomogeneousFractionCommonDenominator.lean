import PfaffianDescent.ProjectiveNegativeTwistStalk
import PfaffianDescent.ThreeGeneratorGradedComplex

/-! SOURCE ONLY / UNVERIFIED. Common homogeneous denominator for THREE
actual negative-twist fractions, including zero and nonreduced later uses.
The full localization at a prime need NOT be graded; no such grading or
projection on nonhomogeneous denominators is assumed. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry MvPolynomial
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime]
local notation "L" => Localization p.primeCompl

lemma polynomialPrimeFraction_eq_of_cross
    (a b c d : MvPolynomial (Fin 4) K)
    (hb : b ∈ p.primeCompl) (hd : d ∈ p.primeCompl)
    (h : a * d = c * b) :
    (Localization.mk a ⟨b, hb⟩ : L) = Localization.mk c ⟨d, hd⟩ := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul]
  convert h using 1 <;> ring

/-- Zero is given a homogeneous denominator by a power of the chosen
actual degree-one element outside the homogeneous prime. -/
theorem negativeTwistFraction_exists_rep
    (t : PS 1) (ht : t.val ∈ p.primeCompl) (m : ℕ)
    (x : stalkSubmodule PS p m) :
    ∃ (i : ℕ) (a : PS i) (b : PS (i + m))
      (hb : b.val ∈ p.primeCompl), x.val = Localization.mk a.val ⟨b.val, hb⟩ := by
  rcases x.property with hx | ⟨i, a, b, hb, hx⟩
  · let b : PS (0 + m) := ⟨t.val ^ m, by
      simpa only [MvPolynomial.mem_homogeneousSubmodule, zero_add, one_mul] using t.property.pow m⟩
    refine ⟨0, 0, b, p.primeCompl.pow_mem ht m, ?_⟩
    rw [hx]
    exact (Localization.mk_zero _).symm
  · exact ⟨i, a, b, hb, hx⟩

/-- All three fractions have SAME homogeneous denominator D, with numerator
of degree d≥6. The extra t^6 makes later Koszul grading shifts natural.
No common denominator or desired graded preimage is an input. -/
theorem negativeTwistFraction_common_denominator_three
    (t : PS 1) (ht : t.val ∈ p.primeCompl) (m : ℕ)
    (x : stalkSubmodule PS p m × stalkSubmodule PS p m × stalkSubmodule PS p m) :
    ∃ (d : ℕ), 6 ≤ d ∧ ∃ (A : PS d × PS d × PS d) (D : PS (d + m))
      (hD : D.val ∈ p.primeCompl),
      x.1.val = Localization.mk A.1.val ⟨D.val, hD⟩ ∧
      x.2.1.val = Localization.mk A.2.1.val ⟨D.val, hD⟩ ∧
      x.2.2.val = Localization.mk A.2.2.val ⟨D.val, hD⟩ := by
  obtain ⟨i, a, b, hb, hx⟩ := negativeTwistFraction_exists_rep p t ht m x.1
  obtain ⟨j, c, e, he, hy⟩ := negativeTwistFraction_exists_rep p t ht m x.2.1
  obtain ⟨k, r, s, hs, hz⟩ := negativeTwistFraction_exists_rep p t ht m x.2.2
  let v := degreeOnePower PS t 6
  let d := i + j + k + m + m + 6
  let D : PS (d + m) := ⟨b.val * e.val * s.val * v.val, by
    simpa only [MvPolynomial.mem_homogeneousSubmodule, d, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((b.property.mul e.property).mul s.property).mul v.property⟩
  let A0 : PS d := ⟨a.val * e.val * s.val * v.val, by
    simpa only [MvPolynomial.mem_homogeneousSubmodule, d, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((a.property.mul e.property).mul s.property).mul v.property⟩
  let A1 : PS d := ⟨c.val * b.val * s.val * v.val, by
    simpa only [MvPolynomial.mem_homogeneousSubmodule, d, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((c.property.mul b.property).mul s.property).mul v.property⟩
  let A2 : PS d := ⟨r.val * b.val * e.val * v.val, by
    simpa only [MvPolynomial.mem_homogeneousSubmodule, d, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((r.property.mul b.property).mul e.property).mul v.property⟩
  have hv : v.val ∈ p.primeCompl := p.primeCompl.pow_mem ht 6
  have hD : D.val ∈ p.primeCompl :=
    p.primeCompl.mul_mem (p.primeCompl.mul_mem (p.primeCompl.mul_mem hb he) hs) hv
  refine ⟨d, by dsimp [d]; omega, (A0, A1, A2), D, hD, ?_, ?_, ?_⟩
  · rw [hx]
    apply polynomialPrimeFraction_eq_of_cross p _ _ _ _ hb hD
    dsimp [A0, D]
    ring
  · rw [hy]
    apply polynomialPrimeFraction_eq_of_cross p _ _ _ _ he hD
    dsimp [A1, D]
    ring
  · rw [hz]
    apply polynomialPrimeFraction_eq_of_cross p _ _ _ _ hs hD
    dsimp [A2, D]
    ring

/-- Injectivity of the actual polynomial localization is proved from the
prime complement, and will turn a localized cycle into a polynomial cycle. -/
theorem polynomialPrimeLocalization_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 4) K) L) :=
  IsLocalization.injective L p.primeCompl_le_nonZeroDivisors

/-- Multiplication by a polynomial keeps the SAME actual denominator. -/
lemma polynomialPrimeFraction_mul (q a d : MvPolynomial (Fin 4) K)
    (hd : d ∈ p.primeCompl) :
    algebraMap (MvPolynomial (Fin 4) K) L q * Localization.mk a ⟨d, hd⟩ =
      Localization.mk (q * a) ⟨d, hd⟩ := by
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [mul_assoc, IsLocalization.mk'_spec, map_mul]

lemma polynomialPrimeFraction_sub (a b d : MvPolynomial (Fin 4) K)
    (hd : d ∈ p.primeCompl) :
    (Localization.mk a ⟨d, hd⟩ : L) - Localization.mk b ⟨d, hd⟩ =
      Localization.mk (a - b) ⟨d, hd⟩ := by
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [sub_mul, IsLocalization.mk'_spec, IsLocalization.mk'_spec, map_sub]

lemma polynomialPrimeFraction_add (a b d : MvPolynomial (Fin 4) K)
    (hd : d ∈ p.primeCompl) :
    (Localization.mk a ⟨d, hd⟩ : L) + Localization.mk b ⟨d, hd⟩ =
      Localization.mk (a + b) ⟨d, hd⟩ := by
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [add_mul, IsLocalization.mk'_spec, IsLocalization.mk'_spec, map_add]

/-- A zero fraction has zero numerator in the actual polynomial domain. -/
lemma polynomialPrimeFraction_eq_zero_iff (a d : MvPolynomial (Fin 4) K)
    (hd : d ∈ p.primeCompl) :
    (Localization.mk a ⟨d, hd⟩ : L) = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply polynomialPrimeLocalization_injective p
    have he := IsLocalization.mk'_spec L a (⟨d, hd⟩ : p.primeCompl)
    rw [← Localization.mk_eq_mk', h, zero_mul] at he
    simpa only [map_zero] using he.symm
  · rintro rfl
    exact Localization.mk_zero _

end PfaffianDescent.ProjectiveNegativeTwist

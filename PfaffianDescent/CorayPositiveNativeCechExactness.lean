import PfaffianDescent.CorayPositiveNativeCechDifferential
import PfaffianDescent.VoisinLaurentCechExact
import PfaffianDescent.VoisinP3TopCechExact

/-! Derived exactness in degrees one, two and three of the CANONICAL
positive-twist Čech complex. Actual native maps/terms are retained;
no vanishing/comparison certificate is an input. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open CategoryTheory AlgebraicGeometry MvPolynomial
open LaurentLocalization LaurentCechCore LaurentCechExact
open scoped AddMonoidAlgebra BigOperators
universe u
variable (K : Type u) [Field K]

/-- Every native positive-twist Čech one-cocycle has a native boundary,
using the actual differential and actual chart representatives. -/
theorem p3PositiveNativeCech_exact_one (m : ℕ) :
    Function.Exact ((p3PositiveNativeCechComplex K m).d 0 1)
      ((p3PositiveNativeCechComplex K m).d 1 2) := by
  intro y
  constructor
  · intro hy
    have hdy : ∀ f, tupleD1 (p3PositiveNativeCechTermToLaurent K m 1 y) f = 0 := by
      intro f
      rw [← congrFun (p3PositiveNativeCechTermToLaurent_d_one K m y) f, hy]
      simp
    obtain ⟨xL, hxL, hdiff⟩ :=
      laurent_tuple_exact_one_of_degree K (m : ℤ)
        (p3PositiveNativeCechTermToLaurent K m 1 y)
        (p3PositiveNativeCechTermToLaurent_support K m 1 y) hdy
    obtain ⟨x, hx⟩ := exists_p3PositiveNativeCechTermToLaurent_eq_of_support K m 0 xL hxL
    refine ⟨x, ?_⟩
    apply p3PositiveNativeCechTermToLaurent_injective K m 1
    rw [p3PositiveNativeCechTermToLaurent_d_zero, hx]
    funext f
    exact hdiff f
  · rintro ⟨x, rfl⟩
    exact ConcreteCategory.congr_hom ((p3PositiveNativeCechComplex K m).d_comp_d 0 1 2) x

/-- Every native positive-twist Čech two-cocycle has a native boundary,
using the actual differential and actual chart representatives. -/
theorem p3PositiveNativeCech_exact_two (m : ℕ) :
    Function.Exact ((p3PositiveNativeCechComplex K m).d 1 2)
      ((p3PositiveNativeCechComplex K m).d 2 3) := by
  intro z
  constructor
  · intro hz
    have hdz : ∀ f, tupleD2 (p3PositiveNativeCechTermToLaurent K m 2 z) f = 0 := by
      intro f
      rw [← congrFun (p3PositiveNativeCechTermToLaurent_d_two K m z) f, hz]
      simp
    obtain ⟨yL, hyL, hdiff⟩ :=
      laurent_tuple_exact_two_of_degree K (m : ℤ)
        (p3PositiveNativeCechTermToLaurent K m 2 z)
        (p3PositiveNativeCechTermToLaurent_support K m 2 z) hdz
    obtain ⟨y, hy⟩ := exists_p3PositiveNativeCechTermToLaurent_eq_of_support K m 1 yL hyL
    refine ⟨y, ?_⟩
    apply p3PositiveNativeCechTermToLaurent_injective K m 2
    rw [p3PositiveNativeCechTermToLaurent_d_one, hy]
    funext f
    exact hdiff f
  · rintro ⟨y, rfl⟩
    exact ConcreteCategory.congr_hom ((p3PositiveNativeCechComplex K m).d_comp_d 1 2 3) y

/-- Nonnegative total degree excludes full negative support, so every
native positive-twist Čech three-cocycle also has a native boundary. -/
theorem p3PositiveNativeCech_exact_three (m : ℕ) :
    Function.Exact ((p3PositiveNativeCechComplex K m).d 2 3)
      ((p3PositiveNativeCechComplex K m).d 3 4) := by
  intro w
  constructor
  · intro hw
    have hproper : ∀ a : LaurentLocalization.LaurentExponent,
        totalDegree a = (m : ℤ) → negativeSupport a ≠ Set.univ := by
      intro a hdegree hfull
      have hrecover := p3SerreDualExponent_polynomialExponent_of_negativeSupport a hfull
      have htotal := congrArg totalDegree hrecover
      rw [p3SerreDualExponent_totalDegree, hdegree] at htotal
      omega
    have hdw : ∀ f, tupleD3 (p3PositiveNativeCechTermToLaurent K m 3 w) f = 0 := by
      intro f
      rw [← congrFun (p3PositiveNativeCechTermToLaurent_d_three K m w) f, hw]
      simp
    obtain ⟨zL, hzL, hdiff⟩ :=
      laurent_tuple_exact_three_of_degree_of_no_full_support K (m : ℤ) hproper
        (p3PositiveNativeCechTermToLaurent K m 3 w)
        (p3PositiveNativeCechTermToLaurent_support K m 3 w) hdw
    obtain ⟨z, hz⟩ := exists_p3PositiveNativeCechTermToLaurent_eq_of_support K m 2 zL hzL
    refine ⟨z, ?_⟩
    apply p3PositiveNativeCechTermToLaurent_injective K m 3
    rw [p3PositiveNativeCechTermToLaurent_d_two, hz]
    funext f
    exact hdiff f
  · rintro ⟨z, rfl⟩
    exact ConcreteCategory.congr_hom ((p3PositiveNativeCechComplex K m).d_comp_d 2 3 4) z

end PfaffianDescent.ProjectiveNegativeTwist

import PfaffianDescent.VoisinTwistCechLaurentDifferential
import PfaffianDescent.VoisinLaurentCechExact

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped AddMonoidAlgebra BigOperators

universe u

namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentLocalization LaurentCechCore LaurentCechExact

variable (K : Type u) [Field K]

/-- Laurent compatibility alone turns the explicit Laurent contraction into
exactness of the raw negative-twist Cech complex in degree one. -/
theorem p3NegativeTwistCech_exact_one_of_laurent_compat
    (m : ℕ)
    (h0 : ∀ x : (p3NegativeTwistCechComplex (K := K) m).X 0,
      p3NegativeTwistCechTermToLaurent K m 1 ((p3NegativeTwistCechComplex (K := K) m).d 0 1 x) = tupleD0 (p3NegativeTwistCechTermToLaurent K m 0 x))
    (h1 : ∀ y : (p3NegativeTwistCechComplex (K := K) m).X 1,
      p3NegativeTwistCechTermToLaurent K m 2 ((p3NegativeTwistCechComplex (K := K) m).d 1 2 y) = tupleD1 (p3NegativeTwistCechTermToLaurent K m 1 y)) :
    Function.Exact ((p3NegativeTwistCechComplex (K := K) m).d 0 1) ((p3NegativeTwistCechComplex (K := K) m).d 1 2) := by
  intro y
  constructor
  · intro hy
    have hdy : ∀ f, tupleD1 (p3NegativeTwistCechTermToLaurent K m 1 y) f = 0 := by
      intro f
      rw [← congrFun (h1 y) f, hy]
      simp
    obtain ⟨xL, hxL, hdiff⟩ :=
      laurent_tuple_exact_one_of_degree K (-(m : ℤ)) (p3NegativeTwistCechTermToLaurent K m 1 y)
        (p3NegativeTwistCechTermToLaurent_support_properties K m 1 y) hdy
    obtain ⟨x, hx⟩ :=
      exists_p3NegativeTwistCechTermToLaurent_eq_of_support K m 0 xL hxL
    refine ⟨x, ?_⟩
    apply p3NegativeTwistCechTermToLaurent_injective K m 1
    rw [h0 x, hx]
    funext f
    exact hdiff f
  · rintro ⟨x, rfl⟩
    exact ConcreteCategory.congr_hom ((p3NegativeTwistCechComplex (K := K) m).d_comp_d 0 1 2) x

/-- Laurent compatibility alone turns the explicit Laurent contraction into
exactness of the raw negative-twist Cech complex in degree two. -/
theorem p3NegativeTwistCech_exact_two_of_laurent_compat
    (m : ℕ)
    (h1 : ∀ y : (p3NegativeTwistCechComplex (K := K) m).X 1,
      p3NegativeTwistCechTermToLaurent K m 2 ((p3NegativeTwistCechComplex (K := K) m).d 1 2 y) = tupleD1 (p3NegativeTwistCechTermToLaurent K m 1 y))
    (h2 : ∀ z : (p3NegativeTwistCechComplex (K := K) m).X 2,
      p3NegativeTwistCechTermToLaurent K m 3 ((p3NegativeTwistCechComplex (K := K) m).d 2 3 z) = tupleD2 (p3NegativeTwistCechTermToLaurent K m 2 z)) :
    Function.Exact ((p3NegativeTwistCechComplex (K := K) m).d 1 2) ((p3NegativeTwistCechComplex (K := K) m).d 2 3) := by
  intro z
  constructor
  · intro hz
    have hdz : ∀ f, tupleD2 (p3NegativeTwistCechTermToLaurent K m 2 z) f = 0 := by
      intro f
      rw [← congrFun (h2 z) f, hz]
      simp
    obtain ⟨yL, hyL, hdiff⟩ :=
      laurent_tuple_exact_two_of_degree K (-(m : ℤ)) (p3NegativeTwistCechTermToLaurent K m 2 z)
        (p3NegativeTwistCechTermToLaurent_support_properties K m 2 z) hdz
    obtain ⟨y, hy⟩ :=
      exists_p3NegativeTwistCechTermToLaurent_eq_of_support K m 1 yL hyL
    refine ⟨y, ?_⟩
    apply p3NegativeTwistCechTermToLaurent_injective K m 2
    rw [h1 y, hy]
    funext f
    exact hdiff f
  · rintro ⟨y, rfl⟩
    exact ConcreteCategory.congr_hom ((p3NegativeTwistCechComplex (K := K) m).d_comp_d 1 2 3) y

end PfaffianDescent.ProjectiveNegativeTwist


namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentCechCore

variable (K : Type u) [Field K]

/-- The raw standard-cover Cech complex of every negative twist on projective
three-space is exact in degree one. -/
theorem p3NegativeTwistCech_exact_one (m : ℕ) :
    Function.Exact
      ((p3NegativeTwistCechComplex (K := K) m).d 0 1)
      ((p3NegativeTwistCechComplex (K := K) m).d 1 2) :=
  p3NegativeTwistCech_exact_one_of_laurent_compat K m
    (p3NegativeTwistCechTermToLaurent_d_zero K m)
    (p3NegativeTwistCechTermToLaurent_d_one K m)

/-- The raw standard-cover Cech complex of every negative twist on projective
three-space is exact in degree two. -/
theorem p3NegativeTwistCech_exact_two (m : ℕ) :
    Function.Exact
      ((p3NegativeTwistCechComplex (K := K) m).d 1 2)
      ((p3NegativeTwistCechComplex (K := K) m).d 2 3) :=
  p3NegativeTwistCech_exact_two_of_laurent_compat K m
    (p3NegativeTwistCechTermToLaurent_d_one K m)
    (p3NegativeTwistCechTermToLaurent_d_two K m)

end PfaffianDescent.ProjectiveNegativeTwist

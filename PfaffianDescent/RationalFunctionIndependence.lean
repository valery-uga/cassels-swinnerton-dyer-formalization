import PfaffianDescent.PolynomialIndependence
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Module

namespace PfaffianDescent
open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- Independence of one polynomial specialization implies independence over rational functions. -/
theorem rationalFunction_independent_of_specialization (P : Fin n → L[X]) (t : K)
    (hP : LinearIndependent K (fun i => (P i).eval (algebraMap K L t))) :
    LinearIndependent K⟮X⟯ (fun i => algebraMap L[X] L⟮X⟯ (P i)) := by
  have hp := polynomial_independent_of_specialization P t hP
  have hi : LinearIndependent K[X] (fun i => algebraMap L[X] L⟮X⟯ (P i)) := by
    exact hp.map' ((Algebra.linearMap L[X] L⟮X⟯).restrictScalars K[X]) (by
      rw [LinearMap.ker_eq_bot]
      exact IsFractionRing.injective L[X] L⟮X⟯)
  exact (LinearIndependent.iff_fractionRing K[X] K⟮X⟯).mp hi

end
end PfaffianDescent

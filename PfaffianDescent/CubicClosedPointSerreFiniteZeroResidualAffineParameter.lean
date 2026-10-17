import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeStalkQuotient
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Actual affine parameter sections generate the actual local maximal ideal -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_affine_parameter_of_principalIdealRing
    (X : Scheme.{u}) (U : X.affineOpens) [IsPrincipalIdealRing Γ(X, U.1)]
    (x : X) (hx : x ∈ U.1) :
    ∃ t : Γ(X, U.1),
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal = Ideal.span {t} ∧
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
        Ideal.span ({X.presheaf.germ U.1 x hx t} : Set (X.presheaf.stalk x)) := by
  let P := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨t, ht⟩ := (inferInstance : P.IsPrincipal)
  refine ⟨t, ht, ?_⟩
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U.1)
  letI := U.2.isLocalization_stalk (⟨x, hx⟩ : U.1)
  have h := IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk x)
  rw [ht, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

end PfaffianDescent

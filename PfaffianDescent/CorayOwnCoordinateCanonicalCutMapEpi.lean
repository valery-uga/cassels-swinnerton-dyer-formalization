import PfaffianDescent.CorayOwnPositiveRestrictionNativeEpi
import PfaffianDescent.CorayOwnCoordinateCokernelCanonicalCutMap

/-! SOURCE ONLY. Genuine Epi of the SAME canonical whole-cut cokernel
comparison. Native restriction factorization supplies all surjectivity. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal coordinate-cut restriction is Epi at every nonnegative
degree, internally from the actual tensor ideal sequence. -/
theorem ownCoordinateCutPositiveRestriction_epi
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) : Epi (ownCoordinateCutPositiveRestriction C j m) := by
  exact ownQuotientPositiveRestriction_epi C
    (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))
    le_sup_left (m + 1)

/-- Surjectivity is proved for the ORIGINAL canonical cokernel desc map,
not for a replacement isomorphism. Kernel injectivity remains separate. -/
theorem ownCoordinateCokernelToWholeCutPositiveTwist_epi
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) : Epi (ownCoordinateCokernelToWholeCutPositiveTwist C j m) := by
  letI : Epi (ownCoordinateCutPositiveRestriction C j m) :=
    ownCoordinateCutPositiveRestriction_epi C j m
  exact epi_of_epi_fac (ownCoordinateCokernelToWholeCutPositiveTwist_projection C j m)

end PfaffianDescent.Coray
end

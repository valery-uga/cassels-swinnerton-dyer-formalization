import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridMinorRestriction
import PfaffianDescent.VoisinSectionRestriction

/-! The actual determinant-open cubic restriction kernel has dimension four. -/
noncomputable section
open MvPolynomial Module
namespace PfaffianDescent
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_cubicProductKernel_finrank_four_of_surjective
    {F : Type v} [Field F]
    (T : homogeneousSubmodule (Fin 4) F 3 →ₗ[F] (Fin 16 → F))
    (hsurj : Function.Surjective T) : finrank F (LinearMap.ker T) = 4 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker T
  have hrange : LinearMap.range T = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hsource : finrank F (homogeneousSubmodule (Fin 4) F 3) = 20 := by
    rw [four_variable_homogeneous_finrank]
    decide
  rw [hrange, finrank_top, hsource] at hdim
  have htarget : finrank F (Fin 16 → F) = 16 := by simp
  rw [htarget] at hdim
  omega

end PfaffianDescent

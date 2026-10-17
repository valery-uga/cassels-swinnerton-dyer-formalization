import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridKernelScalarExtension
import PfaffianDescent.VoisinSectionChoice

/-! Four independent native kernel sections need no surjectivity assumption. -/
noncomputable section
open MvPolynomial Module
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem voisinDegreeTenSelectedAvoidance_exists_four_independent_submoduleMembers
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (H : Submodule F V) (hdim : 4 ≤ finrank F H) :
    ∃ q : Fin 4 → V, LinearIndependent F q ∧ ∀ i, q i ∈ H := by
  obtain ⟨q, hq⟩ := exists_linearIndependent_of_le_finrank hdim
  refine ⟨fun i => (q i).1, ?_, fun i => (q i).2⟩
  exact hq.map' H.subtype (Submodule.ker_subtype _)

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_four_independent_nativeCubicKernelMembers
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (x : Fin 4 → A) (hA : finrank K A ≤ 16) :
    ∃ q : Fin 4 → homogeneousSubmodule (Fin 4) K 3,
      LinearIndependent K q ∧
      ∀ i, q i ∈ LinearMap.ker (homogeneousSectionRestriction x 3) := by
  have hsource : 16 + 4 ≤ finrank K (homogeneousSubmodule (Fin 4) K 3) := by
    rw [four_variable_homogeneous_finrank]
    decide
  have hdim := homogeneousSectionRestriction_kernel_lower_bound x 3 16 4 hsource hA
  exact voisinDegreeTenSelectedAvoidance_exists_four_independent_submoduleMembers
    (LinearMap.ker (homogeneousSectionRestriction x 3)) hdim

end PfaffianDescent

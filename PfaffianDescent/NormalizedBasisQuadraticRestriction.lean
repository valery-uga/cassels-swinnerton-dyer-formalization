import PfaffianDescent.HomogeneousVanishingLinearSystem

/- SOURCE ONLY / UNVERIFIED. Quadrics X_j X_i restrict to the actual
normalized basis vectors, so the FULL restriction has rank four. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem normalizedBasis_quadraticRestriction_surjective
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (b : Basis (Fin 4) K L) (j : Fin 4) (hb : b j = 1) :
    Function.Surjective (homogeneousSectionRestriction (K := K) b 2) := by
  let t := homogeneousSectionRestriction (K := K) b 2
  have hspan : Submodule.span K (Set.range b) ≤ LinearMap.range t := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨X j * X i, (isHomogeneous_X K j).mul (isHomogeneous_X K i)⟩, ?_⟩
    simp only [t, homogeneousSectionRestriction_apply, eval₂_mul, eval₂_X, hb, one_mul]
  rw [b.span_eq] at hspan
  exact LinearMap.range_eq_top.mp (top_unique hspan)

theorem normalizedBasis_homogeneousQuadraticVanishing_finrank_six
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (b : Basis (Fin 4) K L) (j : Fin 4) (hb : b j = 1) :
    finrank K (homogeneousVanishingPolynomialSubmodule (K := K) b 2) = 6 := by
  rw [homogeneousVanishingPolynomialSubmodule_finrank]
  have hdim := LinearMap.finrank_range_add_finrank_ker
    (homogeneousSectionRestriction (K := K) b 2)
  have hrange := LinearMap.range_eq_top.mpr
    (normalizedBasis_quadraticRestriction_surjective b j hb)
  have h4 : finrank K L = 4 := by simpa using finrank_eq_card_basis b
  have h10 : finrank K (homogeneousSubmodule (Fin 4) K 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  rw [hrange, finrank_top, h4, h10] at hdim
  omega

end PfaffianDescent

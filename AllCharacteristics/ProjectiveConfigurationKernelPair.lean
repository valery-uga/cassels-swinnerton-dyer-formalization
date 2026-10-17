import AllCharacteristics.FreeQuotientKernelPair
import AllCharacteristics.ProjectiveConfigurationAffineCharts

/-! # The kernel pair of the actual unordered projective configuration

The proved free affine quotient charts identify the entire kernel pair with the disjoint union of the original permutation graphs in every characteristic.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

instance isIso_projectiveConfigurationKernelPairMap :
    IsIso (schemeActionKernelPairMap (Equiv.Perm (Fin n)) (configurationRightAction f n)
      (projectiveConfigurationQuotientMap 𝒜 f n) (projectiveConfigurationQuotientMap_invariant 𝒜 f n)) := by
  refine isIso_schemeActionKernelPairMap_of_freeQuotientCharts (S := S)
    (Equiv.Perm (Fin n)) (configurationRightAction f n)
    (configurationRightAction_one f n) (configurationRightAction_mul f n)
    (projectiveConfigurationQuotientMap 𝒜 f n) (projectiveConfigurationQuotientMap_invariant 𝒜 f n)
    (projectiveConfigurationQuotientMap_eq_iff_orbit 𝒜 f n)
    (fun K _ c g hg => configurationRightAction_no_fixed_field_point f n K c g hg) ?_
  intro x
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hio, hi, p, hp, j, hjo, hx, hs, _⟩ :=
    exists_projectiveConfigurationQuotient_affineChart 𝒜 f n x
  exact ⟨U, hUa, τ, hτ₁, hτcomp, i, hio, hi, p, hp, j, hjo, hx, hs⟩

end AllCharacteristics

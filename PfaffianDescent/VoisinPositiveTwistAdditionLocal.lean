import PfaffianDescent.ProjectivePositiveTwistAddition
import PfaffianDescent.VoisinPositiveTwistTriviality

/-!
# The zero-degree base for addition of positive twists

This identifies the degree-zero positive-positive product with the already
verified positive-negative inverse pairing.
-/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u

namespace ProjectiveNegativeTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- At degree zero, converting the second positive twist to the ordinary
zero twist makes the two multiplication pairings agree. -/
theorem positivePositivePairing_zero_factorization :
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 0))
      (positiveZeroToZeroTwist 𝒜) ≫ positiveNegativePairing 𝒜 0 =
    positivePositivePairing 𝒜 0 0 ≫ positiveZeroToZeroTwist 𝒜 := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  apply (adj.homEquiv _ _).injective
  rw [schemeModuleTensorMap_eq_sheafification]
  erw [adj.homEquiv_naturality_left]
  have hneg : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 0).val
        (sheafOfModules 𝒜 0).val) (sheafOfModules 𝒜 0)
      (positiveNegativePairing 𝒜 0) =
      positiveNegativePairingPresheaf 𝒜 0 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hneg]
  erw [adj.homEquiv_naturality_right]
  have hpos : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 0).val
        (positiveSheafOfModules 𝒜 0).val)
      (positiveSheafOfModules 𝒜 0)
      (positivePositivePairing 𝒜 0 0) =
      positivePositivePairingPresheaf 𝒜 0 0 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hpos]
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  rfl

/-- The degree-zero positive-positive multiplication pairing is an
isomorphism. -/
theorem positivePositivePairing_zero_isIso :
    IsIso (positivePositivePairing 𝒜 0 0) := by
  let : IsIso (schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 0))
      (positiveZeroToZeroTwist 𝒜)) := by
    exact (schemeModuleTensorMapIso (Iso.refl _) (positiveZeroTwistIso 𝒜)).isIso_hom
  let : IsIso (positiveNegativePairing 𝒜 0) :=
    positiveNegativePairing_zero_isIso 𝒜
  let : IsIso (positiveZeroToZeroTwist 𝒜) :=
    (positiveZeroTwistIso 𝒜).isIso_hom
  have : IsIso (positivePositivePairing 𝒜 0 0 ≫ positiveZeroToZeroTwist 𝒜) := by
    rw [← positivePositivePairing_zero_factorization]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (g := positivePositivePairing 𝒜 0 0)
    (f := positiveZeroToZeroTwist 𝒜)

end ProjectiveNegativeTwist
end PfaffianDescent

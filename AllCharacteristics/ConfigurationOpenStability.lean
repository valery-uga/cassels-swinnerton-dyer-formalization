import AllCharacteristics.RelativePermutationActions
import AllCharacteristics.EquivariantOpenImage

/-! # Stability of the actual distinct-configuration open under permutations -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (n : ℕ)

/-- The full inverse image of the distinct-configuration open under any original
permutation is exactly the same open. -/
theorem orderedFamilyConfigurationOpen_preimage (e : Equiv.Perm (Fin n)) :
    (orderedFamilyRightAction f n e) ⁻¹ᵁ orderedFamilyConfigurationOpen f n =
      orderedFamilyConfigurationOpen f n := by
  ext x
  change orderedFamilyRightAction f n e x ∈ orderedFamilyConfigurationOpen f n ↔
    x ∈ orderedFamilyConfigurationOpen f n
  constructor
  · intro hx
    have hm := orderedFamilyReindex_mem_configuration f e.symm e.symm.injective
      (orderedFamilyRightAction f n e x) hx
    have hi : orderedFamilyRightAction f n e ≫ orderedFamilyRightAction f n e⁻¹ =
        𝟙 (orderedFamilyPowerOver f n).left := by
      rw [← orderedFamilyRightAction_mul, mul_inv_cancel, orderedFamilyRightAction_one]
    have hp := congrArg (fun m : (orderedFamilyPowerOver f n).left ⟶
      (orderedFamilyPowerOver f n).left ↦ m x) hi
    change orderedFamilyRightAction f n e⁻¹ (orderedFamilyRightAction f n e x) = x at hp
    change orderedFamilyRightAction f n e⁻¹ (orderedFamilyRightAction f n e x) ∈
      orderedFamilyConfigurationOpen f n at hm
    exact hp ▸ hm
  · intro hx
    exact orderedFamilyReindex_mem_configuration f e e.injective x hx

end AllCharacteristics

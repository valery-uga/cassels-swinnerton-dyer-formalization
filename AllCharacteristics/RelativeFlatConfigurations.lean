import AllCharacteristics.RelativeConfigurationOpen
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flatness of actual ordered powers and configuration opens -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Actual ordered fiber powers of a flat family are flat over the same base. -/
instance flat_orderedFamilyPower (n : ℕ) [Flat f] :
    Flat (orderedFamilyPowerOver f n).hom := by
  induction n with
  | zero =>
    change Flat (𝟙 S)
    infer_instance
  | succ n ih =>
    have := ih
    change Flat (pullback.fst f (orderedFamilyPowerOver f n).hom ≫ f)
    infer_instance

/-- Actual distinct ordered configurations in a flat separated family are flat. -/
instance flat_orderedFamilyConfiguration [IsSeparated f] (n : ℕ) [Flat f] :
    Flat (orderedFamilyConfigurationOver f n).hom := by
  change Flat ((orderedFamilyConfigurationOpen f n).ι ≫ (orderedFamilyPowerOver f n).hom)
  infer_instance

end AllCharacteristics

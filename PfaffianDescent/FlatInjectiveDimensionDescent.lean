import PfaffianDescent.ModuleFunctorInjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits ModuleCat
universe u
section
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restriction along a flat ring homomorphism does not increase injective dimension. -/
theorem flat_restriction_injectiveDimensionLE (hf : f.Flat) (n : ℕ) (M : ModuleCat.{u} S)
    [HasInjectiveDimensionLE M n] :
    HasInjectiveDimensionLE ((restrictScalars f).obj M) n := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : (restrictScalars f).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (extendRestrictScalarsAdj f)
  exact moduleFunctor_hasInjectiveDimensionLE (restrictScalars f) n M

/-- The unit of a ring extension as a linear map to the restricted regular module. -/
def restrictionUnitLinear : R →ₗ[R] (restrictScalars f).obj (ModuleCat.of S S) where
  toFun := f
  map_add' := f.map_add
  map_smul' r a := f.map_mul r a

/-- Self-injective dimension descends along a flat ring extension whose unit
splits as a map of modules. Field extensions provide such splittings. -/
theorem split_flat_self_injectiveDimensionLE (hf : f.Flat)
    (r : (restrictScalars f).obj (ModuleCat.of S S) →ₗ[R] R)
    (hr : ∀ a : R, r (f a) = a) (n : ℕ)
    [HasInjectiveDimensionLE (ModuleCat.of S S) n] :
    HasInjectiveDimensionLE (ModuleCat.of R R) n := by
  letI := flat_restriction_injectiveDimensionLE f hf n (ModuleCat.of S S)
  let h : Retract (ModuleCat.of R R) ((restrictScalars f).obj (ModuleCat.of S S)) :=
    { i := ModuleCat.ofHom (X := ModuleCat.of R R)
        (Y := (restrictScalars f).obj (ModuleCat.of S S)) (restrictionUnitLinear f)
      r := ModuleCat.ofHom (X := (restrictScalars f).obj (ModuleCat.of S S))
        (Y := ModuleCat.of R R) r
      retract := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact hr a }
  exact h.hasInjectiveDimensionLT (n+1)

end
end PfaffianDescent

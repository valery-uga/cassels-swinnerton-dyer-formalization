import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension

namespace PfaffianDescent
open CategoryTheory
section
variable {R S : Type*} [CommRing R] [CommRing S]
attribute [local instance] RingHomInvPair.of_ringEquiv

/-- A ring isomorphism is semilinear on the regular modules. -/
def regularSemilinearEquiv (e : R ≃+* S) : R ≃ₛₗ[RingHomClass.toRingHom e] S where
  __ := e.toAddEquiv
  map_smul' r x := e.map_mul r x

/-- The self-injective dimension is invariant under isomorphism of rings. -/
theorem self_injectiveDimensionLE_ringEquiv (e : R ≃+* S) (n : ℕ) :
    HasInjectiveDimensionLE (ModuleCat.of R R) n ↔
      HasInjectiveDimensionLE (ModuleCat.of S S) n :=
  ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv e (regularSemilinearEquiv e) n

end
end PfaffianDescent

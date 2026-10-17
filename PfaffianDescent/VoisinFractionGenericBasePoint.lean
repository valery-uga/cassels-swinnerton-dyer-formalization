import PfaffianDescent.VoisinRelativeTripleIntersectionFamily
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The fraction-field point is the affine generic point

This identifies the unique field-valued point used for the generic fiber
with the topological generic point of the integral affine base.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

theorem specFieldMap_closedPoint_eq_genericPoint_of_injective
    {R F : Type u} [CommRing R] [IsDomain R] [Field F]
    (g : R →+* F) (hg : Function.Injective g) :
    Spec.map (CommRingCat.ofHom g)
      (IsLocalRing.closedPoint F) =
      genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  simp only [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot]
  change Ideal.comap g ⊥ = ⊥
  exact Ideal.comap_bot_of_injective g hg

theorem specFractionMap_closedPoint_eq_genericPoint
    {R : Type u} [CommRing R] [IsDomain R] :
    Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      (IsLocalRing.closedPoint (FractionRing R)) =
      genericPoint (Spec (.of R)) := by
  exact specFieldMap_closedPoint_eq_genericPoint_of_injective
    (algebraMap R (FractionRing R))
    (IsFractionRing.injective R (FractionRing R))

end PfaffianDescent

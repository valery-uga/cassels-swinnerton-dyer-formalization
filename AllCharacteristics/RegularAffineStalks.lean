import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Regular local rings on open affine coefficient spaces

Regularity of a ring supplies regular local stalks on its affine spectrum.
Open immersions preserve these stalks, so every open of a regular affine
coefficient space has the local regularity required for specialization.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- The actual scheme stalks of a regular affine ring are regular local rings. -/
theorem isRegularLocalRing_spec_stalk
    (R : Type u) [CommRing R] [IsRegularRing R] (x : Spec (.of R)) :
    IsRegularLocalRing ((Spec (.of R)).presheaf.stalk x) :=
  IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of R) x).commRingCatIsoToRingEquiv.symm

/-- An open immersion transfers local regularity through its stalk isomorphism. -/
theorem isRegularLocalRing_stalk_of_openImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (x : X)
    [IsRegularLocalRing (Y.presheaf.stalk (i x))] :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  IsRegularLocalRing.of_ringEquiv (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv

/-- Every point of an open in a regular affine spectrum has a regular local
ring, including points over positive-characteristic primes of an integer base. -/
theorem isRegularLocalRing_open_spec_stalk
    (R : Type u) [CommRing R] [IsRegularRing R]
    (U : (Spec (.of R)).Opens) (x : U.toScheme) :
    IsRegularLocalRing (U.toScheme.presheaf.stalk x) := by
  have := isRegularLocalRing_spec_stalk R (U.ι x)
  exact isRegularLocalRing_stalk_of_openImmersion U.ι x

end AllCharacteristics

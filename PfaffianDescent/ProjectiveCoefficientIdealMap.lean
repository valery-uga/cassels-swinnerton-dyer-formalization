import AllCharacteristics.HomogeneousProjectiveAmbient

/-!
# Canonical coefficient change of homogeneous projective ideals

The homogeneous ideal obtained by graded coefficient change has exactly
the ordinary extended polynomial ideal. This makes arbitrary base-ideal
fibres available without carrying a separately chosen homogeneous ideal.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual homogeneous ideal after changing polynomial coefficients. -/
noncomputable def coefficientChangedHomogeneousIdeal
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R)) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) S) :=
  HomogeneousIdeal.map (ambientCoefficientGradedRingHom f) J

theorem coefficientChangedHomogeneousIdeal_toIdeal
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R)) :
    J.toIdeal.map (MvPolynomial.map f) =
      (coefficientChangedHomogeneousIdeal f J).toIdeal := by
  rw [coefficientChangedHomogeneousIdeal, HomogeneousIdeal.toIdeal_map]
  rfl

end PfaffianDescent

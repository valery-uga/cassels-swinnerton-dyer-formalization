import PfaffianDescent.LocalizationRegularPreservation
import AllCharacteristics.CoordinateCharts

/-!
# Regular homogeneous equations on actual projective charts

A regular homogeneous element of a projective coordinate quotient remains
regular after localization at any chart coordinate, and hence in the
degree-zero chart ring. No regularity of the chart coordinate is required.
-/

namespace PfaffianDescent

open MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized section of a regular homogeneous coordinate-ring
element is regular on each actual affine projective chart. -/
theorem chartSection_isRegular_of_coordinateRing_isRegular
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    {d : ℕ} (s : grading J d)
    (hs : IsRegular (s : CoordinateRing J)) (j : Fin 4) :
    IsRegular (Away.mk (grading J) (coordinate_mem J j) d
      (s : CoordinateRing J) (by simpa using s.2)) := by
  let z := coordinate J j
  have hloc : IsRegular
      (Localization.mk (s : CoordinateRing J)
        ⟨z ^ d, by use d⟩ : Localization (.powers z)) := by
    rw [Localization.mk_eq_mk'_apply]
    exact isRegular_localization_mk_of_isRegular
      (Submonoid.powers z) (s : CoordinateRing J) hs
      ⟨z ^ d, by use d⟩
  obtain ⟨hl, hr⟩ := (isRegular_iff_eq_zero_of_mul).mp hloc
  apply (isRegular_iff_eq_zero_of_mul).mpr
  constructor
  · intro x hx
    apply HomogeneousLocalization.val_injective (Submonoid.powers z)
    have hh : (Localization.mk (s : CoordinateRing J)
        ⟨z ^ d, by use d⟩ : Localization (.powers z)) * x.val = 0 := by
      simpa only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_zero,
        Away.val_mk] using congrArg HomogeneousLocalization.val hx
    simpa only [HomogeneousLocalization.val_zero] using hl x.val hh
  · intro x hx
    apply HomogeneousLocalization.val_injective (Submonoid.powers z)
    have hh : x.val * (Localization.mk (s : CoordinateRing J)
        ⟨z ^ d, by use d⟩ : Localization (.powers z)) = 0 := by
      simpa only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_zero,
        Away.val_mk] using congrArg HomogeneousLocalization.val hx
    simpa only [HomogeneousLocalization.val_zero] using hr x.val hh

end PfaffianDescent

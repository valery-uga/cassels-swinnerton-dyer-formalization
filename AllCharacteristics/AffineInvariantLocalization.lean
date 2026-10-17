import AllCharacteristics.InvariantLocalization
import AllCharacteristics.LocalizationOpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Cartesian localization of affine invariant quotients

The quotient of an equivariant localization at a fixed element is an actual
open of the original invariant spectrum. The square with the original affine
localization is Cartesian. This is the scheme-theoretic compatibility needed
when gluing affine finite-group quotients.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [SMulCommClass G R A] [SMulCommClass G R B] [SMulDistribClass G A B]
variable (t : FixedPoints.subalgebra R A G) [IsLocalization.Away t.val B]

include t

/-- Localization at a fixed element gives an actual open immersion of invariant spectra. -/
theorem isOpenImmersion_affineInvariantLocalization :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (equivariantFixedSubalgebraMap R A B G))) := by
  let := equivariantFixedSubalgebraAlgebra R A B G
  have : IsLocalization.Away t (FixedPoints.subalgebra R B G) :=
    isLocalizationAway_fixedSubalgebra R A B G t
  exact isOpenImmersion_SpecMap_of_isLocalizationAway
    (FixedPoints.subalgebra R A G) (FixedPoints.subalgebra R B G) t

/-- The original localization and its invariant quotient form an actual Cartesian square. -/
theorem isPullback_affineInvariantLocalization :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (affineInvariantQuotientMap R B G) (affineInvariantQuotientMap R A G)
      (Spec.map (CommRingCat.ofHom (equivariantFixedSubalgebraMap R A B G))) := by
  let := equivariantFixedSubalgebraAlgebra R A B G
  have : IsLocalization.Away t (FixedPoints.subalgebra R B G) :=
    isLocalizationAway_fixedSubalgebra R A B G t
  have : IsLocalization ((Submonoid.powers t).map
      (algebraMap (FixedPoints.subalgebra R A G) A)) B := by
    rw [Submonoid.map_powers]
    exact (inferInstance : IsLocalization.Away t.val B)
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isLocalization
    (algebraMap (FixedPoints.subalgebra R A G) A)
    (algebraMap (FixedPoints.subalgebra R B G) B)
    (equivariantFixedSubalgebraMap_comp R A B G) (Submonoid.powers t)

end AllCharacteristics

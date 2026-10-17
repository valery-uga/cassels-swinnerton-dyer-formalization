import AllCharacteristics.OpenPullbackIsomorphism
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual affine localization squares and restrictions inside open images

Localization of an arbitrary ring homomorphism gives its actual Cartesian
square of spectra. If its spectrum morphism is an open immersion and the
chosen principal open lies in its image, the localized spectrum morphism
is an isomorphism. No domain or characteristic assumption is used.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (t : R)

/-- The actual map between localizations has the prescribed original coefficient map. -/
theorem awayMap_comp_algebraMap :
    (Localization.awayMap φ t).comp (algebraMap R (Localization.Away t)) =
      (algebraMap A (Localization.Away (φ t))).comp φ := by
  apply RingHom.ext
  intro a
  change Localization.awayMap φ t (algebraMap R (Localization.Away t) a) =
    algebraMap A (Localization.Away (φ t)) (φ a)
  have hmap : Submonoid.powers t ≤ (Submonoid.powers (φ t)).comap φ := by
    rintro z ⟨m, rfl⟩
    exact ⟨m, (map_pow φ t m).symm⟩
  exact IsLocalization.map_eq (S := Localization.Away t) (Q := Localization.Away (φ t))
    (g := φ) (M := Submonoid.powers t) (T := Submonoid.powers (φ t)) hmap a

/-- Localization of a ring homomorphism gives the actual Cartesian spectrum square. -/
theorem isPullback_Spec_awayMap :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (φ t)))))
      (Spec.map (CommRingCat.ofHom (Localization.awayMap φ t)))
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))) := by
  have : IsLocalization ((Submonoid.powers t).map φ) (Localization.Away (φ t)) := by
    rw [Submonoid.map_powers]
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isLocalization φ (Localization.awayMap φ t)
    (awayMap_comp_algebraMap φ t) (Submonoid.powers t)

/-- A principal open contained in an affine open image has an isomorphic actual localized preimage. -/
theorem isIso_Spec_awayMap_of_basicOpen_subset
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))]
    (ht : (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum R)) ⊆
      Set.range (Spec.map (CommRingCat.ofHom φ))) :
    IsIso (Spec.map (CommRingCat.ofHom (Localization.awayMap φ t))) := by
  apply isIso_snd_of_isPullback_open_range (isPullback_Spec_awayMap φ t)
  have hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))) =
      (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away t) t
  rw [hr]
  exact ht

end AllCharacteristics

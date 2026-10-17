import AllCharacteristics.AffineLocalizationPullback

/-!
# Ring equivalences on principal opens inside affine open images

The isomorphism of localized spectra yields an actual ring equivalence for
the original localization map. This supplies the algebraic comparison that
will be restricted to the corresponding invariant rings.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- An isomorphism of the actual spectra reflects bijectivity of the original ring homomorphism. -/
theorem ringHom_bijective_of_isIsoSpecMap {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) [IsIso (Spec.map (CommRingCat.ofHom φ))] : Function.Bijective φ := by
  have : IsIso (Scheme.Spec.map (CommRingCat.ofHom φ).op) := by
    change IsIso (Spec.map (CommRingCat.ofHom φ))
    infer_instance
  have : IsIso (CommRingCat.ofHom φ).op := isIso_of_reflects_iso _ Scheme.Spec
  have : IsIso (CommRingCat.ofHom φ) := isIso_of_op _
  exact (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom φ)).mp inferInstance

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (t : R)
variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))]
variable (ht : (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum R)) ⊆
  Set.range (Spec.map (CommRingCat.ofHom φ)))

/-- The original localization map is an actual ring equivalence over a principal open in its image. -/
noncomputable def awayMapRingEquiv_of_basicOpen_subset :
    Localization.Away t ≃+* Localization.Away (φ t) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (Localization.awayMap φ t))) :=
    isIso_Spec_awayMap_of_basicOpen_subset φ t ht
  exact RingEquiv.ofBijective (Localization.awayMap φ t)
    (ringHom_bijective_of_isIsoSpecMap (Localization.awayMap φ t))

/-- The constructed localized ring equivalence has exactly the original localization homomorphism. -/
theorem awayMapRingEquiv_of_basicOpen_subset_toRingHom :
    (awayMapRingEquiv_of_basicOpen_subset φ t ht).toRingHom = Localization.awayMap φ t := rfl

end AllCharacteristics

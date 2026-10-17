import AllCharacteristics.ProjectiveUnitCoefficientFlatness
import AllCharacteristics.ProjectiveBaseChange

/-!
# Flat restrictions to coefficient opens

The flat localized hypersurface is identified with the actual scheme pullback
of the original family. Its flatness then transfers to the restriction of
that family over the basic open where the chosen coefficient is nonzero.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace HomogeneousProjective
universe u

/-- The actual pullback along localization at a coefficient is flat. -/
theorem flat_hypersurfacePullback_after_localizing_coeff
    {R : Type u} {σ : Type} [CommRing R] [Finite σ]
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : σ →₀ ℕ) (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalization.Away (p.coeff m) S] :
    Flat (pullback.snd (hypersurfaceToBase p hp)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) := by
  have : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ _ (h : IsIso _) ↦ by infer_instance)
  have h := flat_hypersurfaceToBase_after_localizing_coeff p hp m S
  rw [← hypersurfaceBaseChangeIso_hom_snd (algebraMap R S) p hp] at h
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Flat.{u}) _ _).mp h

/-- The projective hypersurface family is flat over each basic coefficient
open. No domain, perfection, or characteristic hypothesis is needed. -/
theorem flat_hypersurface_on_coefficient_open
    {R : Type u} {σ : Type} [CommRing R] [Finite σ]
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (m : σ →₀ ℕ) :
    Flat (hypersurfaceToBase p hp ∣_ PrimeSpectrum.basicOpen (p.coeff m)) := by
  have : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ _ (h : IsIso _) ↦ by infer_instance)
  let S := Localization.Away (p.coeff m)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hg : g.opensRange = PrimeSpectrum.basicOpen (p.coeff m) := by
    apply SetLike.coe_injective
    change Set.range (PrimeSpectrum.comap (algebraMap R S)) =
      (PrimeSpectrum.basicOpen (p.coeff m) : Set (PrimeSpectrum R))
    exact PrimeSpectrum.localization_away_comap_range S (p.coeff m)
  have h := (MorphismProperty.arrow_mk_iso_iff (P := @Flat.{u})
    (morphismRestrictOpensRange (hypersurfaceToBase p hp) g)).mpr
      (flat_hypersurfacePullback_after_localizing_coeff p hp m S)
  rwa [hg] at h

end HomogeneousProjective
end AllCharacteristics

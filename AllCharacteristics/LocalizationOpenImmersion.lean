import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Basic

/-!
# Open immersions from arbitrary models of principal localization

The spectrum map for any algebra satisfying the principal localization
property is an open immersion. The comparison with the canonical localization
is an actual algebra isomorphism, and its coefficient map is retained.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- Any actual model of localization at one element gives the corresponding open immersion. -/
theorem isOpenImmersion_SpecMap_of_isLocalizationAway
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (t : R) [IsLocalization.Away t S] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let e := IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t) S
  have : IsIso (CommRingCat.ofHom e.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
  have he : CommRingCat.ofHom (algebraMap R (Localization.Away t)) ≫
      CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom (algebraMap R S) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact e.commutes r
  have hc : Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t))) := by
    rw [← Spec.map_comp, he]
  rw [hc]
  infer_instance

end AllCharacteristics

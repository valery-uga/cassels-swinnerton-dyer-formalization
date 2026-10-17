import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Resolve the canonical open-inclusion instance while X and U are still native variables. -/
private lemma nativeSchemeOpenInclusion294 {X : Scheme.{u}} (U : X.Opens) :
    IsOpenImmersion (Scheme.Opens.ι (X := X) U) := by
  infer_instance

variable {C : Type u} [CommRing C] (delta : C)

/-- The canonical localization morphism, with its native Spec map unchanged. -/
def localizationPrincipalOpenMap294 :
    Spec (.of (Localization.Away delta)) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away delta)))

lemma localizationPrincipalOpenMap_isOpenImmersion294 :
    IsOpenImmersion (localizationPrincipalOpenMap294 delta) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of C) delta

lemma localizationPrincipalOpenMap_range294 :
    Set.range (localizationPrincipalOpenMap294 delta) =
      (PrimeSpectrum.basicOpen delta : Set (PrimeSpectrum C)) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away delta) delta

/-- The actual localization affine scheme is isomorphic to the principal open subscheme. -/
def localizationPrincipalOpenIso294 :
    Spec (.of (Localization.Away delta)) ≅
      Scheme.Opens.toScheme (X := Spec (.of C)) (PrimeSpectrum.basicOpen delta) := by
  letI := localizationPrincipalOpenMap_isOpenImmersion294 delta
  letI : IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of C)) (PrimeSpectrum.basicOpen delta)) :=
    nativeSchemeOpenInclusion294 (X := Spec (.of C))
      (PrimeSpectrum.basicOpen delta : (Spec (.of C)).Opens)
  exact IsOpenImmersion.isoOfRangeEq (localizationPrincipalOpenMap294 delta)
    (Scheme.Opens.ι (X := Spec (.of C)) (PrimeSpectrum.basicOpen delta))
    ((localizationPrincipalOpenMap_range294 delta).trans (Scheme.Opens.range_ι (X := Spec (.of C)) (PrimeSpectrum.basicOpen delta)).symm)

lemma localizationPrincipalOpenIso_hom_fac294 :
    (localizationPrincipalOpenIso294 delta).hom ≫
        Scheme.Opens.ι (X := Spec (.of C)) (PrimeSpectrum.basicOpen delta) =
      localizationPrincipalOpenMap294 delta := by
  letI := localizationPrincipalOpenMap_isOpenImmersion294 delta
  letI : IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of C)) (PrimeSpectrum.basicOpen delta)) :=
    nativeSchemeOpenInclusion294 (X := Spec (.of C))
      (PrimeSpectrum.basicOpen delta : (Spec (.of C)).Opens)
  exact IsOpenImmersion.isoOfRangeEq_hom_fac (localizationPrincipalOpenMap294 delta)
    (Scheme.Opens.ι (X := Spec (.of C)) (PrimeSpectrum.basicOpen delta))
    ((localizationPrincipalOpenMap_range294 delta).trans (Scheme.Opens.range_ι (X := Spec (.of C)) (PrimeSpectrum.basicOpen delta)).symm)

end PfaffianDescent

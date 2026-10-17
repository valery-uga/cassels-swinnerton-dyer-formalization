import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.FinitePresentation

namespace PfaffianDescent
open TensorProduct
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (U : Submonoid R)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization U S]
  (f : M →ₗ[R] N)

lemma localizedTensorMap_eq_baseChange :
    IsLocalizedModule.map U (TensorProduct.mk R S M 1) (TensorProduct.mk R S N 1) f =
      (f.baseChange S).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext U (TensorProduct.mk R S M 1) (TensorProduct.mk R S N 1)
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
  rfl

/-- The tensor and localized-module descriptions give the same invertibility condition. -/
lemma linearMap_baseChange_bijective_iff_localizedMap :
    Function.Bijective (f.baseChange S) ↔ Function.Bijective (LocalizedModule.map U f) := by
  let eM := IsLocalizedModule.iso U (TensorProduct.mk R S M 1)
  let eN := IsLocalizedModule.iso U (TensorProduct.mk R S N 1)
  have hc := IsLocalizedModule.map_iso_commute U (TensorProduct.mk R S M 1) (TensorProduct.mk R S N 1) f
  rw [localizedTensorMap_eq_baseChange] at hc
  have he : (f.baseChange S : _ → _) ∘ eM = eN ∘ (LocalizedModule.map U f) := by
    funext x
    exact LinearMap.congr_fun hc x
  constructor
  · intro h
    have hh : Function.Bijective (eN ∘ (LocalizedModule.map U f)) := he ▸ h.comp eM.bijective
    exact (Function.Bijective.of_comp_iff' eN.bijective _).mp hh
  · intro h
    have hh : Function.Bijective ((f.baseChange S : _ → _) ∘ eM) := he.symm ▸ eN.bijective.comp h
    exact (Function.Bijective.of_comp_iff _ eM.bijective).mp hh

end
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.FinitePresentation R N]

/-- An invertible map between a finite and a finitely presented module remains invertible on a basic neighborhood. -/
theorem linearMap_exists_away_bijective (f : M →ₗ[R] N) (p : PrimeSpectrum R)
    (h : Function.Bijective (f.baseChange (Localization.AtPrime p.asIdeal))) :
    ∃ a : R, a ∉ p.asIdeal ∧ Function.Bijective (f.baseChange (Localization.Away a)) := by
  have hp : Function.Bijective (IsLocalizedModule.map p.asIdeal.primeCompl
      (TensorProduct.mk R (Localization.AtPrime p.asIdeal) M 1)
      (TensorProduct.mk R (Localization.AtPrime p.asIdeal) N 1) f) := by
    rw [localizedTensorMap_eq_baseChange]
    exact h
  obtain ⟨a, ha, hfa⟩ := Module.FinitePresentation.exists_notMem_bijective f p.asIdeal
    (TensorProduct.mk R (Localization.AtPrime p.asIdeal) M 1)
    (TensorProduct.mk R (Localization.AtPrime p.asIdeal) N 1) hp
  exact ⟨a, ha, (linearMap_baseChange_bijective_iff_localizedMap (Submonoid.powers a) (Localization.Away a) f).mpr hfa⟩

end
end PfaffianDescent

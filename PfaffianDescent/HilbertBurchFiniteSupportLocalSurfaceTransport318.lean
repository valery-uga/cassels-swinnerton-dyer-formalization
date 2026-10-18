import PfaffianDescent.FiniteSupportSemilocalBasisSpreading
import PfaffianDescent.HilbertBurchSurfaceResolution318
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
Transport the local surface property from the original finite support to
every maximal localization of its constructed semilocal ambient ring.
The contraction belongs to the specified support by finite prime avoidance.
-/

noncomputable section

namespace PfaffianDescent

theorem finiteSupportLocalization_maximal_localSurface021
    {R : Type*} [CommRing R]
    (t : Finset (MaximalSpectrum R)) (ht : t.Nonempty)
    (hreg : ∀ m ∈ t, IsRegularLocalRing (Localization.AtPrime m.asIdeal))
    (hdim : ∀ m ∈ t, ringKrullDim (Localization.AtPrime m.asIdeal) = 2)
    (P : Ideal (Localization (finiteSupportDenominators001 t))) (hP : P.IsMaximal) :
    IsRegularLocalRing (Localization.AtPrime P) ∧
      ringKrullDim (Localization.AtPrime P) = 2 := by
  let S := finiteSupportDenominators001 t
  let L := Localization S
  letI : P.IsMaximal := hP
  let Q : MaximalSpectrum L := ⟨P, hP⟩
  obtain ⟨m, hm, hunder⟩ := finiteSupportLocalization_maximal_under001 t ht Q
  change P.under R = m.asIdeal at hunder
  let em := Localization.localRingEquiv (P.under R) m.asIdeal (RingEquiv.refl R)
    (by
      apply Ideal.ext
      intro x
      change x ∈ P.under R ↔ x ∈ m.asIdeal
      rw [hunder])
  let e := em.symm.trans
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization S P).toRingEquiv
  letI : IsRegularLocalRing (Localization.AtPrime m.asIdeal) := hreg m hm
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_⟩
  exact (ringKrullDim_eq_of_ringEquiv e).symm.trans (hdim m hm)

end PfaffianDescent

end

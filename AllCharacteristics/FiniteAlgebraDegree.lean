import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Artinian.Algebra

/-!
# Degree of a finite algebra

The dimension of a finite algebra over a field is the sum of local lengths
weighted by residue-field degrees. No separability assumption is made.
-/

open scoped BigOperators
namespace AllCharacteristics

/-- The dimension of a finite local algebra is its length times the full degree
of its residue field, including the inseparable degree. -/
theorem local_finrank_eq_length_mul_residue_degree
    (k A : Type*) [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Module.Finite k A] :
    Module.finrank k A = (Module.length A A).toNat *
      Module.finrank k (IsLocalRing.ResidueField A) := by
  have : IsLocalHom (algebraMap k A) := by infer_instance
  have h : (Module.finrank k A : ℕ∞) = Module.length A A *
      (Module.finrank k (IsLocalRing.ResidueField A) : ℕ∞) := by
    calc
      (Module.finrank k A : ℕ∞) = Module.length k A :=
        (Module.length_eq_finrank k A).symm
      _ = Module.length A A * Module.length (IsLocalRing.ResidueField k)
          (IsLocalRing.ResidueField A) := IsLocalRing.length_restrictScalars k A A
      _ = Module.length A A * Module.length k (IsLocalRing.ResidueField A) := by
        congr 1
        exact (Module.length_eq_of_surjective
          (IsLocalRing.residue_surjective (R := k))).symm
      _ = Module.length A A * (Module.finrank k (IsLocalRing.ResidueField A) : ℕ∞) := by
        rw [Module.length_eq_finrank]
  simpa using congrArg ENat.toNat h

/-- A finite algebra has degree equal to the weighted sum of the degrees of
all its closed points. Each weight is the length of the actual local algebra. -/
theorem finrank_eq_sum_local_length_mul_residue_degree
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    [Fintype (PrimeSpectrum A)] :
    Module.finrank k A = ∑ q : PrimeSpectrum A,
      (Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat * Module.finrank k q.asIdeal.ResidueField := by
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum]
  apply Finset.sum_congr rfl
  intro q _
  have : Module.Finite k (Localization.AtPrime q.asIdeal) :=
    Module.Finite.of_surjective (Algebra.algHom k A (Localization.AtPrime q.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal))
  exact local_finrank_eq_length_mul_residue_degree k (Localization.AtPrime q.asIdeal)

end AllCharacteristics

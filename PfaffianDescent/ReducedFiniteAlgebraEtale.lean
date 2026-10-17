import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.FieldTheory.Perfect

namespace PfaffianDescent
section
variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [IsReduced A]

/-- A finite reduced algebra over a characteristic-zero field is finite étale;
the proof decomposes its actual ring into its residue fields. -/
theorem reduced_finite_algebra_etale : Algebra.Etale K A := by
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  letI (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  apply (Algebra.Etale.iff_exists_algEquiv_prod K A).mpr
  refine ⟨MaximalSpectrum A, inferInstance, (fun m => A ⧸ m.asIdeal),
    inferInstance, inferInstance, (IsArtinianRing.equivPi A).restrictScalars K, ?_⟩
  intro m
  exact ⟨inferInstance, inferInstance⟩

end
end PfaffianDescent

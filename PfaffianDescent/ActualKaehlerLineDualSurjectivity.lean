import PfaffianDescent.ActualKaehlerLineDualAlgebra
import PfaffianDescent.QuarticInfinitesimalPoints

/- SOURCE ONLY / UNVERIFIED. Surjectivity is derived from the ACTUAL line
quotient and separable residue; no infinitesimal generator is supplied. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct KaehlerDifferential
open scoped TensorProduct
universe u
variable {k R L : Type u} [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
  [Algebra.IsSeparable k L]

lemma actualKaehlerLine_exists_residueIdeal_derivative_one
    (hrho : Function.Surjective (algebraMap R L))
    (q : L ⊗[R] KaehlerDifferential k R →ₗ[L] L) (hq : Function.Surjective q) :
    ∃ r : R, algebraMap R L r = 0 ∧
      q (1 ⊗ₜ[R] KaehlerDifferential.D k R r) = 1 := by
  obtain ⟨y, hy⟩ := hq 1
  have he : Function.Surjective (kerCotangentToTensor k R L) := by
    letI : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
    intro z
    have hz : z ∈ LinearMap.range (kerCotangentToTensor k R L) := by
      rw [KaehlerDifferential.range_kerCotangentToTensor k R L hrho]
      change KaehlerDifferential.mapBaseChange k R L z = 0
      exact Subsingleton.elim _ _
    exact hz
  obtain ⟨z, hz⟩ := he y
  obtain ⟨a, rfl⟩ := (RingHom.ker (algebraMap R L)).toCotangent_surjective z
  refine ⟨a.val, a.property, ?_⟩
  rw [kerCotangentToTensor_toCotangent] at hz
  rw [hz]
  exact hy

/-- EVERY surjective actual Kaehler line gives a surjective dual algebra map. -/
theorem actualKaehlerLineDualAlgebraMap_surjective
    (hrho : Function.Surjective (algebraMap R L))
    (q : L ⊗[R] KaehlerDifferential k R →ₗ[L] L) (hq : Function.Surjective q) :
    Function.Surjective (actualKaehlerLineDualAlgebraMap q) := by
  apply QuarticNet.dualNumber_surjective_of_residue_and_nilpotent
  · simpa only [actualKaehlerLineDualAlgebraMap_fst] using hrho
  · obtain ⟨r, hr, hd⟩ := actualKaehlerLine_exists_residueIdeal_derivative_one hrho q hq
    refine ⟨r, ?_, ?_⟩
    · simpa only [actualKaehlerLineDualAlgebraMap_fst] using hr
    · rw [actualKaehlerLineDualAlgebraMap_snd, hd]
      exact one_ne_zero

end PfaffianDescent

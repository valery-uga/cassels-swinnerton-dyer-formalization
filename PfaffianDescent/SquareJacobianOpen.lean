import PfaffianDescent.UnramifiedSquarePresentation
import Mathlib.RingTheory.Etale.Locus

namespace PfaffianDescent
open Algebra Module MvPolynomial TensorProduct

section
variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Finite ι] [Finite σ] (P : Algebra.PreSubmersivePresentation R S ι σ)

/-- Inverting the Jacobian turns a square presentation into an étale algebra. -/
theorem squarePresentation_etale_away_jacobian (hdim : P.dimension = 0) :
    Algebra.Etale R (Localization.Away P.jacobian) := by
  let T := Localization.Away P.jacobian
  let Q := Algebra.PreSubmersivePresentation.localizationAway T P.jacobian
  have hj : IsUnit (algebraMap S T P.jacobian) :=
    IsLocalization.map_units T (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
  let E : Algebra.SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { Q.comp P with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian]
        exact hj.mul hj }
  have he : E.dimension = 0 := by
    change (Q.comp P).dimension = 0
    rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
    change (Algebra.Presentation.localizationAway T P.jacobian).dimension + P.dimension = 0
    rw [Algebra.Presentation.localizationAway_dimension_zero, hdim, zero_add]
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 R T :=
    E.isStandardSmoothOfRelativeDimension he
  infer_instance

/-- The nonvanishing locus of the Jacobian lies in the étale locus. -/
theorem squarePresentation_basicOpen_subset_etaleLocus (hdim : P.dimension = 0) :
    (PrimeSpectrum.basicOpen P.jacobian : Set (PrimeSpectrum S)) ⊆ Algebra.etaleLocus R S := by
  haveI := P.toPresentation.finitePresentation_of_isFinite
  exact Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr
    (squarePresentation_etale_away_jacobian P hdim)

variable (T : Type*) [CommRing T] [Algebra R T]

/-- An unramified fiber makes the Jacobian invertible after base change. -/
theorem presentation_fiber_jacobian_isUnit
    [Algebra.FormallyUnramified T (T ⊗[R] S)] :
    IsUnit (1 ⊗ₜ[R] P.jacobian : T ⊗[R] S) := by
  rw [← P.baseChange_jacobian T]
  exact presentation_jacobian_isUnit_of_unramified (P.baseChange T)

/-- Every point of an unramified fiber lies over the Jacobian open of a square presentation. -/
theorem presentation_fiber_image_subset_jacobianOpen
    [Algebra.FormallyUnramified T (T ⊗[R] S)] :
    Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom) ⊆
      (PrimeSpectrum.basicOpen P.jacobian : Set (PrimeSpectrum S)) := by
  rintro _ ⟨q, rfl⟩
  change (1 ⊗ₜ[R] P.jacobian : T ⊗[R] S) ∉ q.asIdeal
  intro hx
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal hx
    (presentation_fiber_jacobian_isUnit P T))

end
end PfaffianDescent

import PfaffianDescent.ProjectiveLengthOfHilbert
import PfaffianDescent.ProjectiveCoefficientGradeFinrank
import AllCharacteristics.ProjectiveBaseChangeFiniteRank
import AllCharacteristics.HomogeneousProjectiveAmbient
import Mathlib.FieldTheory.RatFunc.Basic

/-! SOURCE ONLY / UNVERIFIED. The actual finite projective Hilbert-length
identity over any ground field, through literal whole-ideal scalar extension. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The finite scheme rank equals the eventual homogeneous Hilbert value
over every field, including finite fields. -/
theorem projective_length_of_eventual_hilbert_anyField
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    [IsFinite (toBase I)] (M D : ℕ)
    (hdim : ∀ n, M ≤ n → finrank K (grading I n) = D) :
    AllCharacteristics.finiteSchemeRank (toBase I) = D := by
  letI : Infinite (RatFunc K) :=
    Infinite.of_injective (algebraMap (Polynomial K) (RatFunc K))
      (RatFunc.algebraMap_injective K)
  let J := I.map (ambientCoefficientGradedRingHom (algebraMap K (RatFunc K)))
  have hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap K (RatFunc K))) =
      J.toIdeal := rfl
  have hdimJ : ∀ n, M ≤ n → finrank (RatFunc K) (grading J n) = D := by
    intro n hn
    rw [grade_finrank_eq_coefficientExtension I J hIJ n]
    exact hdim n hn
  letI : IsFinite (toBase J) :=
    projective_finite_of_hilbert_bound J M D (fun n hn => (hdimJ n hn).le)
  exact (projective_finiteSchemeRank_baseChange I J hIJ).trans
    (projective_length_of_eventual_hilbert J M D hdimJ)

end PfaffianDescent

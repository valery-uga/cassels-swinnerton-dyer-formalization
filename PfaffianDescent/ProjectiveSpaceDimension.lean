import AllCharacteristics.ProjectiveSpaceCharts
import PfaffianDescent.SchemeDimensionFromCharts
import PfaffianDescent.VoisinFixedLinearSystemParameters
import PfaffianDescent.LineGrassmannianProjCharts

/-!
# Dimension of projective coefficient spaces

The coordinate charts of projective space are affine spaces on all but one
homogeneous coordinate. This computes the dimension of the projective
parameter spaces used for section-incidence arguments.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective space on a nonempty finite coordinate set has dimension
one less than the number of coordinates. -/
theorem projectiveSpace_dimension
    (K : Type u) [Field K] (σ : Type) [Fintype σ] [Nonempty σ] :
    topologicalKrullDim
      (scheme (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule σ K))) =
      ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  let I₀ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K) := ⊥
  apply scheme_dimension_eq_of_openCover (coordinateOpenCover I₀).openCover
    (Classical.choice ‹Nonempty σ›)
  intro j
  let jσ : σ := j
  change topologicalKrullDim (PrimeSpectrum (ChartRing I₀ jσ)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv (chartPolynomialEquiv jσ).symm,
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field]
  simpa [Nat.card_eq_fintype_card, eq_comm] using
    (Fintype.card_subtype_compl (fun i : σ => i = jσ))

/-- The parameter scheme of a pencil is a projective line and has dimension
one. This is the actual parameter dimension used for the moving conic
classes in the rank-two incidence argument. -/
theorem projectiveLineProj_dimension
    (K : Type u) [Field K] :
    topologicalKrullDim (projectiveLineProj K) = 1 := by
  rw [projectiveLineProj, projectiveSpace_dimension K Bool]
  norm_num

/-- If a finite-dimensional section space has positive vector-space dimension
at most four, its projectivized parameter scheme has dimension at most three.
This is the parameter-space bound for the rigid-divisor strata in Voisin's
direct rank-two incidence argument. -/
theorem finiteDimensionalProjectiveParameters_dimension_le_three
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (hpositive : 0 < Module.finrank K V)
    (hbound : Module.finrank K V ≤ 4) :
    topologicalKrullDim (finiteDimensionalProjectiveParameters K V) ≤ 3 := by
  letI : Nonempty (Fin (Module.finrank K V)) := ⟨⟨0, hpositive⟩⟩
  rw [show finiteDimensionalProjectiveParameters K V =
      projectiveLinearSystemParameters (K := K)
        (τ := Fin (Module.finrank K V)) by rfl]
  rw [projectiveSpace_dimension K (Fin (Module.finrank K V))]
  simp only [Fintype.card_fin]
  exact_mod_cast (show Module.finrank K V - 1 ≤ 3 by omega)

end PfaffianDescent

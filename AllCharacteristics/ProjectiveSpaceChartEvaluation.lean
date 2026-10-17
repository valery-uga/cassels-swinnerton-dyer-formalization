import AllCharacteristics.ProjectiveSpaceCharts

/-!
# Explicit evaluation of a projective-space chart

A tuple whose distinguished coordinate equals one gives a homomorphism from
the actual homogeneous chart ring. The map preserves the coefficient base and
evaluates normalized coordinates as prescribed. These properties determine it
uniquely and will control coefficient-chart transition maps.
-/

open MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- Polynomial evaluation descends to the zero-ideal homogeneous coordinate ring. -/
noncomputable def projectiveCoordinateEvaluation (f : R →+* A) (x : σ → A) :
    CoordinateRing I₀ →+* A :=
  Ideal.Quotient.lift (⊥ : Ideal (MvPolynomial σ R)) (eval₂Hom f x) (by
    intro p hp
    have h : p = 0 := Ideal.mem_bot.mp hp
    rw [h, map_zero])

/-- Evaluation of a homogeneous coordinate gives the prescribed tuple entry. -/
theorem projectiveCoordinateEvaluation_coordinate (f : R →+* A) (x : σ → A) (i : σ) :
    projectiveCoordinateEvaluation f x (coordinate I₀ i) = x i :=
  eval₂Hom_X' f x i

/-- Evaluation of the homogeneous coordinate ring preserves base coefficients. -/
theorem projectiveCoordinateEvaluation_algebraMap (f : R →+* A) (x : σ → A) (r : R) :
    projectiveCoordinateEvaluation f x (algebraMap R (CoordinateRing I₀) r) = f r :=
  eval₂Hom_C f x r

/-- A normalized tuple defines a map from the actual projective-space chart ring. -/
noncomputable def projectiveChartMap (f : R →+* A) (x : σ → A) (j : σ) (hx : x j = 1) :
    ChartRing I₀ j →+* A :=
  GradedChart.liftCoordinateOne (grading I₀) (coordinate I₀ j)
    (projectiveCoordinateEvaluation f x)
    ((projectiveCoordinateEvaluation_coordinate f x j).trans hx)

/-- The normalized chart map preserves the original coefficient homomorphism. -/
theorem projectiveChartMap_baseMap (f : R →+* A) (x : σ → A) (j : σ) (hx : x j = 1)
    (r : R) : projectiveChartMap f x j hx (chartBaseMap I₀ j r) = f r :=
  (GradedChart.liftCoordinateOne_baseMap (grading I₀) (coordinate I₀ j)
    (projectiveCoordinateEvaluation f x)
    ((projectiveCoordinateEvaluation_coordinate f x j).trans hx) r).trans
      (projectiveCoordinateEvaluation_algebraMap f x r)

/-- The normalized coordinates have exactly their prescribed values. -/
theorem projectiveChartMap_coordinate (f : R →+* A) (x : σ → A) (j : σ) (hx : x j = 1)
    (i : σ) : projectiveChartMap f x j hx (chartCoordinate I₀ j i) = x i :=
  (GradedChart.liftCoordinateOne_normalized (grading I₀) (coordinate I₀ j)
    (projectiveCoordinateEvaluation f x)
    ((projectiveCoordinateEvaluation_coordinate f x j).trans hx)
    (coordinate_mem I₀ j) (coordinate I₀ i) (coordinate_mem I₀ i)).trans
      (projectiveCoordinateEvaluation_coordinate f x i)

/-- Base coefficients and normalized coordinates determine a chart-ring map. -/
theorem projectiveChartMap_ext (j : σ) (f g : ChartRing I₀ j →+* A)
    (hb : f.comp (chartBaseMap I₀ j) = g.comp (chartBaseMap I₀ j))
    (hx : ∀ i, f (chartCoordinate I₀ j i) = g (chartCoordinate I₀ j i)) : f = g := by
  apply RingHom.ext
  intro y
  obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I₀ j y
  change f (p.eval₂ (chartBaseMap I₀ j) (chartCoordinate I₀ j)) =
    g (p.eval₂ (chartBaseMap I₀ j) (chartCoordinate I₀ j))
  simp only [MvPolynomial.hom_eval₂, hb, hx]

end HomogeneousProjective
end AllCharacteristics

import AllCharacteristics.NormalizedChartGeneration
import AllCharacteristics.HomogeneousChartEvaluation

/-!
# An explicit polynomial quotient for each projective coordinate chart

The j-th homogeneous chart is the quotient by the homogeneous equations and
X_j - 1. Both maps are constructed, and the isomorphism preserves normalized
coordinate evaluation. This presentation is valid over arbitrary coefficient
rings, including nonreduced rings and all residue characteristics.
-/

open MvPolynomial HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- The equations of the chart obtained by setting its distinguished
homogeneous coordinate equal to one. -/
noncomputable def chartPresentationIdeal (j : σ) : Ideal (MvPolynomial σ R) :=
  I.toIdeal ⊔ Ideal.span {X j - 1}

/-- Quotient the homogeneous coordinate ring further by X_j - 1. -/
noncomputable def coordinateRingToChartPresentation (j : σ) :
    CoordinateRing I →+* MvPolynomial σ R ⧸ chartPresentationIdeal I j :=
  Ideal.Quotient.factor (show I.toIdeal ≤ chartPresentationIdeal I j from le_sup_left)

/-- The distinguished coordinate is one in the polynomial chart presentation. -/
theorem coordinateRingToChartPresentation_coordinate (j : σ) :
    coordinateRingToChartPresentation I j (coordinate I j) = 1 := by
  change Ideal.Quotient.mk (chartPresentationIdeal I j) (X j) =
    Ideal.Quotient.mk (chartPresentationIdeal I j) 1
  apply Ideal.Quotient.eq.mpr
  exact (show Ideal.span {X j - 1} ≤ chartPresentationIdeal I j from le_sup_right)
    (Ideal.subset_span (Set.mem_singleton _))

/-- Evaluate the actual homogeneous chart in its polynomial presentation. -/
noncomputable def chartToPresentation (j : σ) :
    ChartRing I j →+* MvPolynomial σ R ⧸ chartPresentationIdeal I j :=
  GradedChart.liftCoordinateOne (grading I) (coordinate I j)
    (coordinateRingToChartPresentation I j)
    (coordinateRingToChartPresentation_coordinate I j)

/-- The map to the polynomial presentation preserves base coefficients. -/
theorem chartToPresentation_baseMap (j : σ) (r : R) :
    chartToPresentation I j (chartBaseMap I j r) =
      Ideal.Quotient.mk (chartPresentationIdeal I j) (C r) :=
  GradedChart.liftCoordinateOne_baseMap (grading I) (coordinate I j)
    (coordinateRingToChartPresentation I j)
    (coordinateRingToChartPresentation_coordinate I j) r

/-- A normalized chart coordinate maps to the corresponding polynomial class. -/
theorem chartToPresentation_coordinate (j i : σ) :
    chartToPresentation I j (chartCoordinate I j i) =
      Ideal.Quotient.mk (chartPresentationIdeal I j) (X i) :=
  GradedChart.liftCoordinateOne_normalized (grading I) (coordinate I j)
    (coordinateRingToChartPresentation I j)
    (coordinateRingToChartPresentation_coordinate I j)
    (coordinate_mem I j) (coordinate I i) (coordinate_mem I i)

/-- Normalized polynomial evaluation followed by presentation evaluation is
exactly the quotient homomorphism. -/
theorem chartToPresentation_eval (j : σ) (p : MvPolynomial σ R) :
    chartToPresentation I j (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      Ideal.Quotient.mk (chartPresentationIdeal I j) p := by
  have h : (chartToPresentation I j).comp
      (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) =
        Ideal.Quotient.mk (chartPresentationIdeal I j) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, eval₂Hom_C]
      exact chartToPresentation_baseMap I j r
    · intro i
      simp only [RingHom.comp_apply, eval₂Hom_X']
      exact chartToPresentation_coordinate I j i
  exact DFunLike.congr_fun h p

/-- The only relations among normalized chart coordinates are the homogeneous
equations and X_j - 1. -/
theorem chartEvaluation_ker (j : σ) :
    RingHom.ker (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) =
      chartPresentationIdeal I j := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg (chartToPresentation I j)
      (show eval₂Hom (chartBaseMap I j) (chartCoordinate I j) p = 0 from hp)
    exact (chartToPresentation_eval I j p).symm.trans (h.trans (map_zero _))
  · apply sup_le
    · intro p hp
      exact eval₂_chartCoordinate_eq_zero_of_mem I j p hp
    · apply Ideal.span_le.mpr
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change (X j - 1 : MvPolynomial σ R).eval₂ (chartBaseMap I j) (chartCoordinate I j) = 0
      rw [eval₂_sub, eval₂_X, eval₂_one, chartCoordinate_self, sub_self]

/-- The actual homogeneous coordinate chart is isomorphic to the polynomial
quotient obtained by setting its distinguished coordinate equal to one. -/
noncomputable def chartPresentationEquiv (j : σ) :
    (MvPolynomial σ R ⧸ chartPresentationIdeal I j) ≃+* ChartRing I j :=
  (Ideal.quotEquivOfEq (chartEvaluation_ker I j).symm).trans
    (RingHom.quotientKerEquivOfSurjective (eval₂_chartCoordinate_surjective I j))

/-- The chart presentation isomorphism sends each polynomial class to its
normalized coordinate evaluation. -/
theorem chartPresentationEquiv_mk (j : σ) (p : MvPolynomial σ R) :
    chartPresentationEquiv I j (Ideal.Quotient.mk (chartPresentationIdeal I j) p) =
      p.eval₂ (chartBaseMap I j) (chartCoordinate I j) := by
  exact (congrArg (RingHom.quotientKerEquivOfSurjective (eval₂_chartCoordinate_surjective I j))
    (Ideal.quotEquivOfEq_mk (chartEvaluation_ker I j).symm p)).trans
    (RingHom.quotientKerEquivOfSurjective_apply_mk (eval₂_chartCoordinate_surjective I j) p)

end HomogeneousProjective
end AllCharacteristics

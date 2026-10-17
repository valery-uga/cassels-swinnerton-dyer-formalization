import PfaffianDescent.SerreActualProjectiveMatrixChartDiagram
import PfaffianDescent.SerreActualProjectiveBasisParameter

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The standard chart coordinate is the same actual homogeneous fraction as the
linear chart coordinate at its distinguished coordinate. -/
theorem pointSplittingCubicSerreGroundChosenSection_chartCoordinate_eq_linear
    {K : Type u} [CommRing K] {n : ℕ}
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) (j i : Fin n) :
    chartCoordinate I j i = linearChartCoordinate I (coordinate I j) (coordinate_mem I j) i := rfl

/-- A genuine chart diagram for an actual change of basis yields its invertible
regular normalization and literal matrix coordinate formula. -/
theorem pointSplittingCubicSerreGroundChosenSection_basisChart_regular_coordinates
    {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (b c : Basis (Fin n) K V)
    (f z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hf : f ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    {T : Scheme.{u}}
    (a : T ⟶ Spec (.of (Away (grading (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K))) f)))
    (d : T ⟶ Spec (.of (Away (grading (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K))) z)))
    (h : (a ≫ Proj.awayι (grading (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin n) K))) f hf (by decide : 0 < 1)) ≫
      (projectiveBasisCoordinateIso b c).hom =
      d ≫ Proj.awayι (grading (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin n) K))) z hz (by decide : 0 < 1)) :
    let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
    let β := (affineFunctionHom a).comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := f))
    ∃ u : Γ(T, ⊤), IsUnit u ∧ ∀ i,
      affineFunctionHom d (linearChartCoordinate I z hz i) =
        u * (((c.toMatrix b).map β).mulVec
          (fun j => affineFunctionHom a (linearChartCoordinate I f hf j))) i := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  let F := projectiveMatrixGradingMap (c.toMatrix b)
  have hF : HomogeneousIdeal.irrelevant (grading I) ≤
      (HomogeneousIdeal.irrelevant (grading I)).map F :=
    gradedSurjective_irrelevant_le F
      (polynomialQuotientGradingMap_surjective I I (rectangularSubstitution (c.toMatrix b))
        bot_le (fun _ _ hp => rectangularSubstitution_homogeneous (c.toMatrix b) hp)
        (rectangularSubstitution_surjective (c.toMatrix b) (b.toMatrix c)
          (b.toMatrix_mul_toMatrix_flip c)))
  have hh : (a ≫ Proj.awayι (grading I) f hf (by decide : 0 < 1)) ≫
      Proj.map F hF = d ≫ Proj.awayι (grading I) z hz (by decide : 0 < 1) := h
  exact projectiveMatrixChartDiagram_regular_coordinates (c.toMatrix b) hF f z hf hz a d hh

/-- Standard coordinate-chart specialization of the actual basis change. -/
theorem pointSplittingCubicSerreGroundChosenSection_basisCoordinateChart_regular_coordinates
    {K : Type u} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (b c : Basis (Fin n) K V) (j k : Fin n) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of (ChartRing (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K)) j)))
    (d : T ⟶ Spec (.of (ChartRing (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K)) k)))
    (h : a ≫ chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j ≫
      (projectiveBasisCoordinateIso b c).hom =
      d ≫ chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) k) :
    let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
    let β := (affineFunctionHom a).comp (chartBaseMap I j)
    ∃ u : Γ(T, ⊤), IsUnit u ∧ ∀ i,
      affineFunctionHom d (chartCoordinate I k i) =
        u * (((c.toMatrix b).map β).mulVec
          (fun l => affineFunctionHom a (chartCoordinate I j l))) i := by
  simpa only [chartBaseMap, AllCharacteristics.GradedChart.baseMap, chartCoordinate,
    linearChartCoordinate] using
    pointSplittingCubicSerreGroundChosenSection_basisChart_regular_coordinates b c
      (coordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j)
      (coordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) k)
      (coordinate_mem _ j) (coordinate_mem _ k) a d (by simpa only [chartι, Category.assoc] using h)

end PfaffianDescent

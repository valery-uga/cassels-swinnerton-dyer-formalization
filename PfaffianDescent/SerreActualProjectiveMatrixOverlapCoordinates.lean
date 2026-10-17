import PfaffianDescent.SerreActualProjectiveMatrixChartCoordinates
import AllCharacteristics.GradedChartOverlap

/-! On the actual intersection of an old coordinate chart and the inverse
image of a new chart, the matrix-transformed normalized coefficients differ
by the explicit invertible normalization ratio. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem projectiveMatrixOverlap_normalized_coordinates
    {K : Type u} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (f z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hf : f ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (i : Fin n) :
    let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
    let F := projectiveMatrixGradingMap M
    let g := F z
    let hg := F.map_mem hz
    let R := Away (grading I) (f * g)
    let φold : Away (grading I) f →+* R := awayMap (grading I) hg rfl
    let φnew : Away (grading I) g →+* R := awayMap (grading I) hf (mul_comm f g)
    let a := AllCharacteristics.GradedChart.overlapCoordinateUnit (grading I) hf hg
    let old := fun j => φold (linearChartCoordinate I f hf j)
    φnew ((Away.map F z) (linearChartCoordinate I z hz i)) =
      (a : R) *
        ((M.map (AllCharacteristics.GradedChart.baseMap (grading I) (z := f * g))).mulVec old) i := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  let F := projectiveMatrixGradingMap M
  let g := F z
  have hg : g ∈ grading I 1 := F.map_mem hz
  let R := Away (grading I) (f * g)
  let φold : Away (grading I) f →+* R := awayMap (grading I) hg rfl
  let φnew : Away (grading I) g →+* R := awayMap (grading I) hf (mul_comm f g)
  let a := AllCharacteristics.GradedChart.overlapCoordinateUnit (grading I) hf hg
  let old := fun j => φold (linearChartCoordinate I f hf j)
  let new := fun j => φnew (linearChartCoordinate I g hg j)
  let b := AllCharacteristics.GradedChart.baseMap (grading I) (z := f * g)
  change φnew ((Away.map F z) (linearChartCoordinate I z hz i)) =
    (a : R) * ((M.map b).mulVec old) i
  have hcoords (j : Fin n) : new j = (a : R) * old j := by
    have h := AllCharacteristics.GradedChart.normalized_overlap_mul
      (grading I) hf hg (coordinate I j) (coordinate_mem I j)
    have hscaled := congrArg (fun r : R => (a : R) * r) h
    change (a : R) * ((↑(a⁻¹) : R) * new j) = (a : R) * old j at hscaled
    have ha : (a : R) * (↑(a⁻¹) : R) = 1 := a.val_inv
    rw [← mul_assoc, ha, one_mul] at hscaled
    exact hscaled
  have hmatrix :
      (M.map (AllCharacteristics.GradedChart.baseMap (grading I) (z := g))).map φnew =
        M.map b := by
    apply Matrix.ext
    intro j k
    exact AllCharacteristics.GradedChart.awayMap_baseMap
      (grading I) hf (mul_comm f g) (M j k)
  have hmap :
      φnew (((M.map (AllCharacteristics.GradedChart.baseMap (grading I) (z := g))).mulVec
        (linearChartCoordinate I g hg)) i) = ((M.map b).mulVec new) i := by
    exact (RingHom.map_mulVec φnew
      (M.map (AllCharacteristics.GradedChart.baseMap (grading I) (z := g)))
      (linearChartCoordinate I g hg) i).trans
        (congrArg (fun A => A.mulVec new i) hmatrix)
  calc
    _ = φnew (((M.map (AllCharacteristics.GradedChart.baseMap (grading I) (z := g))).mulVec
        (linearChartCoordinate I g hg)) i) :=
      congrArg φnew (projectiveMatrixChart_normalized_coordinates M z hz i)
    _ = ((M.map b).mulVec new) i := hmap
    _ = ((M.map b).mulVec (fun j => (a : R) * old j)) i :=
      congrArg (fun v => (M.map b).mulVec v i) (funext hcoords)
    _ = (a : R) * ((M.map b).mulVec old) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_left_comm _ _ _

end PfaffianDescent

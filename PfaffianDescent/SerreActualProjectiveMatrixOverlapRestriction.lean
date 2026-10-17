import PfaffianDescent.SerreActualProjectiveMatrixOverlapCoordinates

/-! The genuine regular overlap-coordinate formula on every further
coefficient-ring restriction, retaining its actual invertible ratio. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem projectiveMatrixOverlap_restricted_normalized_coordinates
    {K : Type u} [Field K] {S : Type v} [CommRing S] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K)
    (f z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hf : f ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (φ : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
      (f * projectiveMatrixGradingMap M z) →+* S) (i : Fin n) :
    let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
    let F := projectiveMatrixGradingMap M
    let g := F z
    let hg := F.map_mem hz
    let φold : Away (grading I) f →+* Away (grading I) (f * g) :=
      awayMap (grading I) hg rfl
    let φnew : Away (grading I) g →+* Away (grading I) (f * g) :=
      awayMap (grading I) hf (mul_comm f g)
    let a := AllCharacteristics.GradedChart.overlapCoordinateUnit (grading I) hf hg
    let β := φ.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := f * g))
    φ (φnew ((Away.map F z) (linearChartCoordinate I z hz i))) =
      φ (a : Away (grading I) (f * g)) *
        ((M.map β).mulVec (fun j => φ (φold (linearChartCoordinate I f hf j)))) i := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  let F := projectiveMatrixGradingMap M
  let g := F z
  let hg := F.map_mem hz
  let φold : Away (grading I) f →+* Away (grading I) (f * g) :=
    awayMap (grading I) hg rfl
  let β := AllCharacteristics.GradedChart.baseMap (grading I) (z := f * g)
  have h := congrArg φ (projectiveMatrixOverlap_normalized_coordinates M f z hf hz i)
  rw [map_mul] at h
  exact h.trans (congrArg
    (fun s => φ (AllCharacteristics.GradedChart.overlapCoordinateUnit (grading I) hf hg) * s)
    (RingHom.map_mulVec φ (M.map β) (fun j => φold (linearChartCoordinate I f hf j)) i))

end PfaffianDescent

import PfaffianDescent.QuadraticSkewActualMixedSecantAdapter
import PfaffianDescent.QuadraticSkewSmoothOriginalCubicNonvanishing
import AllCharacteristics.ProjectiveFiberSmoothness
import PfaffianDescent.CubicClosedPointSerreSurfaceCoordinatesChange
/-! SOURCE ONLY / UNVERIFIED. Smoothness of the ORIGINAL ground cubic
internally excludes either mixed block being zero, over the actual line
field and actual paired coordinate frame. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.MixedNonvanishing
open MvPolynomial Module AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective
open MixedNormalForm OriginalBridge ActualSecant SmoothNonvanishing QuarticNet
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

def leftLineIdeal : Ideal (MvPolynomial (Fin 4) E) := Ideal.span {X 2, X 3}
def rightLineIdeal : Ideal (MvPolynomial (Fin 4) E) := Ideal.span {X 0, X 1}

theorem mixed_leftPolynomial_mem_rightLineSquare (G : MvPolynomial (Fin 4) E) :
    leftMixedPolynomial G ∈ (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 := by
  classical
  have h₀ : X 0 ∈ (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E)) :=
    Ideal.subset_span (by simp [rightLineIdeal])
  have h₁ : X 1 ∈ (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E)) :=
    Ideal.subset_span (by simp [rightLineIdeal])
  have h₀₀ : X 0 ^ 2 ∈ (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 :=
    Ideal.pow_mem_pow h₀ 2
  have h₀₁ : X 0 * X 1 ∈ (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul h₀ h₁
  have h₁₁ : X 1 ^ 2 ∈ (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 :=
    Ideal.pow_mem_pow h₁ 2
  rw [leftMixedPolynomial_eq_secant_left]
  unfold leftMixedValue
  apply Ideal.add_mem
  · apply Ideal.add_mem
    · exact Ideal.mul_mem_right _ _ h₀₀
    · exact Ideal.mul_mem_right _ _ h₀₁
  · exact Ideal.mul_mem_right _ _ h₁₁

theorem mixed_rightPolynomial_mem_leftLineSquare (G : MvPolynomial (Fin 4) E) :
    rightMixedPolynomial G ∈ (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 := by
  classical
  have h₂ : X 2 ∈ (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E)) :=
    Ideal.subset_span (by simp [leftLineIdeal])
  have h₃ : X 3 ∈ (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E)) :=
    Ideal.subset_span (by simp [leftLineIdeal])
  have h₂₂ : X 2 ^ 2 ∈ (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 :=
    Ideal.pow_mem_pow h₂ 2
  have h₂₃ : X 2 * X 3 ∈ (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul h₂ h₃
  have h₃₃ : X 3 ^ 2 ∈ (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 :=
    Ideal.pow_mem_pow h₃ 2
  rw [rightMixedPolynomial_eq_secant_right]
  unfold rightMixedValue
  apply Ideal.add_mem
  · apply Ideal.add_mem
    · exact Ideal.mul_mem_right _ _ h₂₂
    · exact Ideal.mul_mem_right _ _ h₂₃
  · exact Ideal.mul_mem_right _ _ h₃₃

theorem eval_leftLineIdeal_zero (q : MvPolynomial (Fin 4) E)
    (hq : q ∈ (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E))) :
    MvPolynomial.eval₂ (RingHom.id E) (Pi.single 0 1) q = 0 := by
  have hle : (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ≤
      RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id E) (Pi.single 0 1)) := by
    apply Ideal.span_le.mpr
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> simp
  exact hle hq

theorem eval_rightLineIdeal_zero (q : MvPolynomial (Fin 4) E)
    (hq : q ∈ (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E))) :
    MvPolynomial.eval₂ (RingHom.id E) (Pi.single 2 1) q = 0 := by
  have hle : (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ≤
      RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id E) (Pi.single 2 1)) := by
    apply Ideal.span_le.mpr
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> simp
  exact hle hq

/-- Both blocks are nonzero for any smooth actual cubic in the derived
coordinate-line position. Nonzero line vectors are explicit coordinate
vectors, requiring neither an infinite field nor a ground rational point. -/
theorem smooth_mixed_cubic_blocks_ne_zero
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3) (hG₀ : G ≠ 0)
    [Smooth (hypersurfaceToBase G hG)]
    (hLeft : G ∈ (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E)))
    (hRight : G ∈ (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E))) :
    blockPiece 2 G ≠ 0 ∧ blockPiece 1 G ≠ 0 := by
  have hDecomp := cubic_eq_two_mixed_block_pieces G hG hLeft hRight
  constructor
  · intro hzero
    have hGRight : G = rightMixedPolynomial G := by
      rw [hzero, zero_add] at hDecomp
      exact hDecomp.trans (blockPiece_one_eq_rightMixedPolynomial G hG)
    have hSquare : G ∈ (leftLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 := by
      rw [hGRight]
      exact mixed_rightPolynomial_mem_leftLineSquare G
    have hx : (Pi.single 0 1 : Fin 4 → E) ≠ 0 := by
      intro h
      have h₀ := congrFun h 0
      simpa using h₀
    exact smooth_original_cubic_not_mem_square G hG hG₀ (RingHom.id E)
      (Pi.single 0 1) hx leftLineIdeal eval_leftLineIdeal_zero hSquare
  · intro hzero
    have hGLeft : G = leftMixedPolynomial G := by
      rw [hzero, add_zero] at hDecomp
      exact hDecomp.trans (blockPiece_two_eq_leftMixedPolynomial G hG)
    have hSquare : G ∈ (rightLineIdeal : Ideal (MvPolynomial (Fin 4) E)) ^ 2 := by
      rw [hGLeft]
      exact mixed_leftPolynomial_mem_rightLineSquare G
    have hx : (Pi.single 2 1 : Fin 4 → E) ≠ 0 := by
      intro h
      have h₂ := congrFun h 2
      simpa using h₂
    exact smooth_original_cubic_not_mem_square G hG hG₀ (RingHom.id E)
      (Pi.single 2 1) hx rightLineIdeal eval_rightLineIdeal_zero hSquare

/-- Original-ground wrapper: coefficient base change and actual frame
change preserve smoothness internally. No Smooth premise for G is added. -/
theorem original_smooth_cubic_paired_blocks_ne_zero
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (C : Basis (Fin 4) E (Fin 4 → E)) (P : Matrix (Fin 4) (Fin 4) E)
    (hC : matchingEdgeProjectorMatrix C = P)
    (hLines : MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal P).toIdeal ∧
      MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal (1 - P)).toIdeal) :
    let G := linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)
    blockPiece 2 G ≠ 0 ∧ blockPiece 1 G ≠ 0 := by
  let FE := MvPolynomial.map (algebraMap k E) F
  have hFE : FE.IsHomogeneous 3 := hF.map _
  have hFE₀ : FE ≠ 0 := by
    intro hz
    apply hF₀
    apply MvPolynomial.map_injective (algebraMap k E) (algebraMap k E).injective
    simpa only [map_zero] using hz
  letI : Smooth (hypersurfaceToBase FE hFE) :=
    smooth_hypersurfaceToBase_map (algebraMap k E) F hF
  let M := basisCoordinateMatrix C
  let G := linearSubstitution M FE
  have hG : G.IsHomogeneous 3 := linearSubstitution_homogeneous M hFE
  have hG₀ : G ≠ 0 := cubicClosedPointSerreSurfaceCoordinates_nonzero M
    (basisCoordinateMatrix_isUnit C) FE hFE₀
  letI : Smooth (hypersurfaceToBase G hG) :=
    cubicClosedPointSerreSurfaceCoordinates_smooth M (basisCoordinateMatrix_isUnit C) FE hFE
  obtain ⟨hLeft, hRight⟩ := original_cubic_paired_coordinate_line_memberships C P hC FE hLines
  exact smooth_mixed_cubic_blocks_ne_zero G hG hG₀ hLeft hRight

end PfaffianDescent.QuadraticSkewRationality.MixedNonvanishing

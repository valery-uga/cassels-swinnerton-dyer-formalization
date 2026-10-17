import PfaffianDescent.MatchingProjectorIdealBaseChange
import PfaffianDescent.QuarticConjugateJets
import PfaffianDescent.MatchingCoordinateLineSchemes

/-! SOURCE ONLY, UNVERIFIED. The projector ideal equals the EXACT original
line ideal obtained by inverse-GL transport of the coordinate matching line.
This is a polynomial ideal equality, not only equality of geometric points. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial Module
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def basisReprCoordinateMatrix (B : Basis (Fin 4) K (Fin 4 → K)) :
    Matrix (Fin 4) (Fin 4) K := fun i n => B.repr (Pi.single n 1) i

theorem basisReprCoordinateMatrix_eq_inverse
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    basisReprCoordinateMatrix B = (basisCoordinateMatrix B)⁻¹ := by
  classical
  let M := basisCoordinateMatrix B
  let R := basisReprCoordinateMatrix B
  have hMR : M * R = 1 := by
    ext m n
    have h := congrFun (B.sum_repr (Pi.single n (1 : K))) m
    change ∑ i, B i m * B.repr (Pi.single n 1) i = if m = n then 1 else 0
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      eq_comm, mul_comm] using h
  have hdet : IsUnit M.det := basisCoordinateMatrix_isUnit B
  calc
    R = 1 * R := (one_mul _).symm
    _ = (M⁻¹ * M) * R := by rw [Matrix.nonsing_inv_mul M hdet]
    _ = M⁻¹ * (M * R) := mul_assoc _ _ _
    _ = M⁻¹ := by rw [hMR, mul_one]

theorem matchingEdgeComplementMatrix_factor
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    1 - matchingEdgeProjectorMatrix B =
      basisCoordinateMatrix B * Matrix.diagonal ![0, 0, 1, 1] *
        (basisCoordinateMatrix B)⁻¹ := by
  classical
  rw [← basisReprCoordinateMatrix_eq_inverse B]
  ext m n
  have h := congrFun (B.sum_repr (Pi.single n (1 : K))) m
  have hsum : B 0 m * B.repr (Pi.single n 1) 0 +
      B 1 m * B.repr (Pi.single n 1) 1 +
      B 2 m * B.repr (Pi.single n 1) 2 +
      B 3 m * B.repr (Pi.single n 1) 3 = if m = n then 1 else 0 := by
    simpa [Fin.sum_univ_four, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.single_apply, eq_comm, mul_comm] using h
  simp only [Matrix.sub_apply, Matrix.one_apply, matchingEdgeProjectorMatrix]
  simp [Matrix.mul_apply, Matrix.diagonal, basisCoordinateMatrix,
    basisReprCoordinateMatrix, Fin.sum_univ_four]
  linear_combination -hsum

/-- Invertible row operations preserve the generated ideal, for actual
polynomial equations. No saturation/reduction is used. -/
theorem polynomialRowIdeal_mulVec_le
    (M : Matrix (Fin 4) (Fin 4) K) (Q : Fin 4 → MvPolynomial (Fin 4) K) :
    Ideal.span (Set.range ((M.map C).mulVec Q)) ≤ Ideal.span (Set.range Q) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨m, rfl⟩
  change ∑ j, C (M m j) * Q j ∈ Ideal.span (Set.range Q)
  exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨j, rfl⟩))

theorem polynomialRowIdeal_mulVec_eq
    (M : Matrix (Fin 4) (Fin 4) K) (hdet : IsUnit M.det)
    (Q : Fin 4 → MvPolynomial (Fin 4) K) :
    Ideal.span (Set.range ((M.map C).mulVec Q)) = Ideal.span (Set.range Q) := by
  apply le_antisymm (polynomialRowIdeal_mulVec_le M Q)
  have h := polynomialRowIdeal_mulVec_le M⁻¹ ((M.map C).mulVec Q)
  have hQ : ((M⁻¹).map C).mulVec ((M.map C).mulVec Q) = Q := by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul M hdet,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  simpa only [hQ] using h

theorem projectorLineIdeal_eq_originalMatchingLine
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    (projectorLineIdeal (matchingEdgeProjectorMatrix B)).toIdeal =
      (coordinateMatchingLineIdeal (K := K) false).toIdeal.map
        (linearSubstitution (basisCoordinateMatrix B)⁻¹).toRingHom := by
  classical
  let M := basisCoordinateMatrix B
  let D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![0, 0, 1, 1]
  have hrow : linearCoordinate (M * D * M⁻¹) =
      (M.map C).mulVec (linearCoordinate (D * M⁻¹)) := by
    funext m
    simp only [linearCoordinate]
    rw [mul_assoc, Matrix.map_mul, ← Matrix.mulVec_mulVec]
    rfl
  change Ideal.span (Set.range (linearCoordinate (1 - matchingEdgeProjectorMatrix B))) = _
  rw [matchingEdgeComplementMatrix_factor B]
  change Ideal.span (Set.range (linearCoordinate (M * D * M⁻¹))) = _
  rw [hrow, polynomialRowIdeal_mulVec_eq M (basisCoordinateMatrix_isUnit B)]
  have hcoords : Set.range (linearCoordinate (D * M⁻¹)) =
      {0, linearCoordinate M⁻¹ 2, linearCoordinate M⁻¹ 3} := by
    ext q
    constructor
    · rintro ⟨m, rfl⟩
      fin_cases m <;>
        simp [D, linearCoordinate, Matrix.mul_apply, Matrix.diagonal,
          Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      intro h
      rcases h with rfl | rfl | rfl
      · refine ⟨0, ?_⟩
        simp [D, linearCoordinate, Matrix.mul_apply, Matrix.diagonal,
          Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      · refine ⟨2, ?_⟩
        simp [D, linearCoordinate, Matrix.mul_apply, Matrix.diagonal,
          Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      · refine ⟨3, ?_⟩
        simp [D, linearCoordinate, Matrix.mul_apply, Matrix.diagonal,
          Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [hcoords]
  change Ideal.span {0, linearCoordinate M⁻¹ 2, linearCoordinate M⁻¹ 3} =
    (Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) K))).map
      (linearSubstitution M⁻¹).toRingHom
  rw [Ideal.map_span, Set.image_pair]
  have hx2 : (linearSubstitution M⁻¹).toRingHom (X 2) = linearCoordinate M⁻¹ 2 :=
    linearSubstitution_X M⁻¹ 2
  have hx3 : (linearSubstitution M⁻¹).toRingHom (X 3) = linearCoordinate M⁻¹ 3 :=
    linearSubstitution_X M⁻¹ 3
  rw [hx2, hx3, Ideal.span_insert_zero]

end PfaffianDescent.QuarticNet

import PfaffianDescent.BasisMatchingProjectorActualLineIdeal
import PfaffianDescent.MatchingProjectorIntersectionGaloisStability

/-! SOURCE ONLY, UNVERIFIED. The other actual line and the WHOLE union
are the inverse-GL transport of the coordinate ideals. No radical is taken. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial Module
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Both matching projectors are expressed in the SAME actual basis. -/
theorem matchingEdgeProjectorMatrix_factor
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    matchingEdgeProjectorMatrix B = basisCoordinateMatrix B *
      Matrix.diagonal ![1, 1, 0, 0] * (basisCoordinateMatrix B)⁻¹ := by
  classical
  let M := basisCoordinateMatrix B
  let D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![0, 0, 1, 1]
  have hComp : 1 - matchingEdgeProjectorMatrix B = M * D * M⁻¹ :=
    matchingEdgeComplementMatrix_factor B
  have hOne : M * (1 : Matrix (Fin 4) (Fin 4) K) * M⁻¹ = 1 := by
    rw [mul_one, Matrix.mul_nonsing_inv M (basisCoordinateMatrix_isUnit B)]
  have hD : (1 : Matrix (Fin 4) (Fin 4) K) - D = Matrix.diagonal ![1, 1, 0, 0] := by
    ext m n
    fin_cases m <;> fin_cases n <;>
      simp [D, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal]
  calc
    matchingEdgeProjectorMatrix B = 1 - (1 - matchingEdgeProjectorMatrix B) := by abel
    _ = M * 1 * M⁻¹ - M * D * M⁻¹ := by rw [hOne, hComp]
    _ = M * (1 - D) * M⁻¹ := by rw [mul_sub, sub_mul]
    _ = _ := by rw [hD]

theorem projectorComplementLineIdeal_eq_originalMatchingLine
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    (projectorLineIdeal (1 - matchingEdgeProjectorMatrix B)).toIdeal =
      (coordinateMatchingLineIdeal (K := K) true).toIdeal.map
        (linearSubstitution (basisCoordinateMatrix B)⁻¹).toRingHom := by
  classical
  let M := basisCoordinateMatrix B
  let D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![1, 1, 0, 0]
  have hrow : linearCoordinate (M * D * M⁻¹) =
      (M.map C).mulVec (linearCoordinate (D * M⁻¹)) := by
    funext m
    simp only [linearCoordinate]
    rw [mul_assoc, Matrix.map_mul, ← Matrix.mulVec_mulVec]
    rfl
  change Ideal.span (Set.range (linearCoordinate (1 - (1 - matchingEdgeProjectorMatrix B)))) = _
  have hBack : 1 - (1 - matchingEdgeProjectorMatrix B) = matchingEdgeProjectorMatrix B := by abel
  rw [hBack]
  rw [matchingEdgeProjectorMatrix_factor B]
  change Ideal.span (Set.range (linearCoordinate (M * D * M⁻¹))) = _
  rw [hrow, polynomialRowIdeal_mulVec_eq M (basisCoordinateMatrix_isUnit B)]
  have hcoords : Set.range (linearCoordinate (D * M⁻¹)) =
      {0, linearCoordinate M⁻¹ 0, linearCoordinate M⁻¹ 1} := by
    ext q
    constructor
    · rintro ⟨m, rfl⟩
      fin_cases m <;>
        simp [D, linearCoordinate, Matrix.mul_apply, Matrix.diagonal,
          Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      intro h
      rcases h with rfl | rfl | rfl
      · refine ⟨2, ?_⟩
        simp [D, linearCoordinate, Matrix.mul_apply, Matrix.diagonal,
          Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      · refine ⟨0, ?_⟩
        simp [D, linearCoordinate, Matrix.mul_apply, Matrix.diagonal,
          Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      · refine ⟨1, ?_⟩
        simp [D, linearCoordinate, Matrix.mul_apply, Matrix.diagonal,
          Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [hcoords]
  change Ideal.span {0, linearCoordinate M⁻¹ 0, linearCoordinate M⁻¹ 1} =
    (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) K))).map
      (linearSubstitution M⁻¹).toRingHom
  rw [Ideal.map_span, Set.image_pair]
  have hx0 : (linearSubstitution M⁻¹).toRingHom (X 0) = linearCoordinate M⁻¹ 0 :=
    linearSubstitution_X M⁻¹ 0
  have hx1 : (linearSubstitution M⁻¹).toRingHom (X 1) = linearCoordinate M⁻¹ 1 :=
    linearSubstitution_X M⁻¹ 1
  rw [hx0, hx1, Ideal.span_insert_zero]


theorem matchingProjectorIntersectionIdeal_eq_originalMatchingUnion
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    (matchingProjectorIntersectionIdeal (matchingEdgeProjectorMatrix B)).toIdeal =
      ((coordinateMatchingLineIdeal (K := K) false).toIdeal ⊓
        (coordinateMatchingLineIdeal (K := K) true).toIdeal).map
          (linearSubstitution (basisCoordinateMatrix B)⁻¹).toRingHom := by
  change (projectorLineIdeal (matchingEdgeProjectorMatrix B)).toIdeal ⊓
      (projectorLineIdeal (1 - matchingEdgeProjectorMatrix B)).toIdeal = _
  rw [projectorLineIdeal_eq_originalMatchingLine B,
    projectorComplementLineIdeal_eq_originalMatchingLine B]
  let e := linearSubstitutionEquiv (basisCoordinateMatrix B)⁻¹
    (Matrix.isUnit_nonsing_inv_det (basisCoordinateMatrix B) (basisCoordinateMatrix_isUnit B))
  exact ((Ideal.relIsoOfBijective e.toRingHom e.bijective).symm.map_inf _ _).symm

end PfaffianDescent.QuarticNet

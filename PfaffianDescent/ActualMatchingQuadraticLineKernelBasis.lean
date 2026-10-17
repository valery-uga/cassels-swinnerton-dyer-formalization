import PfaffianDescent.FiniteCoordinateSpanFieldExtensionRank
import PfaffianDescent.ActualMatchingGroundIntersectionDescent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! SOURCE ONLY, UNVERIFIED. Derives a genuine rank-two E-vector kernel
of the actual line equations (1-P)X, with an actual Fin2 basis. This supplies
line structure over E, not merely a scheme whose scalar extension is a line.
A projectivized kernel/P1 scheme Iso is a further construction. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]

theorem matchingEdgeComplementMatrix_rank_two
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    (1 - matchingEdgeProjectorMatrix B).rank = 2 := by
  classical
  let M := basisCoordinateMatrix B
  have hM : IsUnit M.det := basisCoordinateMatrix_isUnit B
  rw [matchingEdgeComplementMatrix_factor B]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det M⁻¹ _
      (Matrix.isUnit_nonsing_inv_det M hM),
    Matrix.rank_mul_eq_right_of_isUnit_det M _ hM, Matrix.rank_diagonal]
  norm_num [Fintype.card_subtype, Fin.card_filter_univ_succ]


theorem matchingEdgeProjectorMatrix_rank_two
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    (matchingEdgeProjectorMatrix B).rank = 2 := by
  classical
  let M := basisCoordinateMatrix B
  let D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![0, 0, 1, 1]
  have hM : IsUnit M.det := basisCoordinateMatrix_isUnit B
  have hFactor : matchingEdgeProjectorMatrix B =
      M * Matrix.diagonal ![1, 1, 0, 0] * M⁻¹ := by
    have hComp : 1 - matchingEdgeProjectorMatrix B = M * D * M⁻¹ :=
      matchingEdgeComplementMatrix_factor B
    have hOne : M * (1 : Matrix (Fin 4) (Fin 4) K) * M⁻¹ = 1 := by
      rw [mul_one, Matrix.mul_nonsing_inv M hM]
    have hD : (1 : Matrix (Fin 4) (Fin 4) K) - D = Matrix.diagonal ![1, 1, 0, 0] := by
      ext m n
      fin_cases m <;> fin_cases n <;>
        simp [D, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal]
    calc
      matchingEdgeProjectorMatrix B = 1 - (1 - matchingEdgeProjectorMatrix B) := by abel
      _ = M * 1 * M⁻¹ - M * D * M⁻¹ := by rw [hOne, hComp]
      _ = M * (1 - D) * M⁻¹ := by rw [mul_sub, sub_mul]
      _ = M * Matrix.diagonal ![1, 1, 0, 0] * M⁻¹ := by rw [hD]
  rw [hFactor, Matrix.rank_mul_eq_left_of_isUnit_det M⁻¹ _
      (Matrix.isUnit_nonsing_inv_det M hM),
    Matrix.rank_mul_eq_right_of_isUnit_det M _ hM, Matrix.rank_diagonal]
  norm_num [Fintype.card_subtype, Fin.card_filter_univ_succ]

omit [IsGalois k K] in
theorem intermediateMatchingLine_kernel_rank_two
    (E : IntermediateField k K) (P : Matrix (Fin 4) (Fin 4) E)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B) :
    finrank E (LinearMap.ker (1 - P).mulVecLin) = 2 := by
  classical
  have hN : (1 - P).map (algebraMap E K) = 1 - matchingEdgeProjectorMatrix B := by
    change (1 - P).map E.val.toRingHom = 1 - matchingEdgeProjectorMatrix B
    have hMap : (1 - P).map E.val.toRingHom = 1 - P.map E.val.toRingHom := by
      ext m n
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
      split_ifs <;> simp
    simpa only [hP] using hMap
  have hRank : (1 - P).rank = 2 := by
    rw [← PfaffianDescent.finiteCoordinateMatrix_fieldExtension_rank (K := K) (1 - P), hN]
    exact matchingEdgeComplementMatrix_rank_two B
  have hNullity := LinearMap.finrank_range_add_finrank_ker (1 - P).mulVecLin
  change (1 - P).rank + finrank E (LinearMap.ker (1 - P).mulVecLin) =
    finrank E (Fin 4 → E) at hNullity
  rw [hRank, Module.finrank_pi, Fintype.card_fin] at hNullity
  omega


omit [IsGalois k K] in
theorem intermediateMatchingOtherLine_kernel_rank_two
    (E : IntermediateField k K) (P : Matrix (Fin 4) (Fin 4) E)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B) :
    finrank E (LinearMap.ker P.mulVecLin) = 2 := by
  have hRank : P.rank = 2 := by
    rw [← PfaffianDescent.finiteCoordinateMatrix_fieldExtension_rank (K := K) P]
    change (P.map E.val.toRingHom).rank = 2
    rw [hP]
    exact matchingEdgeProjectorMatrix_rank_two B
  have hNullity := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  change P.rank + finrank E (LinearMap.ker P.mulVecLin) =
    finrank E (Fin 4 → E) at hNullity
  rw [hRank, Module.finrank_pi, Fintype.card_fin] at hNullity
  omega

theorem actualMatching_ground_intersection_with_line_kernel
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f) :
    let B := (conjugateBasis full p hs).reindex pi.symm
    ∃ E : IntermediateField k K, ∃ _ : FiniteDimensional k E,
      finrank k E = 2 ∧ IsGalois k E ∧
      E = IntermediateField.adjoin k (Set.range (fun m => B 0 m + B 1 m)) ∧
      ∃ P : Matrix (Fin 4) (Fin 4) E,
        P.map E.val.toRingHom = matchingEdgeProjectorMatrix B ∧
        finrank E (LinearMap.ker (1 - P).mulVecLin) = 2 ∧
        Nonempty (Basis (Fin 2) E (LinearMap.ker (1 - P).mulVecLin)) ∧
        finrank E (LinearMap.ker P.mulVecLin) = 2 ∧
        Nonempty (Basis (Fin 2) E (LinearMap.ker P.mulVecLin)) ∧
        ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k),
          J.toIdeal.map (MvPolynomial.map (algebraMap k E)) =
            (projectorLineIdeal P).toIdeal ⊓ (projectorLineIdeal (1 - P)).toIdeal := by
  classical
  dsimp only
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP, J, hJ⟩ :=
    actualMatching_ground_intersection_descent full p v hs l hl pi a f ha hU
  have hKernel := intermediateMatchingLine_kernel_rank_two E P _ hP
  have hOtherKernel := intermediateMatchingOtherLine_kernel_rank_two E P _ hP
  refine ⟨E, hFD, hdeg, hGal, hE, P, hP, hKernel,
    ⟨Module.finBasisOfFinrankEq E _ hKernel⟩, hOtherKernel,
    ⟨Module.finBasisOfFinrankEq E _ hOtherKernel⟩, J, hJ⟩

end PfaffianDescent.QuarticNet

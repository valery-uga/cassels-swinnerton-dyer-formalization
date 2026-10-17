import PfaffianDescent.FrameGeneratorChange
import PfaffianDescent.ConstantGeneratorChange
import PfaffianDescent.HomogeneousMatrixColumns

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K]

noncomputable def recombinedFrameMatrix
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (D : Matrix (Fin 5) (Fin 5) K) : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 4) K) :=
  (D⁻¹.map C) * ((frameMatrix X).map E)

lemma recombinedFrameMatrix_action
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (D : Matrix (Fin 5) (Fin 5) K) (v : Fin 5 → MvPolynomial (Fin 4) K) :
    (recombinedFrameMatrix E D).mulVec v = (D⁻¹.map C).mulVec (changedFrameMiddle E v) :=
  (Matrix.mulVec_mulVec _ _ _).symm

/-- Changing the quadratic generators transports the entire module of syzygies. -/
theorem recombinedFrameMatrix_exact
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (D : Matrix (Fin 5) (Fin 5) K) (hD : IsUnit D.det)
    (q : Fin 5 → MvPolynomial (Fin 4) K)
    (hq : ∀ j, q j = ∑ i, D i j • E (frameRelations i)) :
    LinearMap.range (recombinedFrameMatrix E D).mulVecLin =
      LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin 4) K) q) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change Fintype.linearCombination _ q ((recombinedFrameMatrix E D).mulVec w) = 0
    rw [polynomial_linearCombination_generator_change _ q D hq,
      recombinedFrameMatrix_action, constant_matrix_mul_invVec D hD]
    exact changedFrameLast_middle E w
  · intro hv
    have hzero : changedFrameLast E ((D.map C).mulVec v) = 0 := by
      change Fintype.linearCombination (MvPolynomial (Fin 4) K) (fun i => E (frameRelations i))
        ((D.map C).mulVec v) = 0
      rw [← polynomial_linearCombination_generator_change _ q D hq]
      exact hv
    obtain ⟨w, hw⟩ := changedFrameLast_kernel E _ hzero
    refine ⟨w, ?_⟩
    change (recombinedFrameMatrix E D).mulVec w = v
    rw [recombinedFrameMatrix_action, hw, constant_matrix_inv_mulVec D hD]

lemma recombinedFrameMatrix_homogeneous
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hE : ∀ d (p : MvPolynomial (Fin 4) K), p.IsHomogeneous d → (E p).IsHomogeneous d)
    (D : Matrix (Fin 5) (Fin 5) K) (i j : Fin 5) :
    (recombinedFrameMatrix E D i j).IsHomogeneous 1 := by
  change (∑ k, C (D⁻¹ i k) * E (frameMatrix X k j)) ∈ homogeneousSubmodule (Fin 4) K 1
  exact Submodule.sum_mem _ (fun k _ => (hE 1 _ (frameMatrix_homogeneous k j)).C_mul _)

lemma recombinedFrameMatrix_kernel
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (D : Matrix (Fin 5) (Fin 5) K) (hD : IsUnit D.det)
    (v : Fin 5 → MvPolynomial (Fin 4) K)
    (hv : (recombinedFrameMatrix E D).mulVec v = 0) :
    ∃ r : MvPolynomial (Fin 4) K, v = r • (fun i => E (frameRelations i)) := by
  have he := congrArg (D.map (C : K →+* MvPolynomial (Fin 4) K)).mulVec hv
  rw [recombinedFrameMatrix_action, constant_matrix_mul_invVec D hD, Matrix.mulVec_zero] at he
  obtain ⟨r, hr⟩ := changedFrameMiddle_kernel E v he
  exact ⟨r, hr.symm⟩

lemma recombinedFrameMatrix_columns_independent
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hE : ∀ d (p : MvPolynomial (Fin 4) K), p.IsHomogeneous d → (E p).IsHomogeneous d)
    (D : Matrix (Fin 5) (Fin 5) K) (hD : IsUnit D.det) :
    LinearIndependent K (fun j => fun i => recombinedFrameMatrix E D i j) :=
  matrix_columns_independent_of_positive_kernel _ (fun i => E (frameRelations i)) 0 2 (by decide)
    (hE 2 _ (frameRelations_homogeneous 0)) ((changedFrameRelations_independent E).ne_zero 0)
    (recombinedFrameMatrix_kernel E D hD)

end
end PfaffianDescent

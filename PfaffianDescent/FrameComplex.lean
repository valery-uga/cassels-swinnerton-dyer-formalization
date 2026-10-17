import PfaffianDescent.FrameKernel
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators

section
variable {K : Type*} [Field K]

noncomputable def frameFirstMap : MvPolynomial (Fin 4) K →ₗ[MvPolynomial (Fin 4) K]
    (Fin 5 → MvPolynomial (Fin 4) K) :=
  LinearMap.toSpanSingleton _ _ (frameRelations (K := K))

noncomputable def frameMiddleMap : (Fin 5 → MvPolynomial (Fin 4) K) →ₗ[MvPolynomial (Fin 4) K]
    (Fin 5 → MvPolynomial (Fin 4) K) := (frameMatrix MvPolynomial.X).mulVecLin

noncomputable def frameLastMap : (Fin 5 → MvPolynomial (Fin 4) K) →ₗ[MvPolynomial (Fin 4) K]
    MvPolynomial (Fin 4) K := Fintype.linearCombination _ (frameRelations (K := K))

/-- The first nonzero map of the frame resolution is injective. -/
theorem frameFirstMap_injective : Function.Injective (frameFirstMap (K := K)) := by
  apply (injective_iff_map_eq_zero frameFirstMap).mpr
  intro r hr
  have h := congrFun hr 0
  change r * (X 0 * X 2 - X 0 * X 1) = 0 at h
  rw [← mul_sub] at h
  have hq : (X 0 : MvPolynomial (Fin 4) K) * (X 2 - X 1) ≠ 0 :=
    mul_ne_zero (MvPolynomial.X_ne_zero 0) frame_difference_prime.ne_zero
  exact (mul_eq_zero.mp h).resolve_right hq

/-- Exactness at the left free module of rank five, as equality of actual
submodules of the polynomial module. -/
theorem frameFirstMap_range_eq_middle_ker :
    LinearMap.range (frameFirstMap (K := K)) = LinearMap.ker frameMiddleMap := by
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    change (frameMatrix MvPolynomial.X).mulVec (r • frameRelations (K := K)) = 0
    rw [Matrix.mulVec_smul, ← frameQuadrics_X, frameMatrix_mul_quadrics, smul_zero]
  · intro hv
    obtain ⟨r, hr⟩ := frameMatrix_kernel v hv
    exact ⟨r, hr.symm⟩

lemma frameMatrix_transpose (x : Vec (MvPolynomial (Fin 4) K) 4) :
    (frameMatrix x).transpose = -frameMatrix x := by
  funext i j
  exact (frameMatrix_alternating x).2 i j

/-- Consecutive middle and last maps have zero composite. -/
theorem frameLastMap_comp_middle :
    (frameLastMap (K := K)).comp frameMiddleMap = 0 := by
  apply LinearMap.ext
  intro v
  change (∑ i, ((frameMatrix MvPolynomial.X).mulVec v) i * frameRelations i) = 0
  change dotProduct ((frameMatrix MvPolynomial.X).mulVec v) (frameRelations (K := K)) = 0
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    frameMatrix_transpose, Matrix.neg_mulVec, ← frameQuadrics_X,
    frameMatrix_mul_quadrics, neg_zero, zero_dotProduct]

/-- The image of the last free-module map is precisely the frame ideal. -/
theorem frameLastMap_range : LinearMap.range (frameLastMap (K := K)) = frameIdeal (K := K) := by
  rw [frameLastMap, Fintype.range_linearCombination]
  rfl

/-- The quotient map is surjective and has exactly the image of the preceding map as kernel. -/
theorem frame_augmentation_exact :
    Function.Surjective (Ideal.Quotient.mkₐ K (frameIdeal (K := K))) ∧
      ∀ p : MvPolynomial (Fin 4) K,
        Ideal.Quotient.mkₐ K (frameIdeal (K := K)) p = 0 ↔ p ∈ LinearMap.range frameLastMap := by
  refine ⟨Ideal.Quotient.mkₐ_surjective K (frameIdeal (K := K)), ?_⟩
  intro p
  rw [frameLastMap_range]
  exact Ideal.Quotient.eq_zero_iff_mem

end
end PfaffianDescent

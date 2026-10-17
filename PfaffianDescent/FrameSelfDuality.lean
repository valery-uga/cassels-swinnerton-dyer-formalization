import PfaffianDescent.FrameResolution
import Mathlib.LinearAlgebra.Matrix.Dual

namespace PfaffianDescent
open Module MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K]

noncomputable def frameScalarDuality : (MvPolynomial (Fin 4) K) ≃ₗ[MvPolynomial (Fin 4) K]
    Dual (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K) :=
  (LinearMap.ringLmapEquivSelf _ _ _).symm

noncomputable def frameVectorDuality : (Fin 5 → MvPolynomial (Fin 4) K) ≃ₗ[MvPolynomial (Fin 4) K]
    Dual (MvPolynomial (Fin 4) K) (Fin 5 → MvPolynomial (Fin 4) K) :=
  dotProductEquiv _ _

@[simp] lemma frameScalarDuality_apply (r s : MvPolynomial (Fin 4) K) :
    frameScalarDuality r s = s * r := rfl

@[simp] lemma frameVectorDuality_apply (v w : Fin 5 → MvPolynomial (Fin 4) K) :
    frameVectorDuality v w = dotProduct v w := rfl

lemma frameFirstMap_apply (r : MvPolynomial (Fin 4) K) (i : Fin 5) :
    frameFirstMap r i = r * frameRelations i := rfl

lemma frameLastMap_apply (v : Fin 5 → MvPolynomial (Fin 4) K) :
    frameLastMap v = ∑ i, v i * frameRelations i := rfl

/-- The first and last differentials are dual under the canonical free-module dualities. -/
theorem frameFirstMap_dual :
    (Dual.transpose (frameFirstMap (K := K))).comp frameVectorDuality.toLinearMap =
      frameScalarDuality.toLinearMap.comp frameLastMap := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Dual.transpose_apply, LinearEquiv.coe_coe,
    frameScalarDuality_apply, frameVectorDuality_apply, dotProduct,
    frameFirstMap_apply, frameLastMap_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The alternating middle differential is its own negative dual. -/
theorem frameMiddleMap_dual :
    (Dual.transpose (frameMiddleMap (K := K))).comp frameVectorDuality.toLinearMap =
      -(frameVectorDuality.toLinearMap.comp frameMiddleMap) := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change dotProduct v ((frameMatrix X).mulVec w) =
    -dotProduct ((frameMatrix X).mulVec v) w
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, frameMatrix_transpose,
    Matrix.neg_mulVec, neg_dotProduct]

/-- The dual of the augmentation differential is the first differential. -/
theorem frameLastMap_dual :
    (Dual.transpose (frameLastMap (K := K))).comp frameScalarDuality.toLinearMap =
      frameVectorDuality.toLinearMap.comp frameFirstMap := by
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Dual.transpose_apply, LinearEquiv.coe_coe,
    frameScalarDuality_apply, frameVectorDuality_apply, dotProduct,
    frameFirstMap_apply, frameLastMap_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end PfaffianDescent

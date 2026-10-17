import PfaffianDescent.QuinticAlgebraCoordinateResolution
import PfaffianDescent.FrameMinimality

namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators
section
variable {K : Type*} [Field K]

lemma quinticFirstMap_apply (a : Vec K 5) (r : MvPolynomial (Fin 4) K) (i : Fin 5) :
    quinticFirstMap a r i = r * quinticRelations a i := rfl

lemma quinticLastMap_apply (a : Vec K 5) (v : Fin 5 → MvPolynomial (Fin 4) K) :
    quinticLastMap a v = ∑ i, v i * quinticRelations a i := rfl

/-- The first and last maps of the canonical quintic resolution are dual. -/
theorem quinticFirstMap_dual (a : Vec K 5) :
    (Dual.transpose (quinticFirstMap a)).comp frameVectorDuality.toLinearMap =
      frameScalarDuality.toLinearMap.comp (quinticLastMap a) := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Dual.transpose_apply, LinearEquiv.coe_coe,
    frameScalarDuality_apply, frameVectorDuality_apply, dotProduct,
    quinticFirstMap_apply, quinticLastMap_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The middle map is its negative dual under the standard free-module pairing. -/
theorem quinticMiddleMap_dual (a : Vec K 5) :
    (Dual.transpose (quinticMiddleMap a)).comp frameVectorDuality.toLinearMap =
      -(frameVectorDuality.toLinearMap.comp (quinticMiddleMap a)) := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change dotProduct v ((quinticPolynomialMatrix a).mulVec w) =
    -dotProduct ((quinticPolynomialMatrix a).mulVec v) w
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, quinticPolynomialMatrix_transpose,
    Matrix.neg_mulVec, neg_dotProduct]

theorem quinticLastMap_dual (a : Vec K 5) :
    (Dual.transpose (quinticLastMap a)).comp frameScalarDuality.toLinearMap =
      frameVectorDuality.toLinearMap.comp (quinticFirstMap a) := by
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Dual.transpose_apply, LinearEquiv.coe_coe,
    frameScalarDuality_apply, frameVectorDuality_apply, dotProduct,
    quinticFirstMap_apply, quinticLastMap_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- All resolution entries belong to the homogeneous maximal ideal. -/
theorem quintic_resolution_entries_minimal (a : Vec K 5) :
    (∀ i, quinticRelations a i ∈ RingHom.ker constantCoeff) ∧
    (∀ i j, quinticPolynomialMatrix a i j ∈ RingHom.ker constantCoeff) := by
  constructor
  · intro i
    exact homogeneous_constantCoeff_zero (quinticRelations_homogeneous a i) (by decide)
  · intro i j
    exact homogeneous_constantCoeff_zero (quinticPolynomialMatrix_homogeneous a i j) (by decide)

/-- Each differential becomes zero after reduction modulo the homogeneous maximal ideal. -/
theorem quintic_resolution_reduces_to_zero (a : Vec K 5) :
    (∀ r : MvPolynomial (Fin 4) K, ∀ i, constantCoeff (quinticFirstMap a r i) = 0) ∧
    (∀ v : Fin 5 → MvPolynomial (Fin 4) K, ∀ i, constantCoeff (quinticMiddleMap a v i) = 0) ∧
    (∀ v : Fin 5 → MvPolynomial (Fin 4) K, constantCoeff (quinticLastMap a v) = 0) := by
  obtain ⟨hq, hT⟩ := quintic_resolution_entries_minimal a
  change (∀ i, constantCoeff (quinticRelations a i) = 0) at hq
  change (∀ i j, constantCoeff (quinticPolynomialMatrix a i j) = 0) at hT
  refine ⟨?_, ?_, ?_⟩
  · intro r i
    rw [quinticFirstMap_apply, map_mul, hq, mul_zero]
  · intro v i
    change constantCoeff (∑ j, quinticPolynomialMatrix a i j * v j) = 0
    simp only [map_sum, map_mul, hT, zero_mul, Finset.sum_const_zero]
  · intro v
    rw [quinticLastMap_apply]
    simp only [map_sum, map_mul, hq, mul_zero, Finset.sum_const_zero]

/-- The explicit minimal resolution has the shifts `5,3,2,0`. -/
theorem quintic_resolution_degrees (a : Vec K 5) :
    (∀ i, (quinticRelations a i).IsHomogeneous (5-3)) ∧
    (∀ i j, (quinticPolynomialMatrix a i j).IsHomogeneous (3-2)) ∧
    (∀ i, (quinticRelations a i).IsHomogeneous (2-0)) :=
  ⟨quinticRelations_homogeneous a, quinticPolynomialMatrix_homogeneous a,
    quinticRelations_homogeneous a⟩

end
end PfaffianDescent

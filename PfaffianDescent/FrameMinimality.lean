import PfaffianDescent.FrameSelfDuality

namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators
section
variable {K : Type*} [Field K]

lemma homogeneous_constantCoeff_zero {σ : Type*} {p : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : d ≠ 0) : constantCoeff p = 0 := by
  exact hp.coeff_eq_zero (by simpa only [map_zero] using Ne.symm hd)

/-- Every entry of both types of differential belongs to the homogeneous maximal ideal. -/
theorem frame_resolution_entries_minimal :
    (∀ i : Fin 5, frameRelations (K := K) i ∈ RingHom.ker constantCoeff) ∧
    (∀ i j : Fin 5, frameMatrix (X : Fin 4 → MvPolynomial (Fin 4) K) i j ∈
      RingHom.ker constantCoeff) := by
  constructor
  · intro i
    exact homogeneous_constantCoeff_zero (frameRelations_homogeneous i) (by decide)
  · intro i j
    exact homogeneous_constantCoeff_zero (frameMatrix_homogeneous i j) (by decide)

/-- Modulo the homogeneous maximal ideal every differential in the free resolution is zero. -/
theorem frame_resolution_reduces_to_zero :
    (∀ r : MvPolynomial (Fin 4) K, ∀ i : Fin 5,
      constantCoeff (frameFirstMap r i) = 0) ∧
    (∀ v : Fin 5 → MvPolynomial (Fin 4) K, ∀ i : Fin 5,
      constantCoeff (frameMiddleMap v i) = 0) ∧
    (∀ v : Fin 5 → MvPolynomial (Fin 4) K,
      constantCoeff (frameLastMap v) = 0) := by
  obtain ⟨hq, ht⟩ := frame_resolution_entries_minimal (K := K)
  change (∀ i, constantCoeff (frameRelations i) = 0) at hq
  change (∀ i j, constantCoeff (frameMatrix X i j) = 0) at ht
  refine ⟨?_, ?_, ?_⟩
  · intro r i
    change constantCoeff (r * frameRelations i) = 0
    rw [map_mul, hq, mul_zero]
  · intro v i
    change constantCoeff (∑ j, frameMatrix X i j * v j) = 0
    simp only [map_sum, map_mul, ht, zero_mul, Finset.sum_const_zero]
  · intro v
    change constantCoeff (∑ i, v i * frameRelations i) = 0
    simp only [map_sum, map_mul, hq, mul_zero, Finset.sum_const_zero]

/-- The graded shifts of the exact resolution are `5,3,2,0`. -/
theorem frame_resolution_degrees :
    (∀ i : Fin 5, (frameRelations (K := K) i).IsHomogeneous (5-3)) ∧
    (∀ i j : Fin 5, (frameMatrix (X : Fin 4 → MvPolynomial (Fin 4) K) i j).IsHomogeneous (3-2)) ∧
    (∀ i : Fin 5, (frameRelations (K := K) i).IsHomogeneous (2-0)) :=
  ⟨frameRelations_homogeneous, frameMatrix_homogeneous, frameRelations_homogeneous⟩

end
end PfaffianDescent

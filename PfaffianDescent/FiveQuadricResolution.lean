import PfaffianDescent.FrameMinimality
import PfaffianDescent.PolynomialComplexEquiv

namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators

/-- An alternating quadratic presentation with all exactness statements for
`0 → R(-5) → R(-3)^5 → R(-2)^5 → R → R/I → 0`. -/
structure FiveQuadricResolution (K : Type*) [Field K]
    (I : Ideal (MvPolynomial (Fin 4) K)) where
  quadrics : Fin 5 → MvPolynomial (Fin 4) K
  matrix : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 4) K)
  quadrics_independent : LinearIndependent K quadrics
  quadrics_homogeneous : ∀ i, (quadrics i).IsHomogeneous 2
  matrix_homogeneous : ∀ i j, (matrix i j).IsHomogeneous 1
  matrix_alternating : IsAlternating matrix
  first_exact : LinearMap.range (LinearMap.toSpanSingleton _ _ quadrics) =
    LinearMap.ker matrix.mulVecLin
  last_exact : LinearMap.range matrix.mulVecLin =
    LinearMap.ker (Fintype.linearCombination (MvPolynomial (Fin 4) K) quadrics)
  image_eq : LinearMap.range (Fintype.linearCombination (MvPolynomial (Fin 4) K) quadrics) = I

namespace FiveQuadricResolution
section
variable {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 4) K)}
    (S : FiveQuadricResolution K I)

noncomputable def firstMap : MvPolynomial (Fin 4) K →ₗ[MvPolynomial (Fin 4) K]
    (Fin 5 → MvPolynomial (Fin 4) K) := LinearMap.toSpanSingleton _ _ S.quadrics

noncomputable def middleMap : (Fin 5 → MvPolynomial (Fin 4) K) →ₗ[MvPolynomial (Fin 4) K]
    (Fin 5 → MvPolynomial (Fin 4) K) := S.matrix.mulVecLin

noncomputable def lastMap : (Fin 5 → MvPolynomial (Fin 4) K) →ₗ[MvPolynomial (Fin 4) K]
    MvPolynomial (Fin 4) K := Fintype.linearCombination _ S.quadrics

lemma firstMap_injective : Function.Injective S.firstMap := by
  apply (injective_iff_map_eq_zero S.firstMap).mpr
  intro r hr
  have h := congrFun hr 0
  change r * S.quadrics 0 = 0 at h
  exact (mul_eq_zero.mp h).resolve_right (S.quadrics_independent.ne_zero 0)

theorem augmentation_exact : Function.Surjective (Ideal.Quotient.mkₐ K I) ∧
    ∀ f : MvPolynomial (Fin 4) K,
      Ideal.Quotient.mkₐ K I f = 0 ↔ f ∈ LinearMap.range S.lastMap := by
  refine ⟨Ideal.Quotient.mkₐ_surjective K I, ?_⟩
  intro f
  change _ ↔ f ∈ LinearMap.range (Fintype.linearCombination _ S.quadrics)
  rw [S.image_eq]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Every differential has entries in the homogeneous maximal ideal. -/
theorem entries_minimal :
    (∀ i, S.quadrics i ∈ RingHom.ker constantCoeff) ∧
    (∀ i j, S.matrix i j ∈ RingHom.ker constantCoeff) := by
  exact ⟨fun i => homogeneous_constantCoeff_zero (S.quadrics_homogeneous i) (by decide),
    fun i j => homogeneous_constantCoeff_zero (S.matrix_homogeneous i j) (by decide)⟩

theorem reduces_to_zero :
    (∀ r : MvPolynomial (Fin 4) K, ∀ i, constantCoeff (S.firstMap r i) = 0) ∧
    (∀ v : Fin 5 → MvPolynomial (Fin 4) K, ∀ i, constantCoeff (S.middleMap v i) = 0) ∧
    (∀ v : Fin 5 → MvPolynomial (Fin 4) K, constantCoeff (S.lastMap v) = 0) := by
  obtain ⟨hq, hT⟩ := S.entries_minimal
  change (∀ i, constantCoeff (S.quadrics i) = 0) at hq
  change (∀ i j, constantCoeff (S.matrix i j) = 0) at hT
  refine ⟨?_, ?_, ?_⟩
  · intro r i
    change constantCoeff (r * S.quadrics i) = 0
    rw [map_mul, hq, mul_zero]
  · intro v i
    change constantCoeff (∑ j, S.matrix i j * v j) = 0
    simp only [map_sum, map_mul, hT, zero_mul, Finset.sum_const_zero]
  · intro v
    change constantCoeff (∑ i, v i * S.quadrics i) = 0
    simp only [map_sum, map_mul, hq, mul_zero, Finset.sum_const_zero]

theorem degrees :
    (∀ i, (S.quadrics i).IsHomogeneous (5-3)) ∧
    (∀ i j, (S.matrix i j).IsHomogeneous (3-2)) ∧
    (∀ i, (S.quadrics i).IsHomogeneous (2-0)) :=
  ⟨S.quadrics_homogeneous, S.matrix_homogeneous, S.quadrics_homogeneous⟩

lemma matrix_transpose : S.matrix.transpose = -S.matrix := by
  funext i j
  exact S.matrix_alternating.2 i j

/-- The first and last differentials are dual under the standard free-module pairing. -/
theorem firstMap_dual :
    (Dual.transpose S.firstMap).comp frameVectorDuality.toLinearMap =
      frameScalarDuality.toLinearMap.comp S.lastMap := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro r
  change (∑ i, v i * (r * S.quadrics i)) = r * ∑ i, v i * S.quadrics i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The middle differential is its negative dual. -/
theorem middleMap_dual :
    (Dual.transpose S.middleMap).comp frameVectorDuality.toLinearMap =
      -(frameVectorDuality.toLinearMap.comp S.middleMap) := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change dotProduct v (S.matrix.mulVec w) = -dotProduct (S.matrix.mulVec v) w
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, S.matrix_transpose,
    Matrix.neg_mulVec, neg_dotProduct]

theorem lastMap_dual :
    (Dual.transpose S.lastMap).comp frameScalarDuality.toLinearMap =
      frameVectorDuality.toLinearMap.comp S.firstMap := by
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro v
  change (∑ i, v i * S.quadrics i) * r = ∑ i, (r * S.quadrics i) * v i
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end FiveQuadricResolution
end PfaffianDescent

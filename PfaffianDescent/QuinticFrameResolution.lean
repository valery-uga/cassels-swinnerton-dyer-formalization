import PfaffianDescent.QuinticComplex
import PfaffianDescent.RecombinedFrameSyzygies
import PfaffianDescent.LinearMatrixReplacement

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]

lemma quinticPolynomialMatrix_columns_independent (a : Vec K 5) :
    LinearIndependent K (quinticPolynomialMatrix a).col :=
  matrix_columns_independent_of_positive_kernel _ (quinticRelations a) 0 2 (by decide)
    (quinticRelations_homogeneous a 0) ((quinticRelations_independent a).ne_zero 0)
    (quinticPolynomialMatrix_kernel a)

lemma quinticPolynomialMatrix_columns_syzygies (a : Vec K 5) (j : Fin 5) :
    quinticLastMap a ((quinticPolynomialMatrix a).col j) = 0 := by
  apply LinearMap.range_le_ker_iff.mpr (quinticLastMap_comp_middle a)
  change (quinticPolynomialMatrix a).col j ∈ LinearMap.range (quinticPolynomialMatrix a).mulVecLin
  rw [Matrix.range_mulVecLin]
  exact Submodule.subset_span (Set.mem_range_self j)

/-- The remaining exactness assertion for the explicit quintic matrix, whenever
its five quadrics vanish on a projective frame. -/
theorem quinticMiddleMap_exact_of_frame
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hE : ∀ d (p : MvPolynomial (Fin 4) K), p.IsHomogeneous d → (E p).IsHomogeneous d)
    (a : Vec K 5) (hI : ∀ i, quinticRelations a i ∈ (frameIdeal (K := K)).map E.toRingHom) :
    LinearMap.range (quinticMiddleMap a) = LinearMap.ker (quinticLastMap a) := by
  obtain ⟨D, hD, hq⟩ := frame_quadratic_generators_matrix E hE (quinticRelations a)
    (quinticRelations_independent a) (quinticRelations_homogeneous a) hI
  exact linear_syzygy_matrix_replacement (quinticLastMap a) (recombinedFrameMatrix E D)
    (quinticPolynomialMatrix a) (recombinedFrameMatrix_homogeneous E hE D)
    (quinticPolynomialMatrix_homogeneous a) (recombinedFrameMatrix_columns_independent E hE D hD)
    (quinticPolynomialMatrix_columns_independent a) (recombinedFrameMatrix_exact E D hD _ hq)
    (quinticPolynomialMatrix_columns_syzygies a)

/-- The canonical quintic ideal is the entire ideal of any projective frame
on which its five quadratic equations vanish. -/
theorem quinticIdeal_eq_frame_ideal
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hE : ∀ d (p : MvPolynomial (Fin 4) K), p.IsHomogeneous d → (E p).IsHomogeneous d)
    (a : Vec K 5) (hI : ∀ i, quinticRelations a i ∈ (frameIdeal (K := K)).map E.toRingHom) :
    quinticIdeal a = (frameIdeal (K := K)).map E.toRingHom := by
  have hs := frame_quadratic_generators_span E hE (quinticRelations a)
    (quinticRelations_independent a) (quinticRelations_homogeneous a) hI
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact hI i
  · rw [frameIdeal, Ideal.map_span, ← Set.range_comp]
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    have hm : E (frameRelations i) ∈ Submodule.span K (Set.range (quinticRelations a)) := by
      rw [hs]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact Submodule.span_le_restrictScalars K (MvPolynomial (Fin 4) K) _ hm

/-- The full free resolution given by the explicit quintic quadrics and
alternating matrix, with the projective-frame hypothesis expressed as actual
homogeneous point ideals. -/
theorem quintic_frame_free_resolution (a : Vec K 5) (p : Fin 5 → (Fin 4 → K))
    (hp : FivePointGeneralPosition p) (hq : ∀ i, quinticRelations a i ∈ fiveVectorIdeal p) :
    Function.Injective (quinticFirstMap a) ∧
    LinearMap.range (quinticFirstMap a) = LinearMap.ker (quinticMiddleMap a) ∧
    LinearMap.range (quinticMiddleMap a) = LinearMap.ker (quinticLastMap a) ∧
    LinearMap.range (quinticLastMap a) = fiveVectorIdeal p := by
  obtain ⟨E, hE, hI⟩ := fiveVectorIdeal_normalization p hp
  have hqI (i : Fin 5) : quinticRelations a i ∈ (frameIdeal (K := K)).map E.toRingHom := hI ▸ hq i
  exact ⟨quinticFirstMap_injective a, quinticFirstMap_range_eq_middle_ker a,
    quinticMiddleMap_exact_of_frame E hE a hqI,
    (quinticLastMap_range a).trans ((quinticIdeal_eq_frame_ideal E hE a hqI).trans hI)⟩

end
end PfaffianDescent

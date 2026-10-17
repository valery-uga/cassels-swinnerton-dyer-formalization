import PfaffianDescent.FiveQuadricResolution

namespace PfaffianDescent
open MvPolynomial
namespace FiveQuadricResolution
section
variable {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 4) K)}

/-- A homogeneous polynomial coordinate automorphism transports the whole
alternating resolution, including its actual ideal. -/
noncomputable def map (S : FiveQuadricResolution K I)
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hE : ∀ d (f : MvPolynomial (Fin 4) K), f.IsHomogeneous d → (E f).IsHomogeneous d) :
    FiveQuadricResolution K (I.map E.toRingHom) where
  quadrics := fun i => E (S.quadrics i)
  matrix := S.matrix.map E
  quadrics_independent := S.quadrics_independent.map' E.toLinearMap
    (LinearMap.ker_eq_bot.mpr E.injective)
  quadrics_homogeneous := fun i => hE 2 _ (S.quadrics_homogeneous i)
  matrix_homogeneous := fun i j => hE 1 _ (S.matrix_homogeneous i j)
  matrix_alternating := by
    constructor
    · intro i
      change E (S.matrix i i) = 0
      rw [S.matrix_alternating.1 i, map_zero]
    · intro i j
      change E (S.matrix j i) = -E (S.matrix i j)
      rw [S.matrix_alternating.2 i j, map_neg]
  first_exact := polynomial_complex_first_exact_equiv E S.quadrics S.matrix S.first_exact
  last_exact := polynomial_complex_last_exact_equiv E S.quadrics S.matrix S.last_exact
  image_eq := by
    have hspan : Ideal.span (Set.range S.quadrics) = I := by
      simpa only [Fintype.range_linearCombination] using S.image_eq
    calc
      _ = (Ideal.span (Set.range S.quadrics)).map E.toRingHom := by
        rw [Fintype.range_linearCombination]
        change Ideal.span _ = (Ideal.span _).map _
        rw [Ideal.map_span, ← Set.range_comp]
        rfl
      _ = I.map E.toRingHom := congrArg (Ideal.map E.toRingHom) hspan

end
end FiveQuadricResolution
end PfaffianDescent

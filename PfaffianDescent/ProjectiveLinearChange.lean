import PfaffianDescent.ProjectiveVectorIdeal
import PfaffianDescent.PolynomialLinearChange

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma vectorLineHom_linearCoordinate (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (i : Fin n) :
    vectorLineHom v (linearCoordinate M i) = C (M.mulVec v i) * X () := by
  change MvPolynomial.aeval (vectorLineVariable v) (∑ j, C (M i j) * X j) =
    C (∑ j, M i j * v j) * X ()
  simp only [map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq,
    vectorLineVariable]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma vectorLineHom_linearSubstitution (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (vectorLineHom v).comp (linearSubstitution M) = vectorLineHom (M.mulVec v) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, linearSubstitution_X, vectorLineHom_linearCoordinate, vectorLineHom_X]

/-- The ideal of the line through a transformed vector is the pullback along polynomial substitution. -/
lemma vectorLineIdeal_linearSubstitution (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (vectorLineIdeal (M.mulVec v)).toIdeal =
      (vectorLineIdeal v).toIdeal.comap (linearSubstitution M).toRingHom := by
  ext f
  change vectorLineHom (M.mulVec v) f = 0 ↔ vectorLineHom v (linearSubstitution M f) = 0
  rw [← AlgHom.congr_fun (vectorLineHom_linearSubstitution M v) f]
  rfl

/-- The image of a projective point's ideal under an invertible substitution is
the ideal of its inverse-transformed coordinates. -/
theorem vectorLineIdeal_linearSubstitutionEquiv (M : Matrix (Fin n) (Fin n) K)
    (hM : IsUnit M.det) (v : Fin n → K) :
    (vectorLineIdeal v).toIdeal.map (linearSubstitutionEquiv M hM).toRingHom =
      (vectorLineIdeal (M⁻¹.mulVec v)).toIdeal := by
  calc
    _ = (vectorLineIdeal v).toIdeal.comap (linearSubstitution M⁻¹).toRingHom :=
      Ideal.map_comap_of_equiv (linearSubstitutionEquiv M hM).toRingEquiv
    _ = (vectorLineIdeal (M⁻¹.mulVec v)).toIdeal :=
      (vectorLineIdeal_linearSubstitution M⁻¹ v).symm

end
end PfaffianDescent

import PfaffianDescent.VoisinQuadraticEvaluationMatrix

/-!
# A unit quadratic minor separates the eight selected vectors

If two rows had the same coordinates, they would give equal rows of every
quadratic evaluation minor. Thus any unit eight-by-eight minor makes the
ordered coordinate vectors pairwise distinct over an arbitrary ring.
-/

namespace PfaffianDescent

open AllCharacteristics.UniversalHomogeneous

universe u

theorem eightPointQuadraticEvaluationMinor_unit_injective
    {R : Type u} [CommRing R] [Nontrivial R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m x).det) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  have hrow : (eightPointQuadraticEvaluationMinor m x) i =
      (eightPointQuadraticEvaluationMinor m x) j := by
    funext a
    simp only [eightPointQuadraticEvaluationMinor, Matrix.submatrix_apply,
      Function.id_def, eightPointQuadraticEvaluationMatrix]
    rw [hij]
  exact h.ne_zero (Matrix.det_zero_of_row_eq hne hrow)

end PfaffianDescent

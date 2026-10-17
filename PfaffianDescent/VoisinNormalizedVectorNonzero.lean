import PfaffianDescent.LinearNormalizedProjectivePoint

/-! A linearly normalized homogeneous vector has a nonzero coordinate. -/

namespace PfaffianDescent

open MvPolynomial

universe u

/-- A degree-one form cannot take value one on the zero vector. -/
theorem exists_nonzero_coordinate_of_linear_normalization
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (x : Fin 4 → F)
    (hx : ell.eval₂ (algebraMap K F) x = 1) :
    ∃ j : Fin 4, x j ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hxzero : x = 0 := by
    funext j
    exact h j
  have hconst : constantCoeff ell = 0 := by
    exact hell.coeff_eq_zero (by decide)
  rw [hxzero, MvPolynomial.eval₂_zero_apply, hconst, map_zero] at hx
  exact zero_ne_one hx

end PfaffianDescent

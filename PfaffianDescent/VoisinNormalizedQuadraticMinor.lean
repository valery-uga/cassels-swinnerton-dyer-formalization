import PfaffianDescent.VoisinQuadraticEvaluationMatrix
import PfaffianDescent.VoisinProjectiveVectorSchemePoint

/-!
# The selected quadratic minor survives linear-chart normalization

Scaling each selected projective vector to make the common linear form
equal to one multiplies each row of the quadratic evaluation matrix by a
unit square. Hence the chosen invertible minor remains invertible.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.UniversalHomogeneous

universe u

theorem eightPointQuadraticEvaluationMinor_isUnit_det_normalized
    {L : Type u} [Field L]
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m y).det) :
    IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i => normalizedVectorInLinearChart c (y i))).det := by
  let a (i : Fin 8) : Lˣ :=
    Units.mk0 ((homogeneousLinearForm c).eval (y i))⁻¹ (inv_ne_zero (hc i))
  have hscale :=
    (eightPointQuadraticEvaluationMinor_isUnit_det_scale_iff m a y).mpr hm
  convert hscale using 1
  congr 2

end PfaffianDescent

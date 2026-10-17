import PfaffianDescent.CubicClosedPointSerreSurfaceJetsDirections

/-! Exact weighted native surface tangent direction with its original
projective anchor/pivot/free-coordinate indices. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
universe u
set_option autoImplicit false

/-- Multiplying by the internally selected nonzero gradient clears the
native pivot direction with its original coordinate indices. -/
theorem nativeSurfaceJetRow_weighted_sum001
    {F : Type u} [Field F] (j : Fin 4) (a : Fin 3 → F) (pivot : Fin 3)
    (D : Fin 4 → F) (r : Fin 2) :
    (∑ i, D i * PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j a pivot i r) =
      D (j.succAbove (pivot.succAbove r)) -
        (D (j.succAbove pivot) * a (pivot.succAbove r)) / a pivot := by
  classical
  rw [Fin.sum_univ_succAbove _ j]
  simp only [PfaffianDescent.cubicClosedPointSerreSurfaceJets_row_diag,
    Pi.zero_apply, mul_zero, zero_add]
  simp only [PfaffianDescent.cubicClosedPointSerreSurfaceJets_row,
    Fin.insertNth_apply_succAbove]
  rw [Fin.sum_univ_succAbove _ pivot]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp [Pi.single_apply, mul_div_assoc, sub_eq_add_neg, mul_neg, neg_div, add_comm]


end PfaffianDescent.Coray

import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section
namespace PfaffianDescent
open Module
universe u v
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {n : ℕ} (b : Basis (Fin n) R M) (v : Fin n → M)

/-- The proposed new vectors become an actual basis when their coordinate determinant is a unit. -/
def finiteBasisOfUnitCoordinateDet290 (h : IsUnit (b.toMatrix v).det) : Basis (Fin n) R M :=
  b.map (Matrix.toLinearEquiv b (b.toMatrix v) h)

lemma finiteBasisOfUnitCoordinateDet_apply290 (h : IsUnit (b.toMatrix v).det) (j : Fin n) :
    finiteBasisOfUnitCoordinateDet290 b v h j = v j := by
  rw [finiteBasisOfUnitCoordinateDet290, Basis.map_apply]
  change Matrix.toLin b b (b.toMatrix v) (b j) = v j
  rw [Matrix.toLin_self]
  exact b.sum_toMatrix_smul_self v j

/-- This criterion works over arbitrary commutative rings, including rings with nilpotents. -/
lemma isUnit_coordinateDet_iff_basis290 :
    IsUnit (b.toMatrix v).det ↔ ∃ c : Basis (Fin n) R M, ∀ j, c j = v j := by
  constructor
  · intro h
    exact ⟨finiteBasisOfUnitCoordinateDet290 b v h,
      finiteBasisOfUnitCoordinateDet_apply290 b v h⟩
  · rintro ⟨c, hc⟩
    have hv : v = c := (funext hc).symm
    rw [hv]
    exact Matrix.isUnit_det_of_left_inverse (Basis.toMatrix_mul_toMatrix_flip c b)

end PfaffianDescent

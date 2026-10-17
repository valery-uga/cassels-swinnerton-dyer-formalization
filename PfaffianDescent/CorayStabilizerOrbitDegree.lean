import PfaffianDescent.CorayStabilizerHomogeneousIdealDescent
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-! Actual fixed-field degree of the existing coefficient-ideal stabilizer.
No orbit cardinality or field-degree equality is an input. Source only. -/
noncomputable section
namespace PfaffianDescent.Coray
open scoped Pointwise
universe u
variable {K E : Type u} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] polynomialGaloisCoefficientAction

/-- The degree over the ORIGINAL K of the actual stabilizer fixed field is
exactly the cardinality of the actual whole-ideal coefficient orbit. -/
theorem homogeneousIdeal_stabilizerFixedField_finrank_eq_orbit_card
    [FiniteDimensional K E] [IsGalois K E]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) E)) :
    Module.finrank K (homogeneousIdealStabilizerFixedField (K := K) C) =
      Nat.card (MulAction.orbit (E ≃ₐ[K] E) C.toIdeal) := by
  change Module.finrank K
      (IntermediateField.fixedField (MulAction.stabilizer (E ≃ₐ[K] E) C.toIdeal)) = _
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    IntermediateField.fixingSubgroup_fixedField, Subgroup.index_eq_card]
  exact (Nat.card_congr
    (MulAction.orbitEquivQuotientStabilizer (E ≃ₐ[K] E) C.toIdeal)).symm

end PfaffianDescent.Coray

import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Basis.Defs

/-! # The relative kernel on an invertible six-column evaluation chart

These formulas work over the actual coordinate ring after localizing a
six-column minor.  They require the literal invertible pivot and the other
three columns, rather than a field-only dimension certificate.
-/
noncomputable section
namespace PfaffianDescent
universe u
variable {R : Type u} [CommRing R]

/-- Evaluation in pivot-plus-free coordinates. -/
def serreIncidenceBlockEvaluation
    (pivot : (Fin 6 → R) ≃ₗ[R] (Fin 6 → R))
    (free : (Fin 3 → R) →ₗ[R] (Fin 6 → R)) :
    ((Fin 6 → R) × (Fin 3 → R)) →ₗ[R] (Fin 6 → R) :=
  pivot.toLinearMap.comp (LinearMap.fst R (Fin 6 → R) (Fin 3 → R)) +
    free.comp (LinearMap.snd R (Fin 6 → R) (Fin 3 → R))

@[simp] theorem serreIncidenceBlockEvaluation_apply
    (pivot : (Fin 6 → R) ≃ₗ[R] (Fin 6 → R))
    (free : (Fin 3 → R) →ₗ[R] (Fin 6 → R))
    (v : (Fin 6 → R) × (Fin 3 → R)) :
    serreIncidenceBlockEvaluation pivot free v = pivot v.1 + free v.2 := rfl

/-- The actual relative evaluation kernel is free on the three nonpivot
coordinates, with pivot coordinates forced by the six vanishing equations. -/
def serreIncidenceBlockKernelEquiv
    (pivot : (Fin 6 → R) ≃ₗ[R] (Fin 6 → R))
    (free : (Fin 3 → R) →ₗ[R] (Fin 6 → R)) :
    LinearMap.ker (serreIncidenceBlockEvaluation pivot free) ≃ₗ[R] (Fin 3 → R) where
  toFun s := s.1.2
  invFun v := ⟨(-pivot.symm (free v), v), by
    simp [LinearMap.mem_ker]⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · have hs := LinearMap.mem_ker.mp s.2
      have h : pivot s.1.1 = -(free s.1.2) := eq_neg_of_add_eq_zero_left hs
      have h' := congrArg pivot.symm h
      simpa using h'.symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end PfaffianDescent

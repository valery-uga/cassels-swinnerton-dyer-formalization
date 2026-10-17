import PfaffianDescent.VoisinFiniteAlgebraQuadraticSplitKernel
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Independence of the unordered quadratic pencil after splitting

The two quadrics in the kernel over the unordered configuration field remain
independent when their coefficients are extended to an ordered splitting field.
-/

namespace PfaffianDescent

open MvPolynomial TensorProduct
open AllCharacteristics.UniversalHomogeneous

universe u

/-- A linearly independent family of polynomials remains independent after
extending coefficients to a field extension. -/
theorem quadraticPolynomial_linearIndependent_after_scalarExtension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type*} (v : ι → MvPolynomial (Fin 4) K)
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => (v i).map (algebraMap K L)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) K L
  have h := Module.Flat.linearIndependent_one_tmul (S := L) hv
  have h' := h.map' e.toLinearEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr e.injective)
  have heq : (e.toLinearEquiv.toLinearMap ∘ fun i => (1 : L) ⊗ₜ[K] v i) =
      fun i => (v i).map (algebraMap K L) := by
    funext i
    simpa [e] using MvPolynomial.algebraTensorAlgEquiv_tmul K L 1 (v i)
  rw [heq] at h'
  exact h'

/-- The coefficient vectors of a quadratic pencil remain independent after
extending from the unordered field to its ordered splitting field. -/
theorem quadraticCoefficientPair_linearIndependent_after_scalarExtension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (v : Fin 2 → Monomials (Fin 4) 2 → K)
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i : Fin 2 =>
      fun m => algebraMap K L (v i m)) := by
  let e : (L ⊗[K] (Monomials (Fin 4) 2 → K)) ≃ₗ[L]
      (Monomials (Fin 4) 2 → L) :=
    (TensorProduct.piRight K L L
      (fun _ : Monomials (Fin 4) 2 => K)).trans
      (LinearEquiv.piCongrRight
        (fun _ => AlgebraTensorModule.rid K L L))
  have h := Module.Flat.linearIndependent_one_tmul (S := L) hv
  have h' := h.map' e.toLinearMap
    (LinearMap.ker_eq_bot.mpr e.injective)
  have heq : (e.toLinearMap ∘ fun i => (1 : L) ⊗ₜ[K] v i) =
      fun i : Fin 2 => fun m => algebraMap K L (v i m) := by
    funext i m
    simpa [e, Algebra.smul_def]
  rw [heq] at h'
  exact h'

/-- At an ordered eight-point configuration on a selected minor chart, any
ground-field basis of the quadratic vanishing pencil spans the entire
ordered-field evaluation kernel, once its two members vanish at the points.
The extension cannot acquire an extra quadratic equation. -/
theorem quadraticCoefficientPair_span_orderedKernel
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (v : Fin 2 → Monomials (Fin 4) 2 → K)
    (hv : LinearIndependent K v)
    (y : Fin 8 → Fin 4 → L)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m y).det)
    (hmem : ∀ i : Fin 2,
      (fun a => algebraMap K L (v i a)) ∈
        LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y))) :
    Submodule.span L (Set.range (fun i : Fin 2 =>
      fun a => algebraMap K L (v i a))) =
      LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y)) := by
  apply span_eq_kernel_of_two_independent_members _ _ hmem
    (quadraticCoefficientPair_linearIndependent_after_scalarExtension v hv)
  exact eightPointQuadraticEvaluationMatrix_kernel_finrank_two y m hminor

end PfaffianDescent

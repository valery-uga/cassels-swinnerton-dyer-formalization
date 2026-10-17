import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Lean.Elab.Tactic.Omega

/-!
# A finite embedded constant field has degree one when its generic tensor is a field

SOURCE ONLY, UNVERIFIED. This is the small algebra step useful after the
existing geometrically-integral generic tensor API. The tensor-field hypothesis
must be produced from actual geometric integrality; it is not silently supplied
for an arbitrary K-integral curve. The original K embedding is explicit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open scoped TensorProduct

/-- If a finite extension L/K embeds into F/K and F tensor L is a field,
its multiplication map injects that tensor into the one-dimensional F-space F.
Thus the original K degree of L is one. -/
theorem finite_subfield_finrank_eq_one_of_tensor_isField
    (K L F : Type*) [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F] [Module.Finite K L]
    (i : L →ₐ[K] F) (htensor : IsField (F ⊗[K] L)) :
    Module.finrank K L = 1 := by
  letI : Field (F ⊗[K] L) := htensor.toField
  let mu : (F ⊗[K] L) →ₐ[F] F :=
    Algebra.TensorProduct.lift (AlgHom.id F F) i (fun _ _ => Commute.all _ _)
  have hsmall : Module.finrank F (F ⊗[K] L) ≤ Module.finrank F F :=
    mu.toLinearMap.finrank_le_finrank_of_injective mu.injective
  rw [Module.finrank_baseChange, CommSemiring.finrank_self] at hsmall
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  omega

end PfaffianDescent.Coray

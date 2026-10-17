import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Surjective actual tensor evaluation gives the literal basis-coordinate matrix rank -/
noncomputable section
open Module
open scoped TensorProduct
namespace PfaffianDescent
universe u

theorem serreIncidenceMatrix_surjective_of_actual_tensor_columns
    {K E V W : Type u} [Field K] [Field E] [Algebra K E]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module E W]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (B : Basis (Fin 9) K V)
    (eval : E ⊗[K] V →ₗ[E] W) (heval : Function.Surjective eval)
    (coord : W ≃ₗ[E] (ι → E)) (A : Matrix ι (Fin 9) E)
    (hcol : ∀ k, coord (eval (1 ⊗ₜ[K] B k)) = A.col k) :
    Function.Surjective (Matrix.toLin' A) := by
  let e := coord.toLinearMap.comp eval
  have he : Function.Surjective e := coord.surjective.comp heval
  have hr : e.range = ⊤ := LinearMap.range_eq_top.mpr he
  have hb := congrArg (fun P : Submodule E (E ⊗[K] V) => P.map e)
    (B.baseChange E).span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top] at hb
  have hc : (e : (E ⊗[K] V) → (ι → E)) ∘ (B.baseChange E) = A.col := by
    funext k
    simp only [Function.comp_apply, Basis.baseChange_apply]
    exact hcol k
  rw [hc, hr] at hb
  apply LinearMap.range_eq_top.mp
  rw [Matrix.range_toLin']
  exact hb

end PfaffianDescent

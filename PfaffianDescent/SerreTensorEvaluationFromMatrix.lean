import PfaffianDescent.VoisinDegreeElevenSerreIncidenceTensorMatrixSurjective
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The native matrix rank also implies surjectivity of the literal
tensor evaluator. A unit column minor remains a rank witness in every field. -/
noncomputable section
open Module
open scoped TensorProduct
namespace PfaffianDescent
universe u v w

theorem serreIncidence_actual_tensor_surjective_of_matrix_columns
    {K E V W : Type u} [Field K] [Field E] [Algebra K E]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module E W]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (B : Basis (Fin 9) K V) (eval : E ⊗[K] V →ₗ[E] W)
    (coord : W ≃ₗ[E] (ι → E)) (A : Matrix ι (Fin 9) E)
    (hcol : ∀ k, coord (eval (1 ⊗ₜ[K] B k)) = A.col k)
    (hA : Function.Surjective (Matrix.toLin' A)) : Function.Surjective eval := by
  let e := coord.toLinearMap.comp eval
  have hb := congrArg (fun P : Submodule E (E ⊗[K] V) => P.map e)
    (B.baseChange E).span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top] at hb
  have hc : (e : (E ⊗[K] V) → (ι → E)) ∘ (B.baseChange E) = A.col := by
    funext k
    simp only [Function.comp_apply, Basis.baseChange_apply]
    exact hcol k
  have hspan : Submodule.span E (Set.range A.col) = ⊤ := by
    rw [← Matrix.range_toLin']
    exact LinearMap.range_eq_top.mpr hA
  rw [hc, hspan] at hb
  have he : Function.Surjective e := LinearMap.range_eq_top.mp hb.symm
  intro w
  obtain ⟨x, hx⟩ := he (coord w)
  exact ⟨x, coord.injective hx⟩

theorem serreIncidenceMatrix_surjective_of_unit_minor
    {E : Type u} [Field E] {ι : Type v} {κ : Type w}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ E) (m : ι ↪ κ)
    (hm : IsUnit (A.submatrix id m).det) : Function.Surjective (Matrix.toLin' A) := by
  have hminor : Function.Surjective (Matrix.toLin' (A.submatrix id m)) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hm)
  have hspan : Submodule.span E (Set.range (A.submatrix id m).col) = ⊤ := by
    rw [← Matrix.range_toLin']
    exact LinearMap.range_eq_top.mpr hminor
  apply LinearMap.range_eq_top.mp
  rw [Matrix.range_toLin']
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨m i, rfl⟩

end PfaffianDescent

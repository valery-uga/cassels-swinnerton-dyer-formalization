import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Tensor matrix identities with a row-index universe independent of the
field and section universes. This includes the literal finite native rows. -/
noncomputable section
open Module
open scoped TensorProduct
namespace PfaffianDescent
universe u v w
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceMatrix_reindexed_column
    {E : Type u} [Field E] {ι : Type v} {κ : Type w}
    (ρ : κ ≃ ι) (A : Matrix ι (Fin 9) E) (k : Fin 9) :
    (LinearEquiv.piCongrLeft E (fun _ : κ => E) ρ.symm) (A.col k) =
      (A.submatrix ρ id).col k := by
  ext r
  simp only [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft'_symm_apply,
    Equiv.piCongrLeft'_symm, Equiv.piCongrLeft'_apply, Equiv.symm_symm,
    Matrix.col, Matrix.submatrix_apply, Matrix.transpose_apply, id_eq]

theorem serreIncidenceTensorMatrix_operator_anyIndex
    {K E V W : Type u} [Field K] [Field E] [Algebra K E]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module E W]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (B : Basis (Fin 9) K V) (eval : E ⊗[K] V →ₗ[E] W)
    (coord : W ≃ₗ[E] (ι → E)) (A : Matrix ι (Fin 9) E)
    (hcol : ∀ k, coord (eval (1 ⊗ₜ[K] B k)) = A.col k)
    (t : E ⊗[K] V) :
    Matrix.toLin' A ((B.baseChange E).equivFun t) = coord (eval t) := by
  have h : (Matrix.toLin' A).comp (B.baseChange E).equivFun.toLinearMap =
      coord.toLinearMap.comp eval := by
    apply (B.baseChange E).ext
    intro k
    have hk : (B.baseChange E).equivFun ((B.baseChange E) k) = Pi.single k 1 := by
      ext i
      simp only [Basis.equivFun_apply, Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hk, Matrix.toLin'_apply]
    simp only [Matrix.mulVec_single, Basis.baseChange_apply]
    change (1 : Eᵐᵒᵖ) • A.col k = coord (eval (1 ⊗ₜ[K] B k))
    simpa only [one_smul] using (hcol k).symm
  exact LinearMap.congr_fun h t


theorem serreIncidenceMatrix_surjective_of_actual_tensor_columns_anyIndex
    {K E V W : Type u} [Field K] [Field E] [Algebra K E]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module E W]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
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

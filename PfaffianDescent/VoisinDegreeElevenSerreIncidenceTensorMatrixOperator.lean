import PfaffianDescent.VoisinDegreeElevenSerreIncidenceTensorMatrixSurjective

/-! # The actual tensor evaluator equals its native matrix on all sections -/
noncomputable section
open Module
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceTensorMatrix_operator
    {K E V W : Type u} [Field K] [Field E] [Algebra K E]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module E W]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
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

end PfaffianDescent

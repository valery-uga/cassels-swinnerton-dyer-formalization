import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Coordinates in a transported ground frame agree with the original tensor frame -/
noncomputable section
open scoped TensorProduct
namespace PfaffianDescent
open Module
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {K F E : Type u} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module F W]

def serreIncidenceGroundTensorFrame (z : F ⊗[K] V ≃ₗ[F] W) :
    E ⊗[F] W ≃ₗ[E] E ⊗[K] V :=
  (z.symm.baseChange F E).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K F E E V)

theorem serreIncidenceGroundTensorFrame_basis
    (z : F ⊗[K] V ≃ₗ[F] W) (b : Basis (Fin 9) K V) (k : Fin 9) :
    serreIncidenceGroundTensorFrame (E := E) z
      ((((b.baseChange F).map z).baseChange E) k) = (b.baseChange E) k := by
  simp only [serreIncidenceGroundTensorFrame, LinearEquiv.trans_apply,
    Basis.baseChange_apply, Basis.map_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.symm_apply_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  simp

theorem serreIncidenceGroundTensorFrame_coordinates
    (z : F ⊗[K] V ≃ₗ[F] W) (b : Basis (Fin 9) K V) (t : E ⊗[F] W) :
    (b.baseChange E).equivFun (serreIncidenceGroundTensorFrame (E := E) z t) =
      (((b.baseChange F).map z).baseChange E).equivFun t := by
  have h : (b.baseChange E).equivFun.toLinearMap.comp
      (serreIncidenceGroundTensorFrame (E := E) z).toLinearMap =
      (((b.baseChange F).map z).baseChange E).equivFun.toLinearMap := by
    apply (((b.baseChange F).map z).baseChange E).ext
    intro k
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      serreIncidenceGroundTensorFrame_basis]
    ext i
    rw [Basis.equivFun_self, Basis.equivFun_self]
  exact LinearMap.congr_fun h t

end PfaffianDescent

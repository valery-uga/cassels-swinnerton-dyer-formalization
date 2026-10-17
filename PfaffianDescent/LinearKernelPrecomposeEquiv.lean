import Mathlib.LinearAlgebra.Basis.Basic

/-! SOURCE ONLY / UNVERIFIED. Exact kernel transport along a linear equivalence. -/
noncomputable section
namespace PfaffianDescent
universe u

def linearKernelPrecomposeEquiv
    {K V W A : Type u} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup A] [Module K A]
    (e : V ≃ₗ[K] W) (r : W →ₗ[K] A) :
    r.ker ≃ₗ[K] (r.comp e.toLinearMap).ker where
  toFun s := ⟨e.symm s.1, by
    change r (e (e.symm s.1)) = 0
    rw [e.apply_symm_apply]
    exact s.2⟩
  invFun p := ⟨e p.1, p.2⟩
  left_inv s := Subtype.ext (e.apply_symm_apply s.1)
  right_inv p := Subtype.ext (e.symm_apply_apply p.1)
  map_add' s t := Subtype.ext (map_add e.symm s.1 t.1)
  map_smul' c s := Subtype.ext (map_smul e.symm c s.1)

end PfaffianDescent

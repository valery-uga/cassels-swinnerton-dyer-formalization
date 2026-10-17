import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace PfaffianDescent
open Module
open scoped BigOperators
section
variable {K M n : Type*} [Field K] [AddCommGroup M] [Module K M] [Fintype n] [DecidableEq n]

/-- Two independent finite generating families of the same vector space are
related by an invertible matrix over their coefficient field. -/
theorem exists_generator_basis_change (u v : n → M)
    (hu : LinearIndependent K u) (hv : LinearIndependent K v)
    (hspan : Submodule.span K (Set.range u) = Submodule.span K (Set.range v)) :
    ∃ D : Matrix n n K, IsUnit D.det ∧ ∀ j, v j = ∑ i, D i j • u i := by
  classical
  let b := Basis.span hu
  let c := (Basis.span hv).map (LinearEquiv.ofEq _ _ hspan.symm)
  let D := b.toMatrix c
  haveI : Invertible D := Basis.invertibleToMatrix b c
  refine ⟨D, Matrix.isUnit_det_of_invertible D, ?_⟩
  intro j
  have h := congrArg Subtype.val (b.sum_toMatrix_smul_self c j)
  simpa only [b, c, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply,
    Submodule.coe_sum, Submodule.coe_smul_of_tower] using h.symm

end
end PfaffianDescent

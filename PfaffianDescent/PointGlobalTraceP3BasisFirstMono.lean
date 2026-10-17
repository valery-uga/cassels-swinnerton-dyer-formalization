import PfaffianDescent.PointGlobalTraceP3BasisKoszul

/-! # Monomorphy of the actual first degree-one Koszul differential -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- A nonzero first equation makes the actual leftmost Koszul sheaf map
monic, since its third component is the actual homogeneous multiplication. -/
theorem pointGlobalTraceP3Basis_first_mono
    (f : Fin 4 → homogeneousSubmodule (Fin 4) K 1) (hf₁ : (f 1).val ≠ 0) :
    Mono (pointGlobalTraceP3BasisKoszulFirst K f) := by
  haveI : Mono (pointGlobalTraceP3BasisMul K f 1 2) :=
    mulHomogeneous_mono PS (f 1) hf₁ 2
  have h : pointGlobalTraceP3BasisKoszulFirst K f ≫
      biproduct.π (pointGlobalTraceP3CoordinateTriple K 2) (2 : Fin 3) =
        pointGlobalTraceP3BasisMul K f 1 2 := by
    simp [pointGlobalTraceP3BasisKoszulFirst]
  haveI : Mono (pointGlobalTraceP3BasisKoszulFirst K f ≫
      biproduct.π (pointGlobalTraceP3CoordinateTriple K 2) (2 : Fin 3)) := h ▸ inferInstance
  exact mono_of_mono (pointGlobalTraceP3BasisKoszulFirst K f)
    (biproduct.π (pointGlobalTraceP3CoordinateTriple K 2) (2 : Fin 3))

end PfaffianDescent.ProjectiveNegativeTwist

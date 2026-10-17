import PfaffianDescent.SchemeModuleFiniteClosedSupportNativeAcyclic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The genuine native restriction map bounds sections on any open by global
sections. Finite closed support and finite global sections remain explicit:
their geometric construction for the coefficient-model cokernel is separate. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
set_option autoImplicit false

/-- Finite closed support makes the original-K restriction surjective, hence
finite global dimension bounds the dimension on every actual open. -/
theorem schemeModuleFiniteClosedSupport_openSections_finite_finrank_le_top
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (C : Set X)
    (hC : C.Finite) (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X))
    (hsupport : schemeModuleStalkSupport M ⊆ C)
    [Module.Finite K (SchemeModuleOpenSectionsOver pi M ⊤)] (U : X.Opens) :
    Module.Finite K (SchemeModuleOpenSectionsOver pi M U) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi M U) ≤
        Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) := by
  let r := schemeModuleOpenSectionsRestrictionLinearMap pi M
    (show U ≤ ⊤ from le_top)
  have hr : Function.Surjective r :=
    schemeModuleFiniteClosedSupport_topRestriction_surjective pi M C hC hclosed hsupport U
  exact ⟨Module.Finite.of_surjective r hr,
    LinearMap.finrank_le_finrank_of_surjective hr⟩

end PfaffianDescent.Coray

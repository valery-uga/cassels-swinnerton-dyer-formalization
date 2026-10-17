import PfaffianDescent.SchemeModuleGlobalSections

/-! # Exact structural morphism equality transports native section scalars -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

def serreIncidenceGlobalSectionsBaseCongr
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base base' : X ⟶ Spec (.of K)) (h : base = base') (M : X.Modules) :
    SchemeModuleGlobalSectionsOver base M ≃ₗ[K] SchemeModuleGlobalSectionsOver base' M := by
  subst base'
  exact LinearEquiv.refl K _

end PfaffianDescent

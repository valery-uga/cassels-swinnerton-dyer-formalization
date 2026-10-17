import PfaffianDescent.CubicFieldPointChartSerreSections

/-! Transport actual global-section dimensions along actual Serre sequence
equality, without unfolding the local-free construction. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreSection_finrank_of_sequence_eq
    {F : Type u} [Field F] {X : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X M)
    (e₀ : SerreExtensionSequenceData X M) (heq : e.toSequenceData = e₀)
    {n : ℕ} (hn : Module.finrank F (SchemeModuleGlobalSectionsOver base
      (show X.Modules from e₀.E)) = n) :
    Module.finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = n := by
  have hE : (show X.Modules from e.E) = (show X.Modules from e₀.E) :=
    congrArg SerreExtensionSequenceData.E heq
  exact (congrArg (fun Q : X.Modules => Module.finrank F
    (SchemeModuleGlobalSectionsOver base Q)) hE).trans hn

end PfaffianDescent

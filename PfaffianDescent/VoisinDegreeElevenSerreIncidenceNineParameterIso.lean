import PfaffianDescent.VoisinFixedLinearSystemParameters

/-! # Actual rank-nine global sections have the literal nine-coordinate parameter scheme -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceNineParameterIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = 9) :
    schemeModuleGlobalSectionsProjectiveParameters base M ≅
      scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) :=
  eqToIso (congrArg (fun n : ℕ =>
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) h9)

end PfaffianDescent

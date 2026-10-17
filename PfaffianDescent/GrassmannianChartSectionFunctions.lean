import PfaffianDescent.GrassmannianChartFunctions
import PfaffianDescent.GrassmannianSubmoduleBaseChange
import PfaffianDescent.CoordinateModuleSheafMaps

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}} {m n : ℕ}

/-- Chart coordinates restricted to any open subset of a test scheme. -/
noncomputable def grassmannianChartSectionFunctions
    (f : X ⟶ grassmannianChartScheme K m n) (U : X.Opens) :
    Matrix (Fin n) (Fin m) Γ(X, U) :=
  (grassmannianChartFunctions K f).map (regularFunctionRestrict X U)

/-- Compatible Grassmannian chart maps give the same actual submodule on every open. -/
lemma grassmannianChartSectionFunctions_submodule_eq
    (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (f g : X ⟶ grassmannianChartScheme K m n)
    (h : f ≫ grassmannianChartι K σ = g ≫ grassmannianChartι K τ) (U : X.Opens) :
    grassmannianChartSubmodule Γ(X, U) σ (grassmannianChartSectionFunctions K f U) =
      grassmannianChartSubmodule Γ(X, U) τ (grassmannianChartSectionFunctions K g U) := by
  have he := congrArg (grassmannianSubmoduleBaseChange (regularFunctionRestrict X U))
    (grassmannianChartFunctions_submodule_eq K σ τ f g h)
  simpa only [grassmannianChartSubmodule_baseChange, grassmannianChartSectionFunctions] using he

/-- Pulling chart coordinates back is the ordinary pullback of global regular functions. -/
lemma grassmannianChartFunctions_comp {Y : Scheme.{u}} (f : Y ⟶ X)
    (g : X ⟶ grassmannianChartScheme K m n) :
    grassmannianChartFunctions K (f ≫ g) = (grassmannianChartFunctions K g).map f.appTop.hom := by
  funext i j
  exact RingHom.congr_fun (affineFunctionHom_comp f g) (MvPolynomial.X (i, j))

end
end PfaffianDescent

import PfaffianDescent.OpenAffineFunctions
import PfaffianDescent.GrassmannianChartSectionFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {X Y : Scheme.{u}} {m n : ℕ}

/-- Graph coordinates on an open subset, in the section ring of the original scheme. -/
noncomputable def grassmannianOpenChartFunctions (U : X.Opens)
    (f : U.toScheme ⟶ grassmannianChartScheme K m n) : Matrix (Fin n) (Fin m) Γ(X, U) :=
  fun i j => openAffineFunctionHom U f (MvPolynomial.X (i, j))

lemma grassmannianOpenChartFunctions_submodule_eq (U : X.Opens)
    (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (f g : U.toScheme ⟶ grassmannianChartScheme K m n)
    (h : f ≫ grassmannianChartι K σ = g ≫ grassmannianChartι K τ) :
    grassmannianChartSubmodule Γ(X, U) σ (grassmannianOpenChartFunctions K U f) =
      grassmannianChartSubmodule Γ(X, U) τ (grassmannianOpenChartFunctions K U g) := by
  have he := congrArg (grassmannianSubmoduleBaseChange U.topIso.hom.hom)
    (grassmannianChartFunctions_submodule_eq K σ τ f g h)
  rw [grassmannianChartSubmodule_baseChange, grassmannianChartSubmodule_baseChange] at he
  exact he

lemma grassmannianOpenChartFunctions_resLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (g : U.toScheme ⟶ grassmannianChartScheme K m n) :
    grassmannianOpenChartFunctions K V (f.resLE U V e ≫ g) =
      (grassmannianOpenChartFunctions K U g).map (f.appLE U V e).hom := by
  funext i j
  exact RingHom.congr_fun (openAffineFunctionHom_resLE f U V e g) (MvPolynomial.X (i, j))

lemma grassmannianOpenChartFunctions_restrict (U : X.Opens)
    (f : X ⟶ grassmannianChartScheme K m n) :
    grassmannianOpenChartFunctions K U (U.ι ≫ f) =
      grassmannianChartSectionFunctions K f U := by
  funext i j
  exact RingHom.congr_fun (openAffineFunctionHom_restrict U f) (MvPolynomial.X (i, j))

end
end PfaffianDescent

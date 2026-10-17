import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffineProductChart
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_affineProduct_sections_noetherian
    {X E S : Scheme.{u}} [IsAffine E] [IsAffine S] [IsNoetherianRing Γ(E, ⊤)]
    (f : X ⟶ S) [LocallyOfFiniteType f] (U : X.affineOpens) (k : E ⟶ S) :
    IsNoetherianRing Γ(pullback (U.1.ι ≫ f) k, ⊤) := by
  letI : IsAffine (U.1 : Scheme.{u}) := U.2
  letI : IsLocallyNoetherian E := isLocallyNoetherian_of_isOpenImmersion E.isoSpec.hom
  letI : IsLocallyNoetherian (pullback (U.1.ι ≫ f) k) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (U.1.ι ≫ f) k)
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

end PfaffianDescent

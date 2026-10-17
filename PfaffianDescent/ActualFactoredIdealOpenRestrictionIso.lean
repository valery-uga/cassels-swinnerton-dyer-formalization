import PfaffianDescent.ActualClosedIdealSourceRestrictionIso

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

def actualFactoredIdealOpenRestrictionIso
    {X U Z : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (j : Z ⟶ U)
    [IsClosedImmersion j] (q : Z ⟶ X) [IsClosedImmersion q]
    (hfac : j ≫ f = q) :
    (Scheme.Modules.restrictFunctor f).obj (closedImmersionModule q) ≅
      closedImmersionModule j := by
  subst q
  exact cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j

end PfaffianDescent
end

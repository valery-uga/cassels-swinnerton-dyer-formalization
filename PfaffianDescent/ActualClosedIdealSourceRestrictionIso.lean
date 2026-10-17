import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealOpenRestrictionInclusion

/- SOURCE ONLY / UNVERIFIED. Actual UNTWiSTED original ideal chart
refinement retains the SAME original closed morphism q and its true source
factorization. The inclusion law is derived, not supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
universe u

def actualClosedIdealSourceRestrictionIso
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (q : Z ⟶ X) [IsClosedImmersion q] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : j ≫ f = q) :
    (Scheme.Modules.restrictFunctor f).obj (closedImmersionModule q) ≅
      closedImmersionModule j := by
  letI : IsClosedImmersion (j ≫ f) := hfac.symm ▸ inferInstanceAs (IsClosedImmersion q)
  exact (Scheme.Modules.restrictFunctor f).mapIso
    (eqToIso (congrArg closedImmersionModule hfac.symm)) ≪≫
      cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualClosedIdealSourceRestrictionIso_toUnit
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (q : Z ⟶ X) [IsClosedImmersion q] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hfac : j ≫ f = q) :
    (actualClosedIdealSourceRestrictionIso f q j hfac).hom ≫
      closedImmersionModuleToUnit j =
    (Scheme.Modules.restrictFunctor f).map (closedImmersionModuleToUnit q) ≫
      (Scheme.Modules.restrictUnitIso f).hom := by
  subst q
  let R := Scheme.Modules.restrictFunctor f
  let M : X.Modules := closedImmersionModule (j ≫ f)
  let e := cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j
  have hi : R.map (𝟙 M) ≫ e.hom = e.hom :=
    (congrArg (fun m => m ≫ e.hom) (R.map_id M)).trans
      (Category.id_comp e.hom)
  have he := cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso_toUnit f j
  change (R.map (𝟙 M) ≫ e.hom) ≫ closedImmersionModuleToUnit j =
    R.map (closedImmersionModuleToUnit (j ≫ f)) ≫
      (Scheme.Modules.restrictUnitIso f).hom
  exact (congrArg (fun m => m ≫ closedImmersionModuleToUnit j) hi).trans he

end PfaffianDescent

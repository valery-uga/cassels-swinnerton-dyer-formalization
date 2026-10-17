import PfaffianDescent.ActualIdealTwistRestrictionInclusion
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartRefinement

/- SOURCE ONLY / UNVERIFIED. Source equality is transported in the actual
ideal-twist module before refining its SAME chart. The inclusion square is
proved, retaining the original ideal and native twist rather than renaming it. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualClosedIdealTwistEqIso_toInclusion
    {X Z : Scheme.{u}} (q q' : Z ⟶ X) [IsClosedImmersion q] [IsClosedImmersion q']
    (h : q = q') (T : X.Modules) :
    (eqToIso (congrArg (fun r => schemeModuleTensor (closedImmersionModule r) T) h)).hom ≫
      actualIdealTwistInclusion q' T = actualIdealTwistInclusion q T := by
  cases h
  simp

def actualOriginalIdealTwistSourceRefinementIso
    {X V Z : Scheme.{u}} (U : X.Opens) (f : V ⟶ (U : Scheme)) [IsIso f]
    (q : Z ⟶ X) [IsClosedImmersion q] (j : Z ⟶ V) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U.ι = q)
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (Scheme.Modules.restrictFunctor (f ≫ U.ι)).obj (closedImmersionIdealTwist q T) ≅
      closedImmersionModule j := by
  letI : IsClosedImmersion ((j ≫ f) ≫ U.ι) :=
    hfac.symm ▸ inferInstanceAs (IsClosedImmersion q)
  exact (Scheme.Modules.restrictFunctor (f ≫ U.ι)).mapIso
      (eqToIso (congrArg (fun r => schemeModuleTensor (closedImmersionModule r) T) hfac.symm)) ≪≫
    cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso U f T p j

lemma actualOriginalIdealTwistSourceRefinementIso_toInclusion
    {X V Z : Scheme.{u}} (U : X.Opens) (f : V ⟶ (U : Scheme)) [IsIso f]
    (q : Z ⟶ X) [IsClosedImmersion q] (j : Z ⟶ V) [IsClosedImmersion j]
    (hfac : (j ≫ f) ≫ U.ι = q)
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (actualOriginalIdealTwistSourceRefinementIso U f q j hfac T p).hom ≫
      closedImmersionModuleToUnit j =
    (Scheme.Modules.restrictFunctor (f ≫ U.ι)).map
      (actualIdealTwistInclusion q T) ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p).hom := by
  cases hfac
  let R := Scheme.Modules.restrictFunctor (f ≫ U.ι)
  let I : X.Modules := schemeModuleTensor (closedImmersionModule ((j ≫ f) ≫ U.ι)) T
  let e := cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso U f T p j
  let v := cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p
  have hi : R.map (𝟙 I) ≫ e.hom = e.hom :=
    (congrArg (fun m => m ≫ e.hom) (R.map_id I)).trans (Category.id_comp e.hom)
  have he : e.hom ≫ closedImmersionModuleToUnit j =
      R.map (actualIdealTwistInclusion ((j ≫ f) ≫ U.ι) T) ≫ v.hom :=
    cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso_toUnit U f T p j
  change (R.map (𝟙 I) ≫ e.hom) ≫ closedImmersionModuleToUnit j =
    R.map (actualIdealTwistInclusion ((j ≫ f) ≫ U.ι) T) ≫ v.hom
  exact (congrArg (fun m => m ≫ closedImmersionModuleToUnit j) hi).trans he

end PfaffianDescent

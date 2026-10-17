import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartRefinement

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open IdealSheafDataModule ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false

private theorem compareLift {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) {O W T : C} {P N : D}
    (u : F.obj O ≅ P) (e : F.obj W ≅ N) (p : F.obj T ≅ P)
    (a : W ⟶ T) (s : O ⟶ T) (v : O ⟶ W) (t : P ⟶ N) (m : N ⟶ P)
    [Mono m] (hc : e.hom ≫ m = F.map a ≫ p.hom)
    (hv : v ≫ a = s) (ht : t ≫ m = u.inv ≫ F.map s ≫ p.hom) :
    u.inv ≫ F.map v ≫ e.hom = t := by
  apply (cancel_mono m).mp
  have hmap : F.map v ≫ F.map a = F.map s :=
    (F.map_comp v a).symm.trans (F.congr_map hv)
  calc
    (u.inv ≫ F.map v ≫ e.hom) ≫ m =
        u.inv ≫ F.map v ≫ (F.map a ≫ p.hom) := by
      simpa only [Category.assoc] using congrArg (fun k => u.inv ≫ F.map v ≫ k) hc
    _ = u.inv ≫ F.map s ≫ p.hom := by
      simpa only [Category.assoc] using congrArg (fun k => u.inv ≫ k ≫ p.hom) hmap
    _ = t ≫ m := ht.symm

/-- Every actual global ideal lift has the SAME literal local ideal section
as its coefficient preimage. No independent section or fibre certificate is used. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChart_sectionComparison
    {X V : Scheme.{u}} (U : X.Opens) (f : V ⟶ (U : Scheme)) [IsOpenImmersion f]
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    {Z : Scheme.{u}} (j : Z ⟶ V) [IsClosedImmersion j]
    [IsClosedImmersion (j ≫ f)] [IsClosedImmersion ((j ≫ f) ≫ U.ι)]
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶
      closedImmersionIdealTwist ((j ≫ f) ≫ U.ι) T)
    (hv : v ≫ (closedImmersionIdealTwistSequence ((j ≫ f) ≫ U.ι) T).f ≫
      (schemeModuleTensorUnitLeftIso T).hom = s)
    (t : SheafOfModules.unit V.ringCatSheaf ⟶ closedImmersionModule j)
    (ht : t ≫ closedImmersionModuleToUnit j =
      (Scheme.Modules.restrictUnitIso (f ≫ U.ι)).inv ≫
      (Scheme.Modules.restrictFunctor (f ≫ U.ι)).map s ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p).hom) :
    (Scheme.Modules.restrictUnitIso (f ≫ U.ι)).inv ≫
      (Scheme.Modules.restrictFunctor (f ≫ U.ι)).map v ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso U f T p j).hom = t := by
  letI : Mono (closedImmersionModuleToUnit j) := by
    change Mono (idealModuleToUnit _)
    infer_instance
  exact compareLift (Scheme.Modules.restrictFunctor (f ≫ U.ι))
    (Scheme.Modules.restrictUnitIso (f ≫ U.ι))
    (cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso U f T p j)
    (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p)
    ((closedImmersionIdealTwistSequence ((j ≫ f) ≫ U.ι) T).f ≫
      (schemeModuleTensorUnitLeftIso T).hom) s v t (closedImmersionModuleToUnit j)
    (cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso_toUnit U f T p j) hv ht

end PfaffianDescent

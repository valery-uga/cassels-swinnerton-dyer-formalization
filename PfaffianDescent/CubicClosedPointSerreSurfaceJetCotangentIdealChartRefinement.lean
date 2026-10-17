import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealChartAbstract

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open IdealSheafDataModule ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false

private theorem refinedSquare {C : Type u} [Category C]
    {W M N P T Q S : C} (b : W ⟶ M) (e : M ⟶ N) (n : N ⟶ P)
    (a : M ⟶ T) (p : T ⟶ P) (c : W ⟶ Q) (d : Q ⟶ T)
    (v : P ⟶ S) (h : e ≫ n = a ≫ p) (hn : c ≫ d = b ≫ a) :
    (b ≫ e) ≫ n ≫ v = c ≫ d ≫ p ≫ v := by
  calc
    (b ≫ e) ≫ n ≫ v = (b ≫ (e ≫ n)) ≫ v := by simp only [Category.assoc]
    _ = (b ≫ (a ≫ p)) ≫ v := congrArg (fun k => (b ≫ k) ≫ v) h
    _ = (b ≫ a) ≫ p ≫ v := by simp only [Category.assoc]
    _ = c ≫ d ≫ p ≫ v := by
      exact (congrArg (fun k => k ≫ p ≫ v) hn.symm).trans
        (by simp only [Category.assoc])

def cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso
    {X V : Scheme.{u}} (U : X.Opens) (f : V ⟶ (U : Scheme)) [IsOpenImmersion f]
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (Scheme.Modules.restrictFunctor (f ≫ U.ι)).obj T ≅
      SheafOfModules.unit V.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorComp f U.ι).app T ≪≫
    (Scheme.Modules.restrictFunctor f).mapIso p ≪≫ Scheme.Modules.restrictUnitIso f

def cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso
    {X V : Scheme.{u}} (U : X.Opens) (f : V ⟶ (U : Scheme)) [IsOpenImmersion f]
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    {Z : Scheme.{u}} (j : Z ⟶ V) [IsClosedImmersion j]
    [IsClosedImmersion (j ≫ f)] [IsClosedImmersion ((j ≫ f) ≫ U.ι)] :
    (Scheme.Modules.restrictFunctor (f ≫ U.ι)).obj
      (closedImmersionIdealTwist ((j ≫ f) ≫ U.ι) T) ≅ closedImmersionModule j :=
  (Scheme.Modules.restrictFunctorComp f U.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor f).mapIso
      (cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso U T p (j ≫ f)) ≪≫
    cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j

theorem cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso_toUnit
    {X V : Scheme.{u}} (U : X.Opens) (f : V ⟶ (U : Scheme)) [IsOpenImmersion f]
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    {Z : Scheme.{u}} (j : Z ⟶ V) [IsClosedImmersion j]
    [IsClosedImmersion (j ≫ f)] [IsClosedImmersion ((j ≫ f) ≫ U.ι)] :
    (cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso U f T p j).hom ≫
      closedImmersionModuleToUnit j =
    (Scheme.Modules.restrictFunctor (f ≫ U.ι)).map
      ((closedImmersionIdealTwistSequence ((j ≫ f) ≫ U.ι) T).f ≫
        (schemeModuleTensorUnitLeftIso T).hom) ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p).hom := by
  let R := Scheme.Modules.restrictFunctor f
  let a := (closedImmersionIdealTwistSequence ((j ≫ f) ≫ U.ι) T).f ≫
    (schemeModuleTensorUnitLeftIso T).hom
  have h := congrArg (fun m => R.map m)
    (cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso_toUnit U T p (j ≫ f))
  rw [R.map_comp, R.map_comp] at h
  have hn := (Scheme.Modules.restrictFunctorComp f U.ι).hom.naturality a
  simp only [Functor.comp_map] at hn
  let b := ((Scheme.Modules.restrictFunctorComp f U.ι).app
    (closedImmersionIdealTwist ((j ≫ f) ≫ U.ι) T)).hom
  let e := R.map (cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso U T p (j ≫ f)).hom
  have hj := cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso_toUnit f j
  have hj' := congrArg (fun k => (b ≫ e) ≫ k) hj
  have hc := refinedSquare b e (R.map (closedImmersionModuleToUnit (j ≫ f)))
    (R.map ((Scheme.Modules.restrictFunctor U.ι).map a)) (R.map p.hom)
    ((Scheme.Modules.restrictFunctor (f ≫ U.ι)).map a)
    ((Scheme.Modules.restrictFunctorComp f U.ι).app T).hom
    (Scheme.Modules.restrictUnitIso f).hom h hn
  exact hj'.trans hc

end PfaffianDescent

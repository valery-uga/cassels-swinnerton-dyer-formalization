import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartRefinement
import PfaffianDescent.VoisinStandardOpenExtVanishing

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open IdealSheafDataModule ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false

private theorem localFactor {C : Type u} [Category C]
    {O P W T N : C} (u : O ≅ P) (p : T ≅ P) (e : W ≅ N)
    (a : W ⟶ T) (s : O ⟶ T) (t : P ⟶ N) (m : N ⟶ P)
    (hc : e.hom ≫ m = a ≫ p.hom)
    (ht : t ≫ m = u.inv ≫ s ≫ p.hom) :
    (u.hom ≫ t ≫ e.inv) ≫ a = s := by
  apply (cancel_mono p.hom).mp
  simp only [Category.assoc]
  rw [← hc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [ht]
  simp

/-- Native refined ideal coordinates detect the actual twisted quotient kernel. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChart_localKernel
    {X V : Scheme.{u}} (U : X.Opens) (f : V ⟶ (U : Scheme)) [IsOpenImmersion f]
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    {Z : Scheme.{u}} (j : Z ⟶ V) [IsClosedImmersion j]
    [IsClosedImmersion (j ≫ f)] [IsClosedImmersion ((j ≫ f) ≫ U.ι)]
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (t : SheafOfModules.unit V.ringCatSheaf ⟶ closedImmersionModule j)
    (ht : t ≫ closedImmersionModuleToUnit j =
      (Scheme.Modules.restrictUnitIso (f ≫ U.ι)).inv ≫
      (Scheme.Modules.restrictFunctor (f ≫ U.ι)).map s ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p).hom) :
    (Scheme.Modules.restrictFunctor (f ≫ U.ι)).map
      (s ≫ (schemeModuleTensorUnitLeftIso T).inv ≫
        (closedImmersionIdealTwistSequence ((j ≫ f) ≫ U.ι) T).g) = 0 := by
  let R := Scheme.Modules.restrictFunctor (f ≫ U.ι)
  let C := closedImmersionIdealTwistSequence ((j ≫ f) ≫ U.ι) T
  let e := cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso U f T p j
  let u := Scheme.Modules.restrictUnitIso (f ≫ U.ι)
  let p' := cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p
  let a := C.f ≫ (schemeModuleTensorUnitLeftIso T).hom
  let b := u.hom ≫ t ≫ e.inv
  have hb : b ≫ R.map a = R.map s :=
    localFactor u p' e (R.map a) (R.map s) t (closedImmersionModuleToUnit j)
      (cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso_toUnit U f T p j) ht
  have ha : R.map a ≫ R.map (schemeModuleTensorUnitLeftIso T).inv = R.map C.f := by
    change R.map (C.f ≫ (schemeModuleTensorUnitLeftIso T).hom) ≫
      R.map (schemeModuleTensorUnitLeftIso T).inv = _
    rw [← R.map_comp]
    simp
  rw [R.map_comp, R.map_comp, ← hb]
  simp only [Category.assoc]
  rw [← Category.assoc (R.map a), ha]
  rw [← R.map_comp C.f C.g, C.zero, R.map_zero, comp_zero]

/-- Restriction along an actual affine-chart isomorphism reflects the vanishing
of a morphism already restricted to the common open. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_restrictCompositeIso_reflect_zero
    {X V : Scheme.{u}} (U : X.Opens) (e : V ≅ (U : Scheme))
    {M N : X.Modules} (a : M ⟶ N)
    (ha : (Scheme.Modules.restrictFunctor (e.hom ≫ U.ι)).map a = 0) :
    (Scheme.Modules.restrictFunctor U.ι).map a = 0 := by
  let E := schemeModulesEquivalenceOfIsoRestrict e.symm
  letI : (Scheme.Modules.restrictFunctor e.hom).IsEquivalence := by
    change E.functor.IsEquivalence
    infer_instance
  letI : (Scheme.Modules.restrictFunctor e.hom).Faithful := Functor.IsEquivalence.faithful
  have h := (Scheme.Modules.restrictFunctorComp e.hom U.ι).hom.naturality a
  rw [ha, zero_comp] at h
  have hz : (Scheme.Modules.restrictFunctor e.hom).map
      ((Scheme.Modules.restrictFunctor U.ι).map a) = 0 := by
    apply (cancel_epi ((Scheme.Modules.restrictFunctorComp e.hom U.ι).hom.app M)).mp
    rw [comp_zero]
    exact h.symm
  apply (Scheme.Modules.restrictFunctor e.hom).map_injective
  simpa only [Functor.map_zero] using hz

end PfaffianDescent

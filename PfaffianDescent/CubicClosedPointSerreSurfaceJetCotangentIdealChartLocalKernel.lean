import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealChartAbstract

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open IdealSheafDataModule ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false

private theorem localFactorFromCoefficient {C : Type u} [Category C]
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

/-- A local preimage in the actual closed ideal kills the actual restricted
twisted quotient. All tensor and inclusion comparisons are constructed natively. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChart_localKernel
    {X : Scheme.{u}} (U : X.Opens) (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    {Z : Scheme.{u}} (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion j] [IsClosedImmersion (j ≫ U.ι)]
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (t : SheafOfModules.unit (U : Scheme).ringCatSheaf ⟶ closedImmersionModule j)
    (ht : t ≫ closedImmersionModuleToUnit j =
      (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map s ≫ p.hom) :
    (Scheme.Modules.restrictFunctor U.ι).map
      (s ≫ (schemeModuleTensorUnitLeftIso T).inv ≫
        (closedImmersionIdealTwistSequence (j ≫ U.ι) T).g) = 0 := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let C := closedImmersionIdealTwistSequence (j ≫ U.ι) T
  let e := cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso U T p j
  let u := Scheme.Modules.restrictUnitIso U.ι
  let a := C.f ≫ (schemeModuleTensorUnitLeftIso T).hom
  let b := u.hom ≫ t ≫ e.inv
  have hb : b ≫ R.map a = R.map s :=
    localFactorFromCoefficient u p e (R.map a) (R.map s) t
      (closedImmersionModuleToUnit j)
      (cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso_toUnit U T p j) ht
  have ha : R.map a ≫ R.map (schemeModuleTensorUnitLeftIso T).inv = R.map C.f := by
    change R.map (C.f ≫ (schemeModuleTensorUnitLeftIso T).hom) ≫
      R.map (schemeModuleTensorUnitLeftIso T).inv = _
    rw [← R.map_comp]
    simp
  rw [R.map_comp, R.map_comp, ← hb]
  simp only [Category.assoc]
  rw [← Category.assoc (R.map a), ha]
  rw [← R.map_comp C.f C.g, C.zero, R.map_zero, comp_zero]

end PfaffianDescent

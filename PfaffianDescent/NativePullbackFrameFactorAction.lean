import PfaffianDescent.NativeOpenPullbackUnitScalar
import PfaffianDescent.NativePositiveQuotientChartPullbackUnit
import PfaffianDescent.ActualPullbackTrivializationBasisComposition

/-! SOURCE ONLY. Native whole-coordinate action transported through a
proved actual chart square. Generic scalar laws are discharged by canonical
homogeneous-section coefficients in the geometric caller. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] isIso_pullbackUnitComparison

/-- Entire framed coordinate action under native pullback composition. -/
theorem actualPullbackTrivializationScalarComposition
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (f : Y ⟶ Z) (T : Z.Modules)
    (v : SheafOfModules.unit Z.ringCatSheaf ⟶ T)
    (e : (Scheme.Modules.pullback f).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (r : Γ(Y, ⊤))
    (hv : (Scheme.Modules.pullback f).map v ≫ e.hom =
      pullbackUnitComparison f ≫ unitEndomorphismOfRegularFunction r) :
    (Scheme.Modules.pullback (j ≫ f)).map v ≫
      (Scheme.Modules.pullbackComp j f).inv.app T ≫
      (Scheme.Modules.pullback j).map e.hom ≫ pullbackUnitComparison j =
    pullbackUnitComparison (j ≫ f) ≫
      unitEndomorphismOfRegularFunction (j.appTop r) := by
  let B := Scheme.Modules.pullbackComp j f
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  have hn : (Scheme.Modules.pullback (j ≫ f)).map v ≫ B.inv.app T =
      B.inv.app O ≫ (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback f).map v) := by
    exact B.inv.naturality v
  have hs : (Scheme.Modules.pullback j).map (unitEndomorphismOfRegularFunction r) ≫
      pullbackUnitComparison j = pullbackUnitComparison j ≫
        unitEndomorphismOfRegularFunction (j.appTop r) := by
    have h : inv (pullbackUnitComparison j) ≫
        (Scheme.Modules.pullback j).map (unitEndomorphismOfRegularFunction r) ≫
          pullbackUnitComparison j = unitEndomorphismOfRegularFunction (j.appTop r) := by
      let hunit := isIso_pullbackUnitComparison j
      letI : IsIso (pullbackUnitComparison j) := hunit
      have hOld := pullbackUnitEndomorphismOfRegularFunction_eq_appTop j hunit r
      unfold pullbackUnitEndomorphism at hOld
      have hchoose : Classical.choose hunit.out = inv (pullbackUnitComparison j) := by
        congr 1
      erw [hchoose] at hOld
      exact hOld
    have h' := congrArg (fun z => pullbackUnitComparison j ≫ z) h
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using h'
  calc
    _ = B.inv.app O ≫ (Scheme.Modules.pullback j).map
        ((Scheme.Modules.pullback f).map v) ≫
        (Scheme.Modules.pullback j).map e.hom ≫ pullbackUnitComparison j := by
      rw [← Category.assoc ((Scheme.Modules.pullback (j ≫ f)).map v) (B.inv.app T)
        ((Scheme.Modules.pullback j).map e.hom ≫ pullbackUnitComparison j), hn]
      simp only [Category.assoc]
    _ = B.inv.app O ≫ (Scheme.Modules.pullback j).map
        ((Scheme.Modules.pullback f).map v ≫ e.hom) ≫ pullbackUnitComparison j := by
      simp only [Functor.map_comp, Category.assoc]
    _ = B.inv.app O ≫ (Scheme.Modules.pullback j).map (pullbackUnitComparison f) ≫
        (Scheme.Modules.pullback j).map (unitEndomorphismOfRegularFunction r) ≫
          pullbackUnitComparison j := by rw [hv, Functor.map_comp]; rfl
    _ = B.inv.app O ≫ (Scheme.Modules.pullback j).map (pullbackUnitComparison f) ≫
        pullbackUnitComparison j ≫ unitEndomorphismOfRegularFunction (j.appTop r) := by
      rw [hs]
    _ = _ := by
      have hcomp : B.inv.app O ≫
          (Scheme.Modules.pullback j).map (pullbackUnitComparison f) ≫
          pullbackUnitComparison j = pullbackUnitComparison (j ≫ f) := by
        rw [← pullbackUnitComparison_comp j f, ← Category.assoc,
          B.inv_hom_id_app, Category.id_comp]
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ unitEndomorphismOfRegularFunction (j.appTop r)) hcomp

/-- Original unit-section normalization across pullback composition. -/
theorem actualPullbackCompositeUnitNormalized
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z) :
    (Scheme.Modules.pullback i).map (inv (pullbackUnitComparison f)) ≫
        (Scheme.Modules.pullbackComp i f).hom.app
          (SheafOfModules.unit Z.ringCatSheaf) ≫
        pullbackUnitComparison (i ≫ f) = pullbackUnitComparison i := by
  rw [pullbackUnitComparison_comp]
  rw [← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Transport of the SAME original section through the PROVED chart square.
No final bundle comparison is assumed in this structural helper. -/
theorem pullbackChartUnitIso_of_actual_factorization_scalarAction
    {X Y W V : Scheme.{u}} (f : X ⟶ Y) (i : W ⟶ X)
    (a : W ⟶ V) [IsOpenImmersion a] (j : V ⟶ Y)
    (h : i ≫ f = a ≫ j) (T : Y.Modules)
    (e : (Scheme.Modules.pullback j).obj T ≅ SheafOfModules.unit V.ringCatSheaf)
    (v : SheafOfModules.unit Y.ringCatSheaf ⟶ T) (r : Γ(V, ⊤))
    (hv : (Scheme.Modules.pullback j).map v ≫ e.hom =
      pullbackUnitComparison j ≫ unitEndomorphismOfRegularFunction r) :
    (Scheme.Modules.pullback i).map
        (inv (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map v) ≫
      (pullbackChartUnitIso_of_actual_factorization f i a j h T e).hom =
    pullbackUnitComparison i ≫ unitEndomorphismOfRegularFunction (a.appTop r) := by
  let B := Scheme.Modules.pullbackComp i f
  let C := Scheme.Modules.pullbackComp a j
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let tT := (eqToIso (congrArg (fun q : W ⟶ Y => (Scheme.Modules.pullback q).obj T) h)).hom
  let tO := (eqToIso (congrArg (fun q : W ⟶ Y => (Scheme.Modules.pullback q).obj O) h)).hom
  have hn : (Scheme.Modules.pullback i).map ((Scheme.Modules.pullback f).map v) ≫
      B.hom.app T = B.hom.app O ≫ (Scheme.Modules.pullback (i ≫ f)).map v := by
    exact B.hom.naturality v
  have ht : (Scheme.Modules.pullback (i ≫ f)).map v ≫ tT =
      tO ≫ (Scheme.Modules.pullback (a ≫ j)).map v :=
    actualPullbackMap_eqToIso_naturality (i ≫ f) (a ≫ j) h v
  have hu : tO ≫ pullbackUnitComparison (a ≫ j) = pullbackUnitComparison (i ≫ f) :=
    actualPullbackUnitComparison_eqToIso (i ≫ f) (a ≫ j) h
  have ha := actualPullbackTrivializationScalarComposition a j T v e r hv
  change (Scheme.Modules.pullback i).map
      (inv (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map v) ≫
    B.hom.app T ≫ tT ≫ C.inv.app T ≫ (Scheme.Modules.pullback a).map e.hom ≫
      pullbackUnitComparison a = _
  rw [Functor.map_comp]
  simp only [Category.assoc]
  calc
    _ = (Scheme.Modules.pullback i).map (inv (pullbackUnitComparison f)) ≫
        B.hom.app O ≫ (Scheme.Modules.pullback (i ≫ f)).map v ≫
        tT ≫ C.inv.app T ≫ (Scheme.Modules.pullback a).map e.hom ≫
        pullbackUnitComparison a := by
      rw [← Category.assoc ((Scheme.Modules.pullback i).map
        ((Scheme.Modules.pullback f).map v)) (B.hom.app T) _, hn]
      simp only [Category.assoc]
    _ = (Scheme.Modules.pullback i).map (inv (pullbackUnitComparison f)) ≫
        B.hom.app O ≫ tO ≫ (Scheme.Modules.pullback (a ≫ j)).map v ≫
        C.inv.app T ≫ (Scheme.Modules.pullback a).map e.hom ≫
        pullbackUnitComparison a := by
      rw [← Category.assoc ((Scheme.Modules.pullback (i ≫ f)).map v) tT _, ht]
      simp only [Category.assoc]
    _ = (Scheme.Modules.pullback i).map (inv (pullbackUnitComparison f)) ≫
        B.hom.app O ≫ tO ≫ pullbackUnitComparison (a ≫ j) ≫
          unitEndomorphismOfRegularFunction (a.appTop r) := by rw [ha]
    _ = (Scheme.Modules.pullback i).map (inv (pullbackUnitComparison f)) ≫
        B.hom.app O ≫ pullbackUnitComparison (i ≫ f) ≫
          unitEndomorphismOfRegularFunction (a.appTop r) := by
      rw [← Category.assoc tO (pullbackUnitComparison (a ≫ j)) _, hu]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ unitEndomorphismOfRegularFunction (a.appTop r))
        (actualPullbackCompositeUnitNormalized i f)

end PfaffianDescent

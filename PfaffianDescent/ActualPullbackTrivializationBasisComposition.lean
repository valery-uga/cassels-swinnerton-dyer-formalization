import PfaffianDescent.BundleSectionZeroLocus

/- SOURCE ONLY / UNVERIFIED. Actual unit comparisons and pullback
composition transport an internally established basis law. Generic
structural inputs are discharged in actual native/original callers. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualPullbackTrivializationBasisComposition
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z) (T : Z.Modules)
    (v : SheafOfModules.unit Z.ringCatSheaf ⟶ T)
    (e : (Scheme.Modules.pullback f).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (hv : (Scheme.Modules.pullback f).map v ≫ e.hom = pullbackUnitComparison f) :
    (Scheme.Modules.pullback (j ≫ f)).map v ≫
      (Scheme.Modules.pullbackComp j f).inv.app T ≫
      (Scheme.Modules.pullback j).map e.hom ≫ pullbackUnitComparison j =
      pullbackUnitComparison (j ≫ f) := by
  let B := Scheme.Modules.pullbackComp j f
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  have hn : (Scheme.Modules.pullback (j ≫ f)).map v ≫ B.inv.app T =
      B.inv.app O ≫ (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback f).map v) := by
    simpa only [Functor.comp_map] using B.inv.naturality v
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
    _ = B.inv.app O ≫ (Scheme.Modules.pullback j).map
        (pullbackUnitComparison f) ≫ pullbackUnitComparison j := by rw [hv]
    _ = _ := by
      rw [← pullbackUnitComparison_comp j f, ← Category.assoc,
        B.inv_hom_id_app, Category.id_comp]

lemma actualPullbackMap_eqToIso_naturality
    {X Z : Scheme.{u}} (q q' : X ⟶ Z) (h : q = q') {M N : Z.Modules}
    (v : M ⟶ N) :
    (Scheme.Modules.pullback q).map v ≫
      (eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj N) h)).hom =
    (eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj M) h)).hom ≫
      (Scheme.Modules.pullback q').map v := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualPullbackUnitComparison_eqToIso
    {X Z : Scheme.{u}} (q q' : X ⟶ Z) (h : q = q') :
    (eqToIso (congrArg (fun r => (Scheme.Modules.pullback r).obj
      (SheafOfModules.unit Z.ringCatSheaf)) h)).hom ≫ pullbackUnitComparison q' =
      pullbackUnitComparison q := by
  cases h
  simp

end PfaffianDescent

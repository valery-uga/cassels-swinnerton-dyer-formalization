import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentRestrictUnitComposition

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

private theorem sectionCoordinateOfComposition
    {A B C : Type u} [Category A] [Category B] [Category C]
    (F : A ⥤ C) (G : A ⥤ B) (H : B ⥤ C) (c : F ≅ G ⋙ H)
    {O T : A} {P : B} {Q : C} (ug : G.obj O ≅ P) (uf : H.obj P ≅ Q)
    (u : F.obj O ≅ Q) (hu : u = c.app O ≪≫ H.mapIso ug ≪≫ uf)
    (p : G.obj T ≅ P) (s : O ⟶ T) :
    u.inv ≫ F.map s ≫ (c.app T).hom ≫ H.map p.hom ≫ uf.hom =
    uf.inv ≫ H.map (ug.inv ≫ G.map s ≫ p.hom) ≫ uf.hom := by
  have h := congrArg (fun m => (c.app O).inv ≫ m) (c.hom.naturality s)
  change (c.app O).inv ≫ (F.map s ≫ (c.app T).hom) =
    (c.app O).inv ≫ ((c.app O).hom ≫ H.map (G.map s)) at h
  have hc : (c.app O).inv ≫ F.map s ≫ (c.app T).hom = H.map (G.map s) := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Functor.comp_map] using h
  rw [hu]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun m => uf.inv ≫ H.map ug.inv ≫ m ≫ H.map p.hom ≫ uf.hom) hc

/-- Local section coordinates commute with refinement of the actual chart. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_refinedSectionCoordinate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (T : Z.Modules)
    (p : (Scheme.Modules.restrictFunctor g).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ T) :
    (Scheme.Modules.restrictUnitIso (f ≫ g)).inv ≫
      (Scheme.Modules.restrictFunctor (f ≫ g)).map s ≫
      ((Scheme.Modules.restrictFunctorComp f g).app T).hom ≫
      (Scheme.Modules.restrictFunctor f).map p.hom ≫
      (Scheme.Modules.restrictUnitIso f).hom =
    (Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map
        ((Scheme.Modules.restrictUnitIso g).inv ≫
          (Scheme.Modules.restrictFunctor g).map s ≫ p.hom) ≫
      (Scheme.Modules.restrictUnitIso f).hom := by
  exact sectionCoordinateOfComposition
    (Scheme.Modules.restrictFunctor (f ≫ g)) (Scheme.Modules.restrictFunctor g)
    (Scheme.Modules.restrictFunctor f) (Scheme.Modules.restrictFunctorComp f g)
    (Scheme.Modules.restrictUnitIso g) (Scheme.Modules.restrictUnitIso f)
    (Scheme.Modules.restrictUnitIso (f ≫ g))
    (cubicClosedPointSerreSurfaceJetCotangent_restrictUnitIso_comp f g) p s

/-- The refined scalar coefficient is the literal restriction of the old one. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_refinedSectionCoefficient
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (T : Z.Modules)
    (p : (Scheme.Modules.restrictFunctor g).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ T) :
    BundleSectionZeroLocus.unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso (f ≫ g)).inv ≫
        (Scheme.Modules.restrictFunctor (f ≫ g)).map s ≫
        ((Scheme.Modules.restrictFunctorComp f g).app T).hom ≫
        (Scheme.Modules.restrictFunctor f).map p.hom ≫
        (Scheme.Modules.restrictUnitIso f).hom) =
    f.appTop (BundleSectionZeroLocus.unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso g).inv ≫
        (Scheme.Modules.restrictFunctor g).map s ≫ p.hom)) :=
  (congrArg BundleSectionZeroLocus.unitEndomorphismValue
    (cubicClosedPointSerreSurfaceJetCotangent_refinedSectionCoordinate f g T p s)).trans
    (BundleSectionZeroLocus.unitEndomorphismValue_restrict_eq_appTop f _)

end PfaffianDescent

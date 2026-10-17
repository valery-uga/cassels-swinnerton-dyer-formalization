import PfaffianDescent.BundleSectionZeroLocusNaturality

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Canonical structure-sheaf restriction coordinates compose literally. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_restrictUnitIso_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    Scheme.Modules.restrictUnitIso (f ≫ g) =
    (Scheme.Modules.restrictFunctorComp f g).app (SheafOfModules.unit Z.ringCatSheaf) ≪≫
      (Scheme.Modules.restrictFunctor f).mapIso (Scheme.Modules.restrictUnitIso g) ≪≫
      Scheme.Modules.restrictUnitIso f := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext z
  change ((f ≫ g).appIso V.unop).hom z =
    (f.appIso V.unop).hom
      ((g.appIso (f ''ᵁ V.unop)).hom
        ((Z.presheaf.map (eqToIso (show g ''ᵁ (f ''ᵁ V.unop) =
          (f ≫ g) ''ᵁ V.unop from by simp)).op.hom).hom z))
  rw [Scheme.Hom.comp_appIso]
  rfl

end PfaffianDescent

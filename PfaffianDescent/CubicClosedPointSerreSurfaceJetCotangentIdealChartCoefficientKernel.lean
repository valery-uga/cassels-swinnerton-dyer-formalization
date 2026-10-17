import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeIdealCoefficientKernel

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open IdealSheafDataModule BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

private theorem inclusionSquare {C D : Type u} [Category C] [Category D]
    (R : C ⥤ D) {O M T : C} {W N P : D}
    (b : W ⟶ R.obj O) (v : O ⟶ M) (a : M ⟶ T)
    (e : R.obj M ⟶ N) (n : N ⟶ P) (p : R.obj T ⟶ P)
    (he : e ≫ n = R.map a ≫ p) :
    (b ≫ R.map v ≫ e) ≫ n = b ≫ R.map (v ≫ a) ≫ p := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← he]

/-- Any literal chart inclusion square forces the actual global ideal
section's positive-twist coefficient into the native chart kernel. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_idealChartCoefficientKernel
    {X : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion f]
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    {M T : X.Modules} (a : M ⟶ T)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅
      closedImmersionModule (Spec.map (CommRingCat.ofHom g)))
    (p : (Scheme.Modules.restrictFunctor f).obj T ≅
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf)
    (he : e.hom ≫ closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g)) =
      (Scheme.Modules.restrictFunctor f).map a ≫ p.hom)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    g ((affineGlobalSectionsUnitLinearEquiv (A := A))
      (unitEndomorphismValue ((Scheme.Modules.restrictUnitIso f).inv ≫
        (Scheme.Modules.restrictFunctor f).map (v ≫ a) ≫ p.hom))) = 0 := by
  have h := inclusionSquare (Scheme.Modules.restrictFunctor f)
    (Scheme.Modules.restrictUnitIso f).inv v a e.hom
    (closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g))) p.hom he
  have hk := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealCoefficientKernel g
    ((Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map v ≫ e.hom)
  exact (congrArg (fun k => g ((affineGlobalSectionsUnitLinearEquiv (A := A))
    (unitEndomorphismValue k))) h).symm.trans hk

end PfaffianDescent

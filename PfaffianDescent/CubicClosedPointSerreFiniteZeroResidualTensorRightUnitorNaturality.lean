import PfaffianDescent.SchemeModuleTensor
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}}
theorem cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_naturality
    {M N : X.Modules} (f : M ⟶ N) :
    schemeModuleTensorMap f (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫
        (schemeModuleTensorUnitRightIso N).hom =
      (schemeModuleTensorUnitRightIso M).hom ≫ f := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  let M₀ : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := M.val
  let M₁ : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) := N.val
  let f₀ : M₀ ⟶ M₁ := f.val
  let U : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
    PresheafOfModules.unit (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
  letI : MonoidalCategory
      (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    PresheafOfModules.monoidalCategory
  have hraw : PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U) ≫ (ρ_ M₁).hom =
      (ρ_ M₀).hom ≫ f₀ :=
    rightUnitor_naturality f₀
  change F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) ≫
      (F.map (ρ_ M₁).hom ≫ adj.counit.app N) =
    (F.map (ρ_ M₀).hom ≫ adj.counit.app M) ≫ f
  have hcounit : F.map f₀ ≫ adj.counit.app N = adj.counit.app M ≫ f := by
    change F.map f.val ≫ adj.counit.app N = adj.counit.app M ≫ f
    exact adj.counit.naturality f
  calc
    F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) ≫
        (F.map (ρ_ M₁).hom ≫ adj.counit.app N) =
        (F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U)) ≫
          F.map (ρ_ M₁).hom) ≫ adj.counit.app N := (Category.assoc _ _ _).symm
    _ = F.map (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U) ≫
          (ρ_ M₁).hom) ≫ adj.counit.app N :=
        congrArg (fun q => q ≫ adj.counit.app N)
          (F.map_comp (PresheafOfModules.Monoidal.tensorHom f₀ (𝟙 U))
            (ρ_ M₁).hom).symm
    _ = F.map ((ρ_ M₀).hom ≫ f₀) ≫ adj.counit.app N :=
        congrArg (fun q => F.map q ≫ adj.counit.app N) hraw
    _ = (F.map (ρ_ M₀).hom ≫ F.map f₀) ≫ adj.counit.app N :=
        congrArg (fun q => q ≫ adj.counit.app N) (F.map_comp (ρ_ M₀).hom f₀)
    _ = F.map (ρ_ M₀).hom ≫ (F.map f₀ ≫ adj.counit.app N) :=
        Category.assoc _ _ _
    _ = F.map (ρ_ M₀).hom ≫ (adj.counit.app M ≫ f) := by
      rw [hcounit]
    _ = (F.map (ρ_ M₀).hom ≫ adj.counit.app M) ≫ f :=
        (Category.assoc _ _ _).symm

end PfaffianDescent

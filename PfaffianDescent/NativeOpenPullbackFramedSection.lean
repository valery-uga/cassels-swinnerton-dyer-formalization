import PfaffianDescent.NativeOpenPullbackUnitScalar

/-! SOURCE ONLY. Whole native section/frame action under the original
restriction-versus-pullback comparison, before any coefficient evaluation. -/
noncomputable section
namespace PfaffianDescent.BundleSectionZeroLocus
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original section morphism has the SAME framed restriction
and pullback, as entire module morphisms. -/
theorem nativeOpenPullbackFramedSection_eq_restricted
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (T : Y.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj T ≅
      SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ T) :
    inv (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map s ≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).symm.app T ≪≫ e).hom =
    (Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map s ≫ e.hom := by
  let α := Scheme.Modules.restrictFunctorIsoPullback f
  let v := Scheme.Modules.restrictUnitIso f
  rw [pullbackUnitComparison_inv_eq_nativeRestrict]
  change (v.inv ≫ α.hom.app _) ≫ (Scheme.Modules.pullback f).map s ≫
    (α.inv.app T ≫ e.hom) = v.inv ≫ (Scheme.Modules.restrictFunctor f).map s ≫ e.hom
  calc
    _ = v.inv ≫ (α.hom.app _ ≫ (Scheme.Modules.pullback f).map s) ≫
      α.inv.app T ≫ e.hom := by rfl
    _ = v.inv ≫ ((Scheme.Modules.restrictFunctor f).map s ≫ α.hom.app T) ≫
      α.inv.app T ≫ e.hom := by
      exact congrArg (fun z => v.inv ≫ z ≫ α.inv.app T ≫ e.hom)
        (α.hom.naturality s).symm
    _ = v.inv ≫ (Scheme.Modules.restrictFunctor f).map s ≫ e.hom := by
      have hmid : ((Scheme.Modules.restrictFunctor f).map s ≫ α.hom.app T) ≫
          α.inv.app T = (Scheme.Modules.restrictFunctor f).map s := by
        calc
          _ = (Scheme.Modules.restrictFunctor f).map s ≫
              (α.hom.app T ≫ α.inv.app T) := by rfl
          _ = (Scheme.Modules.restrictFunctor f).map s ≫ 𝟙 _ :=
            congrArg (fun z => (Scheme.Modules.restrictFunctor f).map s ≫ z)
              (α.hom_inv_id_app T)
          _ = _ := Category.comp_id _
      exact congrArg (fun z => v.inv ≫ z ≫ e.hom) hmid

end PfaffianDescent.BundleSectionZeroLocus

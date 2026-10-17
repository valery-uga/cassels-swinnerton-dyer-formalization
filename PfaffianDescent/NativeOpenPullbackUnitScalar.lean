import PfaffianDescent.BundleSectionZeroLocusNaturality

/-! SOURCE ONLY. Whole native pullback scalar transport on an actual open
immersion, derived from the existing restriction/pullback comparison. -/
noncomputable section
namespace PfaffianDescent.BundleSectionZeroLocus
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual inverse of the canonical pullback-unit comparison on an open. -/
theorem pullbackUnitComparison_inv_eq_nativeRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    inv (pullbackUnitComparison f) =
      (Scheme.Modules.restrictUnitIso f).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
          (SheafOfModules.unit Y.ringCatSheaf) := by
  let α := Scheme.Modules.restrictFunctorIsoPullback f
  let v := Scheme.Modules.restrictUnitIso f
  apply (IsIso.eq_inv_of_hom_inv_id (by
    rw [pullbackUnitComparison_eq_restrict]
    change (α.inv.app _ ≫ v.hom) ≫ (v.inv ≫ α.hom.app _) = 𝟙 _
    calc
      (α.inv.app _ ≫ v.hom) ≫ (v.inv ≫ α.hom.app _) =
          α.inv.app _ ≫ (v.hom ≫ v.inv) ≫ α.hom.app _ := by rfl
      _ = α.inv.app _ ≫ (𝟙 _ ≫ α.hom.app _) := by
        exact congrArg (fun z => α.inv.app _ ≫ (z ≫ α.hom.app _)) v.hom_inv_id
      _ = α.inv.app _ ≫ α.hom.app _ := by rw [Category.id_comp]
      _ = 𝟙 _ := α.inv_hom_id_app _)).symm

/-- Conjugated pullback of an entire unit endomorphism equals its actual
restricted endomorphism, before extracting any coefficient. -/
theorem pullbackUnitEndomorphism_eq_nativeRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      SheafOfModules.unit Y.ringCatSheaf) :
    inv (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map a ≫
        pullbackUnitComparison f =
      (Scheme.Modules.restrictUnitIso f).inv ≫
        (Scheme.Modules.restrictFunctor f).map a ≫
          (Scheme.Modules.restrictUnitIso f).hom := by
  let α := Scheme.Modules.restrictFunctorIsoPullback f
  let v := Scheme.Modules.restrictUnitIso f
  rw [pullbackUnitComparison_inv_eq_nativeRestrict,
    pullbackUnitComparison_eq_restrict]
  change (v.inv ≫ α.hom.app _) ≫ (Scheme.Modules.pullback f).map a ≫
      (α.inv.app _ ≫ v.hom) =
    v.inv ≫ (Scheme.Modules.restrictFunctor f).map a ≫ v.hom
  calc
    _ = v.inv ≫ (α.hom.app _ ≫ (Scheme.Modules.pullback f).map a) ≫
        α.inv.app _ ≫ v.hom := by rfl
    _ = v.inv ≫ ((Scheme.Modules.restrictFunctor f).map a ≫ α.hom.app _) ≫
        α.inv.app _ ≫ v.hom := by
      exact congrArg (fun z => v.inv ≫ z ≫ α.inv.app _ ≫ v.hom)
        (α.hom.naturality a).symm
    _ = v.inv ≫ (Scheme.Modules.restrictFunctor f).map a ≫ v.hom := by
      have hmid : ((Scheme.Modules.restrictFunctor f).map a ≫ α.hom.app _) ≫
          α.inv.app _ = (Scheme.Modules.restrictFunctor f).map a := by
        calc
          _ = (Scheme.Modules.restrictFunctor f).map a ≫
              (α.hom.app _ ≫ α.inv.app _) := by rfl
          _ = (Scheme.Modules.restrictFunctor f).map a ≫ 𝟙 _ :=
            congrArg (fun z => (Scheme.Modules.restrictFunctor f).map a ≫ z)
              (α.hom_inv_id_app _)
          _ = _ := Category.comp_id _
      exact congrArg (fun z => v.inv ≫ z ≫ v.hom) hmid

/- The original BundleSectionZeroLocusNaturality already proves
pullbackUnitEndomorphismOfRegularFunction_eq_appTop with its internally
supplied unit-IsIso argument. Reuse it; do not redeclare that kernel name. -/

end PfaffianDescent.BundleSectionZeroLocus

import PfaffianDescent.ActualPointLocalNativeOpenChartAction
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealOpenRestrictionInclusion

/-! SOURCE ONLY, UNVERIFIED. For every actual local ideal generator,
derive the global/open conormal differential square using the true ideal
inclusion and the genuine differential sheaf. No desired square is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualIdealOpenRestrictionIso_nativeCoefficient
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {L : Type u} [Field L] (j : Spec (.of L) ⟶ Y)
    [IsClosedImmersion j] [IsClosedImmersion (j ≫ f)]
    (z : (closedImmersionModule j).val.obj (op ⊤)) :
    (f.appIso ⊤).hom
      ((closedImmersionModuleToUnit (j ≫ f)).val.app (op (f ''ᵁ ⊤))
        ((cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j).inv.val.app
          (op ⊤) z)) =
      (closedImmersionModuleToUnit j).val.app (op ⊤) z := by
  let E := cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j
  have h := cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso_toUnit f j
  have hInv : E.inv ≫
      ((Scheme.Modules.restrictFunctor f).map (closedImmersionModuleToUnit (j ≫ f)) ≫
        (Scheme.Modules.restrictUnitIso f).hom) = closedImmersionModuleToUnit j := by
    rw [← h, ← Category.assoc, E.inv_hom_id, Category.id_comp]
  exact congrArg (fun a => a.val.app (op ⊤) z) hInv

lemma actualGlobalConormalOpenChartGeneratorSquare
    {k L : Type u} [CommRing k] [Field L] {X Y : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsOpenImmersion f]
    (j : Spec (.of L) ⟶ Y) [IsClosedImmersion j] [IsClosedImmersion (j ≫ f)]
    (z : (closedImmersionModule j).val.obj (op ⊤)) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualModulePointChartSourceFactorizationIso f j (j ≫ f) rfl
        (schemeRelativeDifferentials g) (schemeRelativeDifferentials (f ≫ g))
        (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm).hom
      ((moduleSpecΓFunctor (R := .of L)).map
        (actualGlobalClosedConormalDifferentialMap g (j ≫ f))
        (actualPointLocalSectionClass (j ≫ f) (closedImmersionModule (j ≫ f)) (f ''ᵁ ⊤)
          (actualFieldPointFactor_preimage_image_top f j (j ≫ f) rfl)
          ((cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j).inv.val.app
            (op ⊤) z))) =
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap (f ≫ g) j)
      (actualPointLocalSectionClass j (closedImmersionModule j) ⊤ (by rfl) z) := by
  rw [actualGlobalConormalPointLocalNativeOpenChartAction,
    actualIdealOpenRestrictionIso_nativeCoefficient,
    actualGlobalConormalPointLocalSectionAction]

end PfaffianDescent

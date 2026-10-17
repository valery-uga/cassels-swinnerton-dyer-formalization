import PfaffianDescent.ActualPointLocalChartSourceFactorization
import PfaffianDescent.ActualPointLocalClassTopNormalization
import PfaffianDescent.ActualGlobalConormalPointLocalChartDerivative

/-! SOURCE ONLY, UNVERIFIED. True global differential action in any actual
open chart, including Spec(chart), on LOCAL ideal sections. The source and
target fiber comparisons are built from actual adjunctions and the genuine
open differential-sheaf Iso; none is an input comparison square. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualRestrictUnitImageTopNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (z : M.val.obj (op (f ''ᵁ (⊤ : Y.Opens)))) :
    (M.restrict f).val.map (eqToHom (congrArg op (f.preimage_image_eq ⊤)))
      (((Scheme.Modules.restrictAdjunction f).unit.app M).val.app (op (f ''ᵁ ⊤)) z) =
      (M.restrictAppIso f ⊤).inv z := by
  let t : op (f ⁻¹ᵁ (f ''ᵁ (⊤ : Y.Opens))) ⟶ op (⊤ : Y.Opens) :=
    eqToHom (congrArg op (f.preimage_image_eq ⊤))
  let a := (homOfLE (f.image_preimage_le (f ''ᵁ (⊤ : Y.Opens)))).op
  let b := (f.opensFunctor.map t.unop).op
  have hab : a ≫ b = 𝟙 (op (f ''ᵁ (⊤ : Y.Opens))) := Subsingleton.elim _ _
  have hm : M.presheaf.map a ≫ M.presheaf.map b =
      𝟙 (M.presheaf.obj (op (f ''ᵁ (⊤ : Y.Opens)))) := by
    rw [← M.presheaf.map_comp, hab, M.presheaf.map_id]
  have h : ((Scheme.Modules.restrictAdjunction f).unit.app M).app (f ''ᵁ ⊤) ≫
      (M.restrict f).presheaf.map t = (M.restrictAppIso f ⊤).inv := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    exact hm
  exact ConcreteCategory.congr_hom h z

lemma actualPointLocalChartSourceFactorization_image_top
    {L : Type u} [Field L] {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (j : Spec (.of L) ⟶ Y)
    (q : Spec (.of L) ⟶ X) (hfac : j ≫ f = q)
    (M : X.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N)
    (z : M.val.obj (op (f ''ᵁ (⊤ : Y.Opens)))) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualModulePointChartSourceFactorizationIso f j q hfac M N e).hom
      (actualPointLocalSectionClass q M (f ''ᵁ ⊤)
        (actualFieldPointFactor_preimage_image_top f j q hfac) z) =
    actualPointLocalSectionClass j N ⊤ (by rfl)
      (e.hom.val.app (op ⊤) ((M.restrictAppIso f ⊤).inv z)) := by
  rw [actualPointLocalChartSourceFactorization,
    actualPointLocalSectionClass_eq_top j N _ _ (f.preimage_image_eq ⊤)]
  let t := eqToHom (congrArg op (f.preimage_image_eq (⊤ : Y.Opens)))
  have hn := ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality t)
    (((Scheme.Modules.restrictAdjunction f).unit.app M).val.app (op (f ''ᵁ ⊤)) z)
  change e.hom.val.app (op ⊤)
      ((M.restrict f).val.map t
        (((Scheme.Modules.restrictAdjunction f).unit.app M).val.app (op (f ''ᵁ ⊤)) z)) =
    N.val.map t
      (e.hom.val.app (op (f ⁻¹ᵁ (f ''ᵁ ⊤)))
        (((Scheme.Modules.restrictAdjunction f).unit.app M).val.app (op (f ''ᵁ ⊤)) z)) at hn
  apply congrArg (fun w => actualPointLocalSectionClass j N ⊤ (by rfl) w)
  exact hn.symm.trans (congrArg (fun w => e.hom.val.app (op ⊤) w)
    (actualRestrictUnitImageTopNormalization f M z))

lemma actualGlobalConormalPointLocalNativeOpenChartAction
    {k L : Type u} [CommRing k] [Field L] {X Y : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsOpenImmersion f]
    (j : Spec (.of L) ⟶ Y) (q : Spec (.of L) ⟶ X) [IsClosedImmersion q]
    (hfac : j ≫ f = q)
    (z : (closedImmersionModule q).val.obj (op (f ''ᵁ (⊤ : Y.Opens)))) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualModulePointChartSourceFactorizationIso f j q hfac
        (schemeRelativeDifferentials g) (schemeRelativeDifferentials (f ≫ g))
        (actualOpenImmersionDifferentialSheafRestrictionIso f g).symm).hom
      ((moduleSpecΓFunctor (R := .of L)).map
        (actualGlobalClosedConormalDifferentialMap g q)
        (actualPointLocalSectionClass q (closedImmersionModule q) (f ''ᵁ ⊤)
          (actualFieldPointFactor_preimage_image_top f j q hfac) z)) =
    actualPointLocalSectionClass j (schemeRelativeDifferentials (f ≫ g)) ⊤ (by rfl)
      (actualRelativeDifferentialSection (f ≫ g) ⊤
        ((f.appIso ⊤).hom
          ((closedImmersionModuleToUnit q).val.app (op (f ''ᵁ ⊤)) z))) := by
  rw [actualGlobalConormalPointLocalChartDerivative g f j q hfac z,
    actualPointLocalChartSourceFactorization_image_top]
  change actualPointLocalSectionClass j (schemeRelativeDifferentials (f ≫ g)) ⊤ _
    ((actualOpenImmersionDifferentialSheafRestrictionIso f g).inv.val.app (op ⊤)
      ((actualOpenImmersionDifferentialSheafRestrictionIso f g).hom.val.app (op ⊤) _)) = _
  have h := ConcreteCategory.congr_hom
    (congrArg (fun a => a.val.app (op (⊤ : Y.Opens)))
      (actualOpenImmersionDifferentialSheafRestrictionIso f g).hom_inv_id)
    (actualRelativeDifferentialSection (f ≫ g) ⊤
      ((f.appIso ⊤).hom
        ((closedImmersionModuleToUnit q).val.app (op (f ''ᵁ ⊤)) z)))
  change (actualOpenImmersionDifferentialSheafRestrictionIso f g).inv.val.app (op ⊤)
      ((actualOpenImmersionDifferentialSheafRestrictionIso f g).hom.val.app (op ⊤)
        (actualRelativeDifferentialSection (f ≫ g) ⊤
          ((f.appIso ⊤).hom
            ((closedImmersionModuleToUnit q).val.app (op (f ''ᵁ ⊤)) z)))) =
    actualRelativeDifferentialSection (f ≫ g) ⊤
      ((f.appIso ⊤).hom
        ((closedImmersionModuleToUnit q).val.app (op (f ''ᵁ ⊤)) z)) at h
  exact congrArg (fun w => actualPointLocalSectionClass j
    (schemeRelativeDifferentials (f ≫ g)) ⊤ (by rfl) w) h

end PfaffianDescent

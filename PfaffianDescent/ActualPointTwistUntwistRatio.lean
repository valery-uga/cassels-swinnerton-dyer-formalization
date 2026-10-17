import PfaffianDescent.ActualTensorUnitAutomorphismSectionAction

/- SOURCE ONLY / UNVERIFIED. TWO ACTUAL twist Isos at SAME field point:
their untwist ratio is proved, not assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def actualPointTwistUntwistIso
    {L : Type u} [Field L] (M T : (Spec (.of L)).Modules)
    (e : T ≅ SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    schemeModuleTensor M T ≅ M :=
  schemeModuleTensorMapIso (Iso.refl M) e ≪≫ schemeModuleTensorUnitRightIso M

def actualPointTwistTrivializationScalar
    {L : Type u} [Field L] {T : (Spec (.of L)).Modules}
    (e0 e1 : T ≅ SheafOfModules.unit (Spec (.of L)).ringCatSheaf) : L :=
  actualFieldUnitAutomorphismScalar (e0.inv ≫ e1.hom)

theorem actualPointTwistTrivializationScalar_ne_zero
    {L : Type u} [Field L] {T : (Spec (.of L)).Modules}
    (e0 e1 : T ≅ SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    actualPointTwistTrivializationScalar e0 e1 ≠ 0 := by
  let e : SheafOfModules.unit (Spec (.of L)).ringCatSheaf ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf := e0.symm ≪≫ e1
  letI : IsIso (e0.inv ≫ e1.hom) := by
    change IsIso e.hom
    infer_instance
  exact actualFieldUnitAutomorphismScalar_ne_zero (e0.inv ≫ e1.hom)

lemma actualPointTwistUntwist_ratio_hom
    {L : Type u} [Field L] (M T : (Spec (.of L)).Modules)
    (e0 e1 : T ≅ SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    (actualPointTwistUntwistIso M T e0).inv ≫ (actualPointTwistUntwistIso M T e1).hom =
      (schemeModuleTensorUnitRightIso M).inv ≫
        schemeModuleTensorMap (𝟙 M) (e0.inv ≫ e1.hom) ≫
          (schemeModuleTensorUnitRightIso M).hom := by
  change ((schemeModuleTensorUnitRightIso M).inv ≫ schemeModuleTensorMap (𝟙 M) e0.inv) ≫
    (schemeModuleTensorMap (𝟙 M) e1.hom ≫ (schemeModuleTensorUnitRightIso M).hom) = _
  have ht : schemeModuleTensorMap (𝟙 M) e0.inv ≫
      schemeModuleTensorMap (𝟙 M) e1.hom =
        schemeModuleTensorMap (𝟙 M) (e0.inv ≫ e1.hom) :=
    (schemeModuleTensorMap_comp (𝟙 M) e0.inv (𝟙 M) e1.hom).trans
      (congrArg (fun f : M ⟶ M => schemeModuleTensorMap f (e0.inv ≫ e1.hom))
        (Category.id_comp (𝟙 M)))
  calc
    _ = (schemeModuleTensorUnitRightIso M).inv ≫
        ((schemeModuleTensorMap (𝟙 M) e0.inv ≫
          schemeModuleTensorMap (𝟙 M) e1.hom) ≫
            (schemeModuleTensorUnitRightIso M).hom) := by
      simp only [Category.assoc]
    _ = (schemeModuleTensorUnitRightIso M).inv ≫
        (schemeModuleTensorMap (𝟙 M) (e0.inv ≫ e1.hom) ≫
          (schemeModuleTensorUnitRightIso M).hom) :=
      congrArg (fun k => (schemeModuleTensorUnitRightIso M).inv ≫
        (k ≫ (schemeModuleTensorUnitRightIso M).hom)) ht
    _ = _ := rfl

theorem actualPointTwistUntwist_ratio_section_scalar
    {L : Type u} [Field L] (M T : (Spec (.of L)).Modules)
    (e0 e1 : T ≅ SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (s : SchemeModuleGlobalSectionsOver (𝟙 (Spec (.of L))) M) :
    s ≫ (actualPointTwistUntwistIso M T e0).inv ≫
      (actualPointTwistUntwistIso M T e1).hom =
        actualPointTwistTrivializationScalar e0 e1 • s := by
  rw [actualPointTwistUntwist_ratio_hom]
  exact actualFieldTensorUnitAutomorphism_section_scalar M _ s

end PfaffianDescent

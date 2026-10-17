import PfaffianDescent.ActualFieldUnitAutomorphismScalar
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/- SOURCE ONLY / UNVERIFIED. Tensor balancing and actual unit naturality
compute an arbitrary unit automorphism's action on EVERY genuine section. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualTensorRightUnit_naturality
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    schemeModuleTensorMap f (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫
      (schemeModuleTensorUnitRightIso N).hom =
        (schemeModuleTensorUnitRightIso M).hom ≫ f :=
  (schemeModuleTensorRightUnitIso (X := X)).hom.naturality f

lemma actualTensorUnitAutomorphism_section_action
    {X : Scheme.{u}} (M : X.Modules)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    s ≫ (schemeModuleTensorUnitRightIso M).inv ≫
      schemeModuleTensorMap (𝟙 M) a ≫ (schemeModuleTensorUnitRightIso M).hom = a ≫ s := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let eM := schemeModuleTensorUnitRightIso M
  let eO := schemeModuleTensorUnitRightIso O
  have hs : s ≫ eM.inv = eO.inv ≫ schemeModuleTensorMap s (𝟙 O) :=
    (schemeModuleTensorRightUnitIso (X := X)).inv.naturality s
  have hbal : schemeModuleTensorMap s (𝟙 O) ≫ schemeModuleTensorMap (𝟙 M) a =
      schemeModuleTensorMap a (𝟙 O) ≫ schemeModuleTensorMap s (𝟙 O) := by
    rw [schemeModuleTensorMap_unit_central a, schemeModuleTensorMap_comp,
      schemeModuleTensorMap_comp]
    exact (congrArg₂ (fun (f : O ⟶ M) (g : O ⟶ O) => schemeModuleTensorMap f g)
      (Category.comp_id s) (Category.id_comp a)).trans
        (congrArg₂ (fun (f : O ⟶ M) (g : O ⟶ O) => schemeModuleTensorMap f g)
          (Category.id_comp s) (Category.comp_id a)).symm
  have hS : schemeModuleTensorMap s (𝟙 O) ≫ eM.hom = eO.hom ≫ s :=
    actualTensorRightUnit_naturality (X := X) s
  have hA : schemeModuleTensorMap a (𝟙 O) ≫ eO.hom = eO.hom ≫ a :=
    actualTensorRightUnit_naturality (X := X) a
  calc
    s ≫ eM.inv ≫ schemeModuleTensorMap (𝟙 M) a ≫ eM.hom =
        (s ≫ eM.inv) ≫ (schemeModuleTensorMap (𝟙 M) a ≫ eM.hom) :=
      (Category.assoc _ _ _).symm
    _ = (eO.inv ≫ schemeModuleTensorMap s (𝟙 O)) ≫
        (schemeModuleTensorMap (𝟙 M) a ≫ eM.hom) :=
      congrArg (fun k => k ≫ (schemeModuleTensorMap (𝟙 M) a ≫ eM.hom)) hs
    _ = eO.inv ≫ ((schemeModuleTensorMap s (𝟙 O) ≫
        schemeModuleTensorMap (𝟙 M) a) ≫ eM.hom) := by simp only [Category.assoc]
    _ = eO.inv ≫ ((schemeModuleTensorMap a (𝟙 O) ≫
        schemeModuleTensorMap s (𝟙 O)) ≫ eM.hom) :=
      congrArg (fun k => eO.inv ≫ (k ≫ eM.hom)) hbal
    _ = eO.inv ≫ (schemeModuleTensorMap a (𝟙 O) ≫
        (schemeModuleTensorMap s (𝟙 O) ≫ eM.hom)) :=
      congrArg (fun k => eO.inv ≫ k) (Category.assoc _ _ _)
    _ = eO.inv ≫ (schemeModuleTensorMap a (𝟙 O) ≫ (eO.hom ≫ s)) :=
      congrArg (fun k => eO.inv ≫ (schemeModuleTensorMap a (𝟙 O) ≫ k)) hS
    _ = eO.inv ≫ ((schemeModuleTensorMap a (𝟙 O) ≫ eO.hom) ≫ s) :=
      congrArg (fun k => eO.inv ≫ k) (Category.assoc _ _ _).symm
    _ = eO.inv ≫ ((eO.hom ≫ a) ≫ s) :=
      congrArg (fun k => eO.inv ≫ (k ≫ s)) hA
    _ = (eO.inv ≫ eO.hom) ≫ (a ≫ s) := by simp only [Category.assoc]
    _ = a ≫ s := by rw [eO.inv_hom_id, Category.id_comp]

theorem actualFieldTensorUnitAutomorphism_section_scalar
    {L : Type u} [Field L] (M : (Spec (.of L)).Modules)
    (a : SheafOfModules.unit (Spec (.of L)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (s : SchemeModuleGlobalSectionsOver (𝟙 (Spec (.of L))) M) :
    s ≫ (schemeModuleTensorUnitRightIso M).inv ≫
      schemeModuleTensorMap (𝟙 M) a ≫ (schemeModuleTensorUnitRightIso M).hom =
        actualFieldUnitAutomorphismScalar a • s := by
  rw [actualTensorUnitAutomorphism_section_action (X := Spec (.of L)) M a s]
  change a ≫ s = schemeModuleConstantEndomorphism (𝟙 (Spec (.of L)))
    (actualFieldUnitAutomorphismScalar a) ≫ s
  exact congrArg (fun b => b ≫ s) (actualFieldUnitAutomorphism_eq_constant (L := L) a)

end PfaffianDescent

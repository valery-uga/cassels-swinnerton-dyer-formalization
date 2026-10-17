import PfaffianDescent.CoordinateModuleSheaf
import PfaffianDescent.SheafFreeIso
import Mathlib.CategoryTheory.Preadditive.Biproducts

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (X : Scheme.{u}) (ι : Type)

noncomputable def coordinateModuleSheafFan :
    Fan (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) :=
  Fan.mk (coordinateModuleSheaf X ι)
    (fun i => ⟨coordinateModulePresheafProjection X ι i⟩)

noncomputable def coordinateModuleSheafFanIsLimit : IsLimit (coordinateModuleSheafFan X ι) :=
  isLimitOfReflects (SheafOfModules.forget X.ringCatSheaf)
    (coordinateModulePresheafFanIsLimit X ι)

/-- Finite tuples of regular functions form an actual finite free sheaf. -/
noncomputable def coordinateModuleSheafFree [Finite ι] :
    (coordinateModuleSheaf X ι : SheafOfModules X.ringCatSheaf) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} ι) := by
  haveI : HasBiproduct (fun _ : ULift.{u} ι => SheafOfModules.unit X.ringCatSheaf) :=
    HasBiproduct.of_hasProduct _
  exact (coordinateModuleSheafFanIsLimit X ι).conePointUniqueUpToIso
    (productIsProduct (fun _ : ι => SheafOfModules.unit X.ringCatSheaf)) ≪≫
  Pi.whiskerEquiv (f := fun _ : ι => SheafOfModules.unit X.ringCatSheaf)
    (g := fun _ : ULift.{u} ι => SheafOfModules.unit X.ringCatSheaf) Equiv.ulift.symm (fun _ => Iso.refl (SheafOfModules.unit X.ringCatSheaf)) ≪≫
  (biproduct.isoProduct (fun _ : ULift.{u} ι => SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
  biproduct.isoCoproduct (fun _ : ULift.{u} ι => SheafOfModules.unit X.ringCatSheaf)

instance coordinateModuleSheaf_isLocallyFree [Finite ι] :
    (coordinateModuleSheaf X ι : SheafOfModules X.ringCatSheaf).IsLocallyFree :=
  sheaf_isLocallyFree_of_freeIso X.ringCatSheaf _ _ (coordinateModuleSheafFree X ι).symm

end
end PfaffianDescent

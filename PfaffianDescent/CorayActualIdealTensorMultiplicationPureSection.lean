import PfaffianDescent.CorayActualIdealModuleTensorProductMultiplication
import PfaffianDescent.SheafModuleCanonicalTensorPureSections
import PfaffianDescent.NativeOriginalTensorSectionFrames
import PfaffianDescent.ClosedImmersionIdealModuleAffineFree
import PfaffianDescent.VoisinPositiveTwistTriviality

/-! SOURCE ONLY / UNVERIFIED. Original own chart frames and GLOBAL IsIso for
actual Cartier ideal-power multiplication. Production global multiplication10roots
and native tensor frames10roots are imported. Own chart011 and pure-section
prerequisites and ALL new IsIso tails remain unverified. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MonoidalCategory
open IdealSheafDataModule
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}

/-- The multiplication used in the ORIGINAL unchanged pure-section header:
it is literally the native coefficient-ring Mul, exposed on its SAME unit carrier.
Only Mul is exposed here; the original additive/module/scalar actions are unchanged. -/
local instance nativeOriginalUnitRingMul (U : X.Opensᵒᵖ) :
    Mul ((SheafOfModules.unit X.ringCatSheaf).val.obj U) :=
  inferInstanceAs (Mul (X.presheaf.obj U))

private theorem nativeOriginalUnitRingMul_value (U : X.Opensᵒᵖ)
    (a b : (SheafOfModules.unit X.ringCatSheaf).val.obj U) :
    @Mul.mul ((SheafOfModules.unit X.ringCatSheaf).val.obj U)
        (nativeOriginalUnitRingMul U) a b =
      @Mul.mul (X.presheaf.obj U) (inferInstance : Mul (X.presheaf.obj U)) a b := rfl

private theorem nativeRingRegularAction_comm (R : CommRingCat) (a b : R) :
    a • b = @Mul.mul R (inferInstance : Mul R) b a :=
  mul_comm a b

/-- The GLOBAL multiplication map takes each genuine sheafified pure
section to an ideal section whose inclusion is the literal product of
its two ORIGINAL ideal coefficients. No tensor/sheaf comparison is input. -/
theorem actualIdealModuleTensorMul_pureSection_value
    (I J : X.IdealSheafData) (U : X.Opensᵒᵖ)
    (m : (idealModule I).val.obj U) (n : (idealModule J).val.obj U) :
    (idealModuleToUnit (I * J)).val.app U
        ((actualIdealModuleTensorMul I J).val.app U
          (SheafOfModules.commRingSheafTensorPureSection X.sheaf
            (idealModule I) (idealModule J) U m n)) =
      (idealModuleToUnit I).val.app U m * (idealModuleToUnit J).val.app U n := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let c := SheafOfModules.commRingSheafTensorPureSection X.sheaf
    (idealModule I) (idealModule J) U m n
  have h := congrArg
    (fun k : schemeModuleTensor (idealModule I) (idealModule J) ⟶ O => k.val.app U c)
    (actualIdealModuleTensorMul_toUnit I J)
  have ht := SheafOfModules.commRingSheafTensorPureSection_map X.sheaf
    (idealModuleToUnit I) (idealModuleToUnit J) U m n
  have hmap := congrArg
    (fun s : (schemeModuleTensor O O).val.obj U =>
      (schemeModuleTensorUnitRightIso O).hom.val.app U s) ht
  have hu := SheafOfModules.commRingSheafTensorUnitRightIso_pureSection X.sheaf O U
    ((idealModuleToUnit I).val.app U m) ((idealModuleToUnit J).val.app U n)
  exact h.trans (hmap.trans (hu.trans
    (nativeRingRegularAction_comm (X.presheaf.obj U)
      ((idealModuleToUnit J).val.app U n) ((idealModuleToUnit I).val.app U m))))

end PfaffianDescent.Coray

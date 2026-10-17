import PfaffianDescent.SchemeModuleTensorStalkPureGerms

/-! Zero laws for the SAME actual tensor-sheaf pure-germ pairing.
The actual sheafification-unit linear component sends a zero pure tensor
to zero; the accepted germ law then descends both laws to actual stalks.
No stalk tensor comparison, bilinearity or pure-kernel premise is used.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensorPureSection_zero_left
    (M N : X.Modules) (U : X.Opens) (n : N.val.obj (op U)) :
    SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U)
        (0 : M.val.obj (op U)) n = 0 := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M.val N.val
  change ((A.unit.app T).app (op U)).hom
      ((0 : M.val.obj (op U)) ⊗ₜ[X.sheaf.obj.obj (op U)] n) = 0
  exact (congrArg ((A.unit.app T).app (op U)).hom
    (TensorProduct.zero_tmul (R := X.sheaf.obj.obj (op U)) (M.val.obj (op U)) n)).trans
      (((A.unit.app T).app (op U)).hom.map_zero)

private theorem tensorPureSection_zero_right
    (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) :
    SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U)
        m (0 : N.val.obj (op U)) = 0 := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M.val N.val
  change ((A.unit.app T).app (op U)).hom
      (m ⊗ₜ[X.sheaf.obj.obj (op U)] (0 : N.val.obj (op U))) = 0
  exact (congrArg ((A.unit.app T).app (op U)).hom
    (TensorProduct.tmul_zero (R := X.sheaf.obj.obj (op U)) (N.val.obj (op U)) m)).trans
      (((A.unit.app T).app (op U)).hom.map_zero)

/-- Zero in the original left additive stalk gives zero under the
actual pure-germ pairing, for every actual right stalk value. -/
theorem schemeModuleTensorStalkPureGerm_zero_left
    (M N : X.Modules) (x : X) (b : N.presheaf.stalk x) :
    schemeModuleTensorStalkPureGerm M N x 0 b = 0 := by
  obtain ⟨U, hxU, n, hn⟩ := N.presheaf.exists_germ_eq b
  have hzero : M.presheaf.germ U x hxU (0 : M.val.obj (op U)) = 0 :=
    (M.presheaf.germ U x hxU).hom.map_zero
  exact (congrArg₂ (schemeModuleTensorStalkPureGerm M N x) hzero.symm hn.symm).trans
    ((schemeModuleTensorStalkPureGerm_germ M N x U hxU 0 n).trans
      ((congrArg ((schemeModuleTensor M N).presheaf.germ U x hxU)
        (tensorPureSection_zero_left M N U n)).trans
          (((schemeModuleTensor M N).presheaf.germ U x hxU).hom.map_zero)))

/-- Zero in the original right additive stalk gives zero under the
actual pure-germ pairing, for every actual left stalk value. -/
theorem schemeModuleTensorStalkPureGerm_zero_right
    (M N : X.Modules) (x : X) (a : M.presheaf.stalk x) :
    schemeModuleTensorStalkPureGerm M N x a 0 = 0 := by
  obtain ⟨U, hxU, m, hm⟩ := M.presheaf.exists_germ_eq a
  have hzero : N.presheaf.germ U x hxU (0 : N.val.obj (op U)) = 0 :=
    (N.presheaf.germ U x hxU).hom.map_zero
  exact (congrArg₂ (schemeModuleTensorStalkPureGerm M N x) hm.symm hzero.symm).trans
    ((schemeModuleTensorStalkPureGerm_germ M N x U hxU m 0).trans
      ((congrArg ((schemeModuleTensor M N).presheaf.germ U x hxU)
        (tensorPureSection_zero_right M N U m)).trans
          (((schemeModuleTensor M N).presheaf.germ U x hxU).hom.map_zero)))

end PfaffianDescent

import PfaffianDescent.SchemeModuleFixedFrameStalkInjectiveOfLocallyRankOne
import PfaffianDescent.SchemeModuleFixedFrameTensorStalkFieldMultiplication
import PfaffianDescent.SchemeModuleTensorStalkPureGermZero

/-! Injectivity of the SAME actual tensor fixed-frame stalk map.
Genuine local rank-one geometry derives factor injection and original
pure-germ generation. The checked multiplication law and actual zero
laws then detect the tensor kernel, without a pure-kernel certificate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original fixed-frame map of the actual tensor stalk is injective
at every point. Both factor injections are proved from genuine local
rank-one charts; pure-germ generation and multiplication are the SAME
accepted constructions, and their zero laws are derived from actual pure
sections. No tensor-injection, generation or pure-kernel premise is used. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_tensor_injective_of_locallyRankOne
    (pi : X ⟶ Spec (CommRingCat.of K)) (M N : X.Modules)
    (hM : schemeModuleLocallyRankOne M) (hN : schemeModuleLocallyRankOne N)
    (C : X.Opens) [Nonempty C]
    (eM : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (eN : N.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X) :
    letI := schemeModuleStalkModule M x
    letI := schemeModuleStalkModule N x
    letI := schemeModuleStalkModule (schemeModuleTensor M N) x
    Function.Injective (schemeModuleFixedFrameStalkToFunctionFieldLinearMap
      pi (schemeModuleTensor M N) C (schemeModuleTensorOverUnitIso M N C eM eN) x) := by
  letI := schemeModuleStalkModule M x
  letI := schemeModuleStalkModule N x
  letI := schemeModuleStalkModule (schemeModuleTensor M N) x
  let T := schemeModuleTensor M N
  let ψT := schemeModuleFixedFrameStalkToFunctionFieldLinearMap
    pi T C (schemeModuleTensorOverUnitIso M N C eM eN) x
  let ψM := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C eM x
  let ψN := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi N C eN x
  have hiM : Function.Injective ψM :=
    schemeModuleFixedFrameStalkToFunctionFieldLinearMap_injective_of_locallyRankOne pi M hM C eM x
  have hiN : Function.Injective ψN :=
    schemeModuleFixedFrameStalkToFunctionFieldLinearMap_injective_of_locallyRankOne pi N hN C eN x
  change Function.Injective ψT
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨p, hp⟩ := schemeModuleTensorStalkPureGerm_surjective_of_locallyRankOne M N hM hN x t
  have hprod : @HMul.hMul X.functionField X.functionField X.functionField inferInstance
      (ψM p.1) (ψN p.2) = 0 :=
    (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_tensorPureGerm
      pi M N C eM eN x p.1 p.2).symm.trans ((congrArg ψT hp).trans ht)
  rcases mul_eq_zero.mp hprod with hleft | hright
  · have hzero : p.1 = 0 := hiM (hleft.trans ψM.map_zero.symm)
    exact hp.symm.trans
      ((congrArg (fun a => schemeModuleTensorStalkPureGerm M N x a p.2) hzero).trans
        (schemeModuleTensorStalkPureGerm_zero_left M N x p.2))
  · have hzero : p.2 = 0 := hiN (hright.trans ψN.map_zero.symm)
    exact hp.symm.trans
      ((congrArg (fun b => schemeModuleTensorStalkPureGerm M N x p.1 b) hzero).trans
        (schemeModuleTensorStalkPureGerm_zero_right M N x p.1))

end PfaffianDescent

import PfaffianDescent.SchemeModuleFixedFrameStalkFunctionField
import PfaffianDescent.SchemeModuleTensorStalkPureGerms

/-! Literal tensor multiplication after actual fixed-frame stalk descent.
The existing pure-germ pairing, the actual over-site tensor chart and
original-pi field actions are retained. Rank-one geometry derives full
range multiplication; no multiplicativity or image certificate is input.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensorChart_subopen_pureSection
    (M N : X.Modules) (C : X.Opens)
    (eM : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (eN : N.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    {W : X.Opens} (f : W ⟶ C)
    (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    ((schemeModuleTensorOverUnitIso M N C eM eN).hom.val.app (op (Over.mk f))
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op W) m n) : Γ(X, W)) =
      @HMul.hMul (Γ(X, W)) (Γ(X, W)) (Γ(X, W)) inferInstance
        (eM.hom.val.app (op (Over.mk f)) m) (eN.hom.val.app (op (Over.mk f)) n) := by
  let V := op (Over.mk f)
  change (SheafOfModules.commRingSheafTensorCanonicalUnitIso
      (SheafOfModules.commRingSheafOver X.sheaf C) eM eN).hom.val.app V
      ((schemeModuleTensorOverIso C M N).hom.val.app V
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op W) m n)) = _
  exact (congrArg (fun s => (SheafOfModules.commRingSheafTensorCanonicalUnitIso
    (SheafOfModules.commRingSheafOver X.sheaf C) eM eN).hom.val.app V s)
      (schemeModuleTensorOverIso_pureSection C M N V m n)).trans
        (SheafOfModules.commRingSheafTensorCanonicalUnitIso_pureSection
          (SheafOfModules.commRingSheafOver X.sheaf C) eM eN V m n)

variable {K : Type u} [Field K] [IsIntegral X]

private theorem generic_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

/-- SAME original local maps multiply on the actual sheafification-unit
pure section after restricting to the SAME common fixed complement. -/
theorem schemeModuleFixedFrameOpenToFunctionFieldLinearMap_tensorPureSection
    (pi : X ⟶ Spec (CommRingCat.of K)) (M N : X.Modules)
    (C : X.Opens) [Nonempty C]
    (eM : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (eN : N.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (U : X.Opens) [Nonempty U]
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi (schemeModuleTensor M N) C
        (schemeModuleTensorOverUnitIso M N C eM eN) U
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n) :
          X.functionField) =
      @HMul.hMul X.functionField X.functionField X.functionField inferInstance
        (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C eM U m)
        (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi N C eN U n) := by
  let W := U ⊓ C
  letI : Nonempty W := ⟨⟨genericPoint X, generic_mem U, generic_mem C⟩⟩
  let r : W ⟶ U := homOfLE inf_le_left
  let f : W ⟶ C := homOfLE inf_le_right
  let eT := schemeModuleTensorOverUnitIso M N C eM eN
  let T := schemeModuleTensor M N
  have hres := SheafOfModules.commRingSheafTensorPureSection_restrict
    X.sheaf M N r.op m n
  have hcoeff := tensorChart_subopen_pureSection M N C eM eN f
    (M.val.map r.op m) (N.val.map r.op n)
  exact (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi T C eT U _).trans
    ((congrArg (fun t => X.germToFunctionField W (eT.hom.val.app (op (Over.mk f)) t)) hres).trans
      ((congrArg (X.germToFunctionField W) hcoeff).trans
        (((X.germToFunctionField W).hom.map_mul _ _).trans
          (congrArg₂ (fun a b : X.functionField => a * b)
            (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M C eM U m).symm
            (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi N C eN U n).symm))))

/-- Every pair of ACTUAL original stalk values multiplies in the SAME
function field under canonical product charts. Common representatives and
the accepted canonical pure-germ law derive this identity internally. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_tensorPureGerm
    (pi : X ⟶ Spec (CommRingCat.of K)) (M N : X.Modules)
    (C : X.Opens) [Nonempty C]
    (eM : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (eN : N.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X) :
    letI := schemeModuleStalkModule M x
    letI := schemeModuleStalkModule N x
    letI := schemeModuleStalkModule (schemeModuleTensor M N) x
    ∀ (a : M.presheaf.stalk x) (b : N.presheaf.stalk x),
      schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi (schemeModuleTensor M N) C
          (schemeModuleTensorOverUnitIso M N C eM eN) x
          (schemeModuleTensorStalkPureGerm M N x a b) =
        @HMul.hMul X.functionField X.functionField X.functionField inferInstance
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C eM x a)
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi N C eN x b) := by
  letI := schemeModuleStalkModule M x
  letI := schemeModuleStalkModule N x
  letI := schemeModuleStalkModule (schemeModuleTensor M N) x
  intro a b
  obtain ⟨U, hxU, m, hm⟩ := M.presheaf.exists_germ_eq a
  obtain ⟨V, hVU, hxV, n, hn⟩ := N.presheaf.exists_le_germ_eq b hxU
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let mV : M.val.obj (op V) := M.val.map (homOfLE hVU).op m
  have hmV : M.presheaf.germ V x hxV mV = a :=
    (M.presheaf.germ_res_apply (homOfLE hVU) x hxV m).trans hm
  let T := schemeModuleTensor M N
  let eT := schemeModuleTensorOverUnitIso M N C eM eN
  let ψT := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi T C eT x
  let ψM := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C eM x
  let ψN := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi N C eN x
  have hp : schemeModuleTensorStalkPureGerm M N x a b =
      T.presheaf.germ V x hxV
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op V) mV n) :=
    (congrArg₂ (schemeModuleTensorStalkPureGerm M N x) hmV.symm hn.symm).trans
      (schemeModuleTensorStalkPureGerm_germ M N x V hxV mV n)
  have hM : ψM a = schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C eM V mV :=
    (congrArg ψM hmV.symm).trans
      (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C eM x V hxV mV)
  have hN : ψN b = schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi N C eN V n :=
    (congrArg ψN hn.symm).trans
      (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi N C eN x V hxV n)
  exact (congrArg ψT hp).trans
    ((schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi T C eT x V hxV _).trans
      ((schemeModuleFixedFrameOpenToFunctionFieldLinearMap_tensorPureSection
        pi M N C eM eN V mV n).trans
          (congrArg₂ (fun r s : X.functionField => r * s) hM.symm hN.symm)))

/-- FULL actual tensor-stalk image is the product of the two actual
factor images in rank one. Pure-germ surjectivity is derived from genuine
unit charts by the accepted producer; an image premise is never supplied. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_range_tensor_product
    (pi : X ⟶ Spec (CommRingCat.of K)) (M N : X.Modules)
    (hM : schemeModuleLocallyRankOne M) (hN : schemeModuleLocallyRankOne N)
    (C : X.Opens) [Nonempty C]
    (eM : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (eN : N.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X) :
    letI := schemeModuleStalkModule M x
    letI := schemeModuleStalkModule N x
    letI := schemeModuleStalkModule (schemeModuleTensor M N) x
    Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap
        pi (schemeModuleTensor M N) C (schemeModuleTensorOverUnitIso M N C eM eN) x) =
      Set.range (fun p : M.presheaf.stalk x × N.presheaf.stalk x =>
        @HMul.hMul X.functionField X.functionField X.functionField inferInstance
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C eM x p.1)
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi N C eN x p.2)) := by
  letI := schemeModuleStalkModule M x
  letI := schemeModuleStalkModule N x
  letI := schemeModuleStalkModule (schemeModuleTensor M N) x
  let T := schemeModuleTensor M N
  let ψT := schemeModuleFixedFrameStalkToFunctionFieldLinearMap
    pi T C (schemeModuleTensorOverUnitIso M N C eM eN) x
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht⟩
    obtain ⟨p, hp⟩ := schemeModuleTensorStalkPureGerm_surjective_of_locallyRankOne M N hM hN x t
    refine ⟨p, ?_⟩
    exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_tensorPureGerm
      pi M N C eM eN x p.1 p.2).symm.trans ((congrArg ψT hp).trans ht)
  · rintro z ⟨p, hp⟩
    refine ⟨schemeModuleTensorStalkPureGerm M N x p.1 p.2, ?_⟩
    exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_tensorPureGerm
      pi M N C eM eN x p.1 p.2).trans hp

end PfaffianDescent

import PfaffianDescent.SchemeModuleFixedFrameStalkFunctionField

/-! Injectivity of the ORIGINAL fixed-frame stalk map at every point.
Actual unit charts, original integral ring restrictions and original
generic germs detect a zero local representative, including away from C.
No factor injection or rational-comparison certificate is assumed.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem generic_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

private theorem restrictedChart_coefficient
    (M : X.Modules) (C : X.Opens)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    {U : X.Opens} (f : U ⟶ C) (a : M.val.obj (op U)) :
    SchemeModuleInternalHom.overTopLinearEquiv M U
        (SchemeModuleInternalHom.overUnitChartRestrict M f e) a =
      (e.hom.val.app (op (Over.mk f)) a : Γ(X, U)) := rfl

private theorem chartRestriction_injective
    (M : X.Modules) (U : X.Opens)
    (eU : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (W : X.Opens) [Nonempty W] (f : W ⟶ U) :
    Function.Injective (M.val.map f.op) := by
  intro m n hmn
  let qU := SchemeModuleInternalHom.overTopLinearEquiv M U eU
  let k : Over.mk f ⟶ Over.mk (𝟙 U) := Over.homMk f
  have hnat (s : M.val.obj (op U)) :
      X.presheaf.map f.op (qU s) =
        eU.hom.val.app (op (Over.mk f)) (M.val.map f.op s) :=
    (PresheafOfModules.naturality_apply eU.hom.val k.op s).symm
  apply qU.injective
  apply map_injective_of_isIntegral X f
  exact (hnat m).trans
    ((congrArg (eU.hom.val.app (op (Over.mk f))) hmn).trans (hnat n).symm)

private theorem fixedFrameOpen_injective_of_chart
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (eC : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (U : X.Opens) [Nonempty U]
    (eU : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    Function.Injective (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C eC U) := by
  intro m n hmn
  let W : X.Opens := U ⊓ C
  letI : Nonempty W := ⟨⟨genericPoint X, generic_mem U, generic_mem C⟩⟩
  let r : W ⟶ U := homOfLE inf_le_left
  let f : W ⟶ C := homOfLE inf_le_right
  let qW := SchemeModuleInternalHom.overTopLinearEquiv M W
    (SchemeModuleInternalHom.overUnitChartRestrict M f eC)
  have hval (s : M.val.obj (op U)) :
      (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C eC U s : X.functionField) =
        X.germToFunctionField W (qW (M.val.map r.op s)) :=
    (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M C eC U s).trans
      (congrArg (X.germToFunctionField W)
        (restrictedChart_coefficient M C eC f (M.val.map r.op s)).symm)
  have hq : qW (M.val.map r.op m) = qW (M.val.map r.op n) :=
    (X.germToFunctionField_injective W) ((hval m).symm.trans (hmn.trans (hval n)))
  exact chartRestriction_injective M U eU W r (qW.injective hq)

/-- The SAME original fixed-frame stalk map is injective at EVERY point
for an actual locally rank-one sheaf. A point need not lie in C. Genuine
local unit charts internally discharge all section and factor injections. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_injective_of_locallyRankOne
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M)
    (C : X.Opens) [Nonempty C]
    (eC : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X) :
    letI := schemeModuleStalkModule M x
    Function.Injective (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C eC x) := by
  letI := schemeModuleStalkModule M x
  let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C eC x
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨V, hxV, ⟨eV⟩⟩ := hM x
  obtain ⟨U, hUV, hxU, m, hm⟩ := M.presheaf.exists_le_germ_eq a hxV
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  let eU := SchemeModuleInternalHom.overUnitChartRestrict M (homOfLE hUV) eV
  have hzero : (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C eC U m :
      X.functionField) = 0 :=
    (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C eC x U hxU m).symm.trans
      ((congrArg ψ hm).trans ha)
  have hmzero : m = 0 := fixedFrameOpen_injective_of_chart pi M C eC U eU
    (hzero.trans (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C eC U).map_zero.symm)
  exact hm.symm.trans ((congrArg (M.presheaf.germ U x hxU) hmzero).trans
    (M.presheaf.germ U x hxU).hom.map_zero)

end PfaffianDescent

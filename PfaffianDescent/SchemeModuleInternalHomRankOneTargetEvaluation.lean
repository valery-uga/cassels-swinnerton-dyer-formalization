import PfaffianDescent.SchemeModuleInternalHomRankOneTargetChart
import PfaffianDescent.CorayCartierPullbackIntrinsicDual
import PfaffianDescent.SchemeModuleRankOneDualKernelIso

/-! SAME evaluation and native tensor/Hom comparison for rank-one sources,
with arbitrary original target. SOURCE ONLY / UNVERIFIED. No global duality. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Arbitrary-target GLOBAL evaluation is invertible from source charts;
all raw bijectivity and sheafification comparisons are derived internally. -/
theorem evaluation_isIso_of_pointwise_unitCharts
    (U : X → X.Opens) (hU : ∀ x, x ∈ U x)
    (e : ∀ x, M.over (U x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (U x)) :
    IsIso (evaluation M N) := by
  let I : Type u := {V : X.Opens // ∃ x : X, V ≤ U x}
  let B : I → X.Opens := Subtype.val
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hxW
    exact ⟨W ⊓ U x, ⟨⟨W ⊓ U x, x, inf_le_right⟩, rfl⟩,
      ⟨hxW, hU x⟩, inf_le_left⟩
  have hraw : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (evaluationPresheaf M N)) := by
    apply moduleSheafification_map_isIso_of_basiswise_bijective
      (evaluationPresheaf M N) B hB
    intro V
    obtain ⟨x, hVU⟩ := V.2
    let eV := overUnitChartRestrict M (homOfLE hVU) (e x)
    letI : IsIso ((evaluationPresheaf M N).app (op V.1)) :=
      targetEvaluationPresheaf_app_isIso M N V.1 eV
    exact ConcreteCategory.bijective_of_isIso ((evaluationPresheaf M N).app (op V.1))
  have hcounit : IsIso
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app N) :=
    NatIso.isIso_app_of_isIso
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit N
  exact (evaluation_eq_sheafification_counit M N).symm ▸
    IsIso.comp_isIso' hraw hcounit

/-- Actual local rank-one geometry of the source suffices for evaluation. -/
theorem evaluation_isIso_of_locallyRankOne (hM : schemeModuleLocallyRankOne M) :
    IsIso (evaluation M N) := by
  obtain ⟨U, hU, ⟨eU⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  exact evaluation_isIso_of_pointwise_unitCharts M N U hU eU

/-- An actual invertible pairing with a rank-one source yields the actual
intrinsic Hom, without a target frame or supplied evaluation compatibility. -/
theorem tensorCurry_isIso_of_locallyRankOne
    (B : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (p : schemeModuleTensor M B ⟶ N) [IsIso p] :
    IsIso (tensorCurry M B N p) := by
  let g := tensorCurry M B N p
  let hEval : IsIso (evaluation M N) := evaluation_isIso_of_locallyRankOne M N hM
  have h : schemeModuleTensorMap (𝟙 M) g ≫ evaluation M N = p :=
    tensorCurry_evaluation M B N p
  let hComp : IsIso (schemeModuleTensorMap (𝟙 M) g ≫ evaluation M N) :=
    h.symm ▸ (inferInstance : IsIso p)
  let hTensor : IsIso (schemeModuleTensorMap (𝟙 M) g) :=
    @IsIso.of_isIso_comp_right X.Modules (inferInstance : Category X.Modules)
      _ _ _ (schemeModuleTensorMap (𝟙 M) g) (evaluation M N) hEval hComp
  exact @schemeModuleTensorMap_right_isIso_of_locallyRankOne_left X M hM
    B (sheaf M N) g hTensor

/-- The tensor-Hom Iso is the curry of the SAME original contraction. -/
def rankOneTensorHomIso (hM : schemeModuleLocallyRankOne M) :
    schemeModuleTensor N (dual M) ≅ sheaf M N := by
  let p := schemeModuleRankOneDualKernelMap M N hM
  let hp : IsIso p := schemeModuleRankOneDualKernelMap_isIso M N hM
  let hg : IsIso (tensorCurry M (schemeModuleTensor N (dual M)) N p) :=
    @tensorCurry_isIso_of_locallyRankOne X M N
      (schemeModuleTensor N (dual M)) hM p hp
  exact @asIso X.Modules (inferInstance : Category X.Modules) _ _
    (tensorCurry M (schemeModuleTensor N (dual M)) N p) hg

/-- Exact original evaluation square of the constructed Hom comparison. -/
theorem rankOneTensorHomIso_evaluation (hM : schemeModuleLocallyRankOne M) :
    schemeModuleTensorMap (𝟙 M) (rankOneTensorHomIso M N hM).hom ≫ evaluation M N =
      schemeModuleRankOneDualKernelMap M N hM := by
  exact tensorCurry_evaluation M (schemeModuleTensor N (dual M)) N
    (schemeModuleRankOneDualKernelMap M N hM)

end PfaffianDescent.SchemeModuleInternalHom
end

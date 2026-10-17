import PfaffianDescent.CorayCartierPullbackRankOne
import PfaffianDescent.CubicClosedPointSerreTensorStalkUnitIso

/-!
The SAME native tensor comparison on a genuine unit-framed factor,
and a literal pulled-back dual pairing with its ordinary evaluation square.
This is a chart-level prerequisite; it does not assert that arbitrary
local frames glue to the intrinsic dual comparison.
SOURCE ONLY / UNVERIFIED. Root owns compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- A genuine unit frame reduces the actual pullback tensor map to its
proved unit case by actual naturality. No IsIso conclusion is input. -/
theorem schemeModulePullbackTensorMap_isIso_of_unitFrame
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N) := by
  let P := Scheme.Modules.pullback f
  let a := P.map (schemeModuleTensorMap (𝟙 M) eN.hom)
  let b := schemeModuleTensorMap (P.map (𝟙 M)) (P.map eN.hom)
  let c := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N
  let cO := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
    (SheafOfModules.unit X.ringCatSheaf)
  letI : IsIso (schemeModuleTensorMap (𝟙 M) eN.hom) := by
    change IsIso (schemeModuleTensorMapIso (Iso.refl M) eN).hom
    infer_instance
  letI : IsIso a := by
    dsimp only [a]
    infer_instance
  letI : IsIso b := by
    change IsIso (schemeModuleTensorMap (P.map (𝟙 M)) (P.map eN.hom))
    rw [P.map_id]
    change IsIso (schemeModuleTensorMapIso (Iso.refl (P.obj M)) (P.mapIso eN)).hom
    infer_instance
  letI : IsIso cO := cubicClosedPointSerreTensorStalk_pullbackTensorMap_unit_isIso f M
  have hn : a ≫ cO = c ≫ b :=
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_naturality f (𝟙 M) eN.hom
  letI : IsIso (c ≫ b) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right c b

/-- An ordinary Iso with the SAME native tensor-comparison hom. -/
def schemeModulePullbackTensorIsoOfUnitFrame
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback f).obj (schemeModuleTensor M N) ≅
      schemeModuleTensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) := by
  letI := schemeModulePullbackTensorMap_isIso_of_unitFrame f M N eN
  exact asIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N)

/-- Construct the actual pulled-back dual pairing on a genuine unit
chart of the dual; use the inverse of the SAME tensor comparison, not a
replacement module or a supplied evaluation-compatibility certificate. -/
def schemeModulePullbackDualEvaluationOfUnitFrame
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (eD : SchemeModuleInternalHom.dual M ≅ SheafOfModules.unit X.ringCatSheaf) :
    schemeModuleTensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj (SchemeModuleInternalHom.dual M)) ⟶
      SheafOfModules.unit Y.ringCatSheaf :=
  (schemeModulePullbackTensorIsoOfUnitFrame f M (SchemeModuleInternalHom.dual M) eD).inv ≫
    (Scheme.Modules.pullback f).map (SchemeModuleInternalHom.dualEvaluation M) ≫
    BundleSectionZeroLocus.pullbackUnitComparison f

/-- The constructed pairing is compatible with the literal original
evaluation through the actual native tensor comparison. -/
theorem schemeModulePullbackDualEvaluationOfUnitFrame_tensor_square
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (eD : SchemeModuleInternalHom.dual M ≅ SheafOfModules.unit X.ringCatSheaf) :
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
        (SchemeModuleInternalHom.dual M) ≫
      schemeModulePullbackDualEvaluationOfUnitFrame f M eD =
    (Scheme.Modules.pullback f).map (SchemeModuleInternalHom.dualEvaluation M) ≫
      BundleSectionZeroLocus.pullbackUnitComparison f := by
  let e := schemeModulePullbackTensorIsoOfUnitFrame f M (SchemeModuleInternalHom.dual M) eD
  change e.hom ≫ (e.inv ≫
      (Scheme.Modules.pullback f).map (SchemeModuleInternalHom.dualEvaluation M) ≫
      BundleSectionZeroLocus.pullbackUnitComparison f) = _
  exact e.hom_inv_id_assoc _

/-- On genuine rank-one geometry the SAME constructed chart pairing is
invertible, internally from the actual original dual evaluation. -/
theorem schemeModulePullbackDualEvaluationOfUnitFrame_isIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M)
    (eD : SchemeModuleInternalHom.dual M ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (schemeModulePullbackDualEvaluationOfUnitFrame f M eD) := by
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  let hEval : IsIso (SchemeModuleInternalHom.dualEvaluation M) :=
    SchemeModuleInternalHom.dualEvaluation_isIso_of_pointwise_unitCharts M B hB eB
  let eEval : schemeModuleTensor M (SchemeModuleInternalHom.dual M) ≅
      SheafOfModules.unit X.ringCatSheaf :=
    @asIso _ _ _ _ (SchemeModuleInternalHom.dualEvaluation M) hEval
  let eUnit : (Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
    @asIso _ _ _ _ (BundleSectionZeroLocus.pullbackUnitComparison f)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison f)
  let eTensor := schemeModulePullbackTensorIsoOfUnitFrame f M
    (SchemeModuleInternalHom.dual M) eD
  let e := eTensor.symm ≪≫ (Scheme.Modules.pullback f).mapIso eEval ≪≫ eUnit
  change IsIso e.hom
  exact e.isIso_hom

end PfaffianDescent
end

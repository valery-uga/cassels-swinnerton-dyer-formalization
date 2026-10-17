import PfaffianDescent.CorayCartierPullbackTensorRankOne
import PfaffianDescent.CorayCartierCanonicalProjectionFormula

/-!
The actual OWN residue quotient as the tensor of the two actual pullbacks,
and genuine evaluation on the actual pulled-back ideal and ideal-dual.
P(dual I) is not silently replaced by dual(P I); intrinsic dual comparison
and dualizing/cohomological adjunction remain separate obligations.
SOURCE ONLY / UNVERIFIED. Root owns compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Native pullback evaluation on an arbitrary rank-one module, with no
global dual frame and no supplied tensor/evaluation compatibility input. -/
def schemeModulePullbackDualEvaluationOfLocallyRankOne
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) :
    schemeModuleTensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj (SchemeModuleInternalHom.dual M)) ⟶
      SheafOfModules.unit Y.ringCatSheaf :=
  (schemeModulePullbackTensorIsoOfLocallyRankOne f M (SchemeModuleInternalHom.dual M)
      (schemeModuleLocallyRankOne_dual M hM)).inv ≫
    (Scheme.Modules.pullback f).map (SchemeModuleInternalHom.dualEvaluation M) ≫
    BundleSectionZeroLocus.pullbackUnitComparison f

/-- The actual constructed pairing preserves the literal original
canonical evaluation through the SAME native tensor comparison. -/
theorem schemeModulePullbackDualEvaluationOfLocallyRankOne_tensor_square
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) :
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
        (SchemeModuleInternalHom.dual M) ≫
      schemeModulePullbackDualEvaluationOfLocallyRankOne f M hM =
    (Scheme.Modules.pullback f).map (SchemeModuleInternalHom.dualEvaluation M) ≫
      BundleSectionZeroLocus.pullbackUnitComparison f := by
  let e := schemeModulePullbackTensorIsoOfLocallyRankOne f M (SchemeModuleInternalHom.dual M)
    (schemeModuleLocallyRankOne_dual M hM)
  change e.hom ≫ (e.inv ≫
      (Scheme.Modules.pullback f).map (SchemeModuleInternalHom.dualEvaluation M) ≫
      BundleSectionZeroLocus.pullbackUnitComparison f) = _
  exact e.hom_inv_id_assoc _

/-- Invertibility follows from the actual rank-one dual evaluation and
the genuine tensor comparison, not from a perfect-pairing hypothesis. -/
theorem schemeModulePullbackDualEvaluationOfLocallyRankOne_isIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) :
    IsIso (schemeModulePullbackDualEvaluationOfLocallyRankOne f M hM) := by
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  letI : IsIso (SchemeModuleInternalHom.dualEvaluation M) :=
    SchemeModuleInternalHom.dualEvaluation_isIso_of_pointwise_unitCharts M B hB eB
  letI : IsIso ((Scheme.Modules.pullback f).map
      (SchemeModuleInternalHom.dualEvaluation M)) :=
    ((Scheme.Modules.pullback f).mapIso
      (asIso (SchemeModuleInternalHom.dualEvaluation M))).isIso_hom
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison f) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  let eTensor := schemeModulePullbackTensorIsoOfLocallyRankOne f M
    (SchemeModuleInternalHom.dual M) (schemeModuleLocallyRankOne_dual M hM)
  let eEval := asIso (SchemeModuleInternalHom.dualEvaluation M)
  let eUnit := asIso (BundleSectionZeroLocus.pullbackUnitComparison f)
  let e := eTensor.symm ≪≫ ((Scheme.Modules.pullback f).mapIso eEval ≪≫ eUnit)
  change IsIso e.hom
  exact e.isIso_hom

/-- The literal OWN residue quotient is the pushforward of the tensor
of its actual two pullback factors. The own ideal-dual's geometry is
internally derived from the genuine regular-principal immersion. -/
def RegularPrincipalImmersion.actualCartierResidueRestrictedTensorIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    (H.actualCartierResidueSequence W).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
          ((Scheme.Modules.pullback i).obj
            (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)))) :=
  H.actualCartierResidueProjectionIso W hW ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (schemeModulePullbackTensorIsoOfLocallyRankOne i W
        (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i))
        (schemeModuleLocallyRankOne_dual _ H.inverseCartierTwist_locallyRankOne))

/-- The actual quotient comparison has exactly the original canonical
projection followed by pushforward of the original native tensor map. -/
theorem RegularPrincipalImmersion.actualCartierResidueRestrictedTensorIso_hom
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    (H.actualCartierResidueRestrictedTensorIso W hW).hom =
      (H.actualCartierResidueProjectionIso W hW).hom ≫
        (Scheme.Modules.pushforward i).map
          (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i W
            (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i))) := rfl

end PfaffianDescent
end

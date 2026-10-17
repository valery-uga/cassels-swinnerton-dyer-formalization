import PfaffianDescent.SchemeModuleInternalHomTensorCurry
import PfaffianDescent.CorayOwnCartierResidueTensorEvaluation

/-! The actual pullback of the original ideal-dual agrees with the
intrinsic dual of the actual pulled-back ideal. SOURCE ONLY / UNVERIFIED.
No desired dual/evaluation compatibility is input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- A genuine rank-one left factor reflects invertibility of a tensor
map, by actual symmetry and the native local restriction natural Iso. -/
theorem schemeModuleTensorMap_right_isIso_of_locallyRankOne_left
    {X : Scheme.{u}} (A : X.Modules) (hA : schemeModuleLocallyRankOne A)
    {B C : X.Modules} (g : B ⟶ C)
    [IsIso (schemeModuleTensorMap (𝟙 A) g)] : IsIso g := by
  have hs := schemeModuleTensorSymmetry_naturality (𝟙 A) g
  let sB := schemeModuleTensorSymmetry A B
  let sC := schemeModuleTensorSymmetry A C
  letI : IsIso sB.hom := sB.isIso_hom
  letI : IsIso sC.hom := sC.isIso_hom
  letI : IsIso (sB.hom ≫ schemeModuleTensorMap g (𝟙 A)) := by
    rw [← hs]
    infer_instance
  letI : IsIso (schemeModuleTensorMap g (𝟙 A)) :=
    IsIso.of_isIso_comp_left sB.hom (schemeModuleTensorMap g (𝟙 A))
  apply schemeModuleMap_isIso_of_stalk
  intro x
  obtain ⟨U, hx, ⟨eA⟩⟩ := hA x
  let R := Scheme.Modules.restrictFunctor U.ι
  let n := schemeModuleTensorRestrictNatIsoOfLocalTrivialization U A eA
  letI : IsIso (R.map (schemeModuleTensorMap g (𝟙 A))) :=
    (R.mapIso (asIso (schemeModuleTensorMap g (𝟙 A)))).isIso_hom
  letI : IsIso (n.app B).hom := (n.app B).isIso_hom
  letI : IsIso (n.app C).hom := (n.app C).isIso_hom
  have hn := n.hom.naturality g
  change R.map (schemeModuleTensorMap g (𝟙 A)) ≫ (n.app C).hom =
    (n.app B).hom ≫ R.map g at hn
  letI : IsIso ((n.app B).hom ≫ R.map g) := by
    have hcomp : IsIso (R.map (schemeModuleTensorMap g (𝟙 A)) ≫ (n.app C).hom) :=
      (R.mapIso (asIso (schemeModuleTensorMap g (𝟙 A))) ≪≫ n.app C).isIso_hom
    exact hn ▸ hcomp
  letI : IsIso (R.map g) := IsIso.of_isIso_comp_left (n.app B).hom (R.map g)
  exact cubicClosedPointSerreTensorStalk_map_isIso_of_restrict U ⟨x, hx⟩ g

/-- An actual invertible pairing with a rank-one module induces an
invertible map to its constructed intrinsic dual. -/
theorem SchemeModuleInternalHom.tensorCurry_dual_isIso_of_locallyRankOne
    {X : Scheme.{u}} (M B : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (p : schemeModuleTensor M B ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso p] :
    IsIso (SchemeModuleInternalHom.tensorCurry M B
      (SheafOfModules.unit X.ringCatSheaf) p) := by
  obtain ⟨U, hU, ⟨eU⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  let hEval : IsIso (SchemeModuleInternalHom.dualEvaluation M) :=
    SchemeModuleInternalHom.dualEvaluation_isIso_of_pointwise_unitCharts M U hU eU
  let g := SchemeModuleInternalHom.tensorCurry M B
    (SheafOfModules.unit X.ringCatSheaf) p
  have h : schemeModuleTensorMap (𝟙 M) g ≫
      SchemeModuleInternalHom.dualEvaluation M = p :=
    SchemeModuleInternalHom.tensorCurry_evaluation M B
      (SheafOfModules.unit X.ringCatSheaf) p
  let hComp : IsIso (schemeModuleTensorMap (𝟙 M) g ≫
      SchemeModuleInternalHom.dualEvaluation M) :=
    h.symm ▸ (inferInstance : IsIso p)
  let hTensor : IsIso (schemeModuleTensorMap (𝟙 M) g) :=
    @IsIso.of_isIso_comp_right X.Modules (inferInstance : Category X.Modules)
      _ _ _ (schemeModuleTensorMap (𝟙 M) g)
      (SchemeModuleInternalHom.dualEvaluation M) hEval hComp
  exact @schemeModuleTensorMap_right_isIso_of_locallyRankOne_left X M hM
    B (SchemeModuleInternalHom.dual M) g hTensor

/-- The forward map is the native curry of the constructed pullback
evaluation, retaining every original O-action. -/
def schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) :
    (Scheme.Modules.pullback f).obj (SchemeModuleInternalHom.dual M) ≅
      SchemeModuleInternalHom.dual ((Scheme.Modules.pullback f).obj M) := by
  let P := Scheme.Modules.pullback f
  let p := schemeModulePullbackDualEvaluationOfLocallyRankOne f M hM
  let hp : IsIso p := schemeModulePullbackDualEvaluationOfLocallyRankOne_isIso f M hM
  let hg : IsIso (SchemeModuleInternalHom.tensorCurry (P.obj M)
      (P.obj (SchemeModuleInternalHom.dual M)) (SheafOfModules.unit Y.ringCatSheaf) p) :=
    @SchemeModuleInternalHom.tensorCurry_dual_isIso_of_locallyRankOne Y
      (P.obj M) (P.obj (SchemeModuleInternalHom.dual M))
      (schemeModuleLocallyRankOne_pullback f M hM) p hp
  exact @asIso Y.Modules (inferInstance : Category Y.Modules) _ _
    (SchemeModuleInternalHom.tensorCurry (P.obj M)
      (P.obj (SchemeModuleInternalHom.dual M)) (SheafOfModules.unit Y.ringCatSheaf) p) hg

/-- The actual forward intrinsic-dual comparison preserves evaluation. -/
theorem schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne_evaluation
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) :
    schemeModuleTensorMap (𝟙 ((Scheme.Modules.pullback f).obj M))
        (schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne f M hM).hom ≫
      SchemeModuleInternalHom.dualEvaluation ((Scheme.Modules.pullback f).obj M) =
    schemeModulePullbackDualEvaluationOfLocallyRankOne f M hM := by
  exact SchemeModuleInternalHom.tensorCurry_evaluation
    ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj (SchemeModuleInternalHom.dual M))
    (SheafOfModules.unit Y.ringCatSheaf)
    (schemeModulePullbackDualEvaluationOfLocallyRankOne f M hM)

/-- Literal original canonical tensor-pullback/evaluation square,
now with the intrinsic dual of the actual pulled-back module. -/
theorem schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne_tensor_square
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) :
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
        (SchemeModuleInternalHom.dual M) ≫
      schemeModuleTensorMap (𝟙 ((Scheme.Modules.pullback f).obj M))
        (schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne f M hM).hom ≫
      SchemeModuleInternalHom.dualEvaluation ((Scheme.Modules.pullback f).obj M) =
    (Scheme.Modules.pullback f).map (SchemeModuleInternalHom.dualEvaluation M) ≫
      BundleSectionZeroLocus.pullbackUnitComparison f := by
  rw [schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne_evaluation]
  exact schemeModulePullbackDualEvaluationOfLocallyRankOne_tensor_square f M hM

/-- The own quotient is the tensor with the INTRINSIC dual of the
original ideal's actual pullback, derived without compatibility input. -/
def RegularPrincipalImmersion.actualCartierResidueIntrinsicNormalTensorIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    (H.actualCartierResidueSequence W).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
          (SchemeModuleInternalHom.dual ((Scheme.Modules.pullback i).obj
            (IdealSheafDataModule.closedImmersionModule i)))) :=
  H.actualCartierResidueRestrictedTensorIso W hW ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (schemeModuleTensorMapIso (Iso.refl ((Scheme.Modules.pullback i).obj W))
        (schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne i
          (IdealSheafDataModule.closedImmersionModule i) H.inverseCartierTwist_locallyRankOne))

/-- The actual own quotient hom is the original canonical projection,
original tensor comparison, and constructed intrinsic-dual comparison. -/
theorem RegularPrincipalImmersion.actualCartierResidueIntrinsicNormalTensorIso_hom
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    (H.actualCartierResidueIntrinsicNormalTensorIso W hW).hom =
      (H.actualCartierResidueProjectionIso W hW).hom ≫
        (Scheme.Modules.pushforward i).map
          (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i W
            (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i))) ≫
        (Scheme.Modules.pushforward i).map
          (schemeModuleTensorMap (𝟙 ((Scheme.Modules.pullback i).obj W))
            (schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne i
              (IdealSheafDataModule.closedImmersionModule i)
              H.inverseCartierTwist_locallyRankOne).hom) := by
  change ((H.actualCartierResidueProjectionIso W hW).hom ≫
    (Scheme.Modules.pushforward i).map
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i W
        (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)))) ≫
    (Scheme.Modules.pushforward i).map
      (schemeModuleTensorMap (𝟙 ((Scheme.Modules.pullback i).obj W))
        (schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne i
          (IdealSheafDataModule.closedImmersionModule i)
          H.inverseCartierTwist_locallyRankOne).hom) = _
  exact Category.assoc _ _ _

end PfaffianDescent
end

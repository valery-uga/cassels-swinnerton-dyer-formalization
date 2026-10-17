import PfaffianDescent.SchemeModuleInternalHomRankOneEvaluation
import PfaffianDescent.BasiswiseBijectiveModuleSheafification

/-! GLOBAL inverse from actual pointwise unit charts. Smaller chart
opens form a genuine topological basis; the SAME raw evaluation is
bijective there. Actual module sheafification and its actual counit
therefore prove the GLOBAL canonical evaluation IsIso. No inverse,
dual-chart, evaluation or sheafification certificate is assumed.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Actual restriction of a unit chart, through the installed over-site
functors and their actual natural comparison. No dual comparison input. -/
def overUnitChartRestrict {U V : X.Opens} (f : V ⟶ U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    M.over V ≅ (SheafOfModules.unit X.ringCatSheaf).over V :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf f).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf f).mapIso e ≪≫
    (SheafOfModules.overFunctorMap X.ringCatSheaf f).app
      (SheafOfModules.unit X.ringCatSheaf)

/-- Actual canonical evaluation is the sheafification of the SAME raw
map followed by the target's actual sheafification counit. -/
theorem evaluation_eq_sheafification_counit :
    evaluation M N =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (evaluationPresheaf M N) ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app N := by
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_counit
    _ _ (evaluationPresheaf M N)

/-- The GLOBAL actual canonical dual evaluation is invertible when the
original input module has genuine pointwise rank-one unit charts. Only
charts of M are natural generic hypotheses: the dual and its evaluation
are constructed internally, and the primitive point-ideal caller derives
the charts from its actual original geometry. Empty schemes are included. -/
theorem dualEvaluation_isIso_of_pointwise_unitCharts
    (U : X → X.Opens) (hU : ∀ x, x ∈ U x)
    (e : ∀ x, M.over (U x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (U x)) :
    IsIso (dualEvaluation M) := by
  let I : Type u := {V : X.Opens // ∃ x : X, V ≤ U x}
  let B : I → X.Opens := Subtype.val
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hxW
    exact ⟨W ⊓ U x, ⟨⟨W ⊓ U x, x, inf_le_right⟩, rfl⟩,
      ⟨hxW, hU x⟩, inf_le_left⟩
  haveI hraw : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (evaluationPresheaf M (SheafOfModules.unit X.ringCatSheaf))) := by
    apply moduleSheafification_map_isIso_of_basiswise_bijective
      (evaluationPresheaf M (SheafOfModules.unit X.ringCatSheaf)) B hB
    intro V
    obtain ⟨x, hVU⟩ := V.2
    let eV := overUnitChartRestrict M (homOfLE hVU) (e x)
    haveI : IsIso ((evaluationPresheaf M (SheafOfModules.unit X.ringCatSheaf)).app
        (op V.1)) := evaluationPresheaf_app_isIso M V.1 eV
    exact ConcreteCategory.bijective_of_isIso _
  change IsIso (evaluation M (SheafOfModules.unit X.ringCatSheaf))
  rw [evaluation_eq_sheafification_counit]
  have hcounit : IsIso
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
        (SheafOfModules.unit X.ringCatSheaf)) :=
    NatIso.isIso_app_of_isIso
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
      (SheafOfModules.unit X.ringCatSheaf)
  exact IsIso.comp_isIso' hraw hcounit

/-- The actual constructed O-linear dual is a GLOBAL tensor inverse;
the forward map is the SAME canonical sheafified evaluation. -/
def dualTensorInverseIso_of_pointwise_unitCharts
    (U : X → X.Opens) (hU : ∀ x, x ∈ U x)
    (e : ∀ x, M.over (U x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (U x)) :
    schemeModuleTensor M (dual M) ≅ SheafOfModules.unit X.ringCatSheaf := by
  letI := dualEvaluation_isIso_of_pointwise_unitCharts M U hU e
  exact asIso (dualEvaluation M)

end PfaffianDescent.SchemeModuleInternalHom

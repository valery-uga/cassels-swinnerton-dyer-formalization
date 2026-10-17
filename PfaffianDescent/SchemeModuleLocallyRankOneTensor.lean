import PfaffianDescent.SchemeModuleInternalHomRankOneInverse
import PfaffianDescent.SheafFreeCover

/-! Actual local rank-one geometry, expressed by ordinary unit neighborhoods.
Tensor exactness is derived from these charts, never supplied as a certificate.
All tensor products and coefficient rings are the original sheaf constructions.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- Ordinary local rank-one geometry on the original scheme. This is
actual local triviality, with no exactness, fiber or dimension conclusion. -/
def schemeModuleLocallyRankOne (L : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (L.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)

/-- Internally choose pointwise charts from ordinary local rank-one geometry. -/
theorem schemeModuleLocallyRankOne_pointwise_charts
    (L : X.Modules) (hL : schemeModuleLocallyRankOne L) :
    ∃ B : X → X.Opens, (∀ x, x ∈ B x) ∧
      Nonempty (∀ x, L.over (B x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (B x)) := by
  classical
  let B : X → X.Opens := fun x => Classical.choose (hL x)
  have hB (x : X) : x ∈ B x := (Classical.choose_spec (hL x)).1
  let e (x : X) := Classical.choice ((Classical.choose_spec (hL x)).2)
  exact ⟨B, hB, ⟨e⟩⟩

/-- Rank-one neighborhoods genuinely imply the installed local-free property. -/
theorem schemeModuleLocallyRankOne_isLocallyFree
    (L : X.Modules) (hL : schemeModuleLocallyRankOne L) : L.IsLocallyFree := by
  classical
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts L hL
  apply sheaf_isLocallyFree_of_pointwise_free X L B hB (fun _ => PUnit.{u+1})
  intro x
  exact (coproductUniqueIso (fun _ : PUnit.{u+1} =>
    SheafOfModules.unit (X.ringCatSheaf.over (B x)))) ≪≫ (eB x).symm

/-- Actual tensor chart after refining both original unit neighborhoods. -/
def schemeModuleTensorOverUnitIso
    (M L : X.Modules) (U : X.Opens)
    (eM : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (eL : L.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (schemeModuleTensor M L).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U :=
  schemeModuleTensorOverIso U M L ≪≫
    SheafOfModules.commRingSheafTensorMapIso
      (SheafOfModules.commRingSheafOver X.sheaf U) eM eL ≪≫
    SheafOfModules.commRingSheafTensorUnitRightIso
      (SheafOfModules.commRingSheafOver X.sheaf U)
      ((SheafOfModules.unit X.ringCatSheaf).over U)

/-- Products of actual rank-one sheaves are rank one on the actual
intersection chart; the original scalar rings are retained. -/
theorem schemeModuleLocallyRankOne_tensor
    (M L : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (hL : schemeModuleLocallyRankOne L) : schemeModuleLocallyRankOne (schemeModuleTensor M L) := by
  classical
  intro x
  obtain ⟨U, hxU, ⟨eM⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨eL⟩⟩ := hL x
  let W := U ⊓ V
  let eMW := SchemeModuleInternalHom.overUnitChartRestrict M
    (homOfLE (show W ≤ U from inf_le_left)) eM
  let eLW := SchemeModuleInternalHom.overUnitChartRestrict L
    (homOfLE (show W ≤ V from inf_le_right)) eL
  exact ⟨W, ⟨hxU, hxV⟩, ⟨schemeModuleTensorOverUnitIso M L W eMW eLW⟩⟩

/-- Tensor flatness in its actual categorical form, internally from the
rank-one neighborhoods. No PreservesFiniteLimits certificate is input. -/
theorem schemeModuleLocallyRankOne_tensor_preservesFiniteLimits
    (L : X.Modules) (hL : schemeModuleLocallyRankOne L) :
    PreservesFiniteLimits (schemeModuleTensorRight L) := by
  classical
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts L hL
  have hcover : (Opens.grothendieckTopology X).CoversTop B := by
    apply (Opens.coversTop_iff X B).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  exact schemeModuleTensorRight_preservesFiniteLimits_of_coversTop_iso_unit B hcover eB

/-- Tensoring an actual short exact sequence by the actual rank-one L
is short exact. The geometric primitive caller derives the original hS. -/
theorem schemeModuleLocallyRankOne_tensor_shortExact
    (L : X.Modules) (hL : schemeModuleLocallyRankOne L)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (schemeModuleTensorRight L)).ShortExact := by
  classical
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts L hL
  have hcover : (Opens.grothendieckTopology X).CoversTop B := by
    apply (Opens.coversTop_iff X B).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  exact shortComplex_tensor_shortExact_of_coversTop_iso_unit S hS B hcover eB

end PfaffianDescent


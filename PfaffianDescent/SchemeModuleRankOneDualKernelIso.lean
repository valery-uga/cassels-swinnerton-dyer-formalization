import PfaffianDescent.SchemeModuleLocallyRankOneTensor
import PfaffianDescent.SchemeModuleTensorInverseContraction
import PfaffianDescent.SheafificationTensorComparison
import PfaffianDescent.SchemeModuleInternalHomRankOneAction
import PfaffianDescent.SchemeModuleInternalHomDualOverUnit

/-! Canonical contraction of the SAME rank-one ideal and its actual dual.
The original sheafification comparison is derived from genuine unit charts.
No association, inverse, comparison or action certificate is a hypothesis.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- The actual constructed O-linear dual retains genuine rank-one geometry. -/
theorem schemeModuleLocallyRankOne_dual (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) :
    schemeModuleLocallyRankOne (SchemeModuleInternalHom.dual M) := by
  intro x
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM x
  exact ⟨U, hxU, ⟨SchemeModuleInternalHom.dualOverUnitIso U eU⟩⟩

/-- Invertibility of the ACTUAL right-sheafification comparison, from
ordinary original neighborhoods of its right tensor factor. -/
theorem schemeModuleLocallyRankOne_rightComparison_isIso
    (P : PresheafOfModules X.ringCatSheaf.obj) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) :
    IsIso (schemeModuleTensorSheafificationRightComparison P M) := by
  classical
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  have hc : (Opens.grothendieckTopology X).CoversTop B := by
    apply (Opens.coversTop_iff X B).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  apply schemeModuleTensorSheafificationRightComparison_isIso_of_coversTop B hc P M
  intro x
  exact restrict_schemeModuleTensorSheafificationRightComparison_isIso_of_over_iso_unit
    (B x) P M (eB x)

/-- SAME evaluation with its two factors swapped. All choices occur only
in proving invertibility; the forward map is literal symmetry/evaluation. -/
def schemeModuleRankOneSwappedDualPairingIso
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M) :
    schemeModuleTensor (SchemeModuleInternalHom.dual M) M ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : IsIso (SchemeModuleInternalHom.dualEvaluation M) := by
    classical
    obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
    exact SchemeModuleInternalHom.dualEvaluation_isIso_of_pointwise_unitCharts M B hB eB
  exact schemeModuleTensorSymmetry (SchemeModuleInternalHom.dual M) M ≪≫
    asIso (SchemeModuleInternalHom.dualEvaluation M)

/-- The raw adjoint of the swapped SAME pairing is literal swapped
component evaluation, by the sheafification unit's naturality. -/
theorem schemeModuleRankOneSwappedDualPairingRaw
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M) :
    letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    letI : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
      PresheafOfModules.symmetricCategory
    schemeModuleTensorPairingRaw (SchemeModuleInternalHom.dual M) M
        (schemeModuleRankOneSwappedDualPairingIso M hM) =
      (β_ (SchemeModuleInternalHom.dual M).val M.val).hom ≫
        SchemeModuleInternalHom.evaluationPresheaf M
          (SheafOfModules.unit X.ringCatSheaf) := by
  let D := SchemeModuleInternalHom.dual M
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  letI : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.symmetricCategory
  let b := (β_ D.val M.val).hom
  have he : adj.unit.app (PresheafOfModules.Monoidal.tensorObj M.val D.val) ≫
      (SchemeModuleInternalHom.dualEvaluation M).val =
        SchemeModuleInternalHom.evaluationPresheaf M (SheafOfModules.unit X.ringCatSheaf) := by
    change adj.homEquiv _ _ (SchemeModuleInternalHom.dualEvaluation M) = _
    exact SchemeModuleInternalHom.evaluation_raw M (SheafOfModules.unit X.ringCatSheaf)
  have hn : b ≫ adj.unit.app _ = adj.unit.app _ ≫ (F.map b).val :=
    adj.unit.naturality b
  change adj.unit.app _ ≫ ((F.map b).val ≫
    (SchemeModuleInternalHom.dualEvaluation M).val) = b ≫ _
  rw [← Category.assoc, ← hn, Category.assoc]
  exact congrArg (fun a => b ≫ a) he

/-- Inverse symmetry is the actual reversed symmetry. -/
theorem schemeModuleTensorSymmetry_inv_eq (M N : X.Modules) :
    (schemeModuleTensorSymmetry M N).inv = (schemeModuleTensorSymmetry N M).hom := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  letI : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.symmetricCategory
  change F.map (β_ M.val N.val).inv = F.map (β_ N.val M.val).hom
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding]

/-- The original sheaf tensor symmetry and left unitor give the SAME
right unitor, by the actual raw braiding/unit law. -/
theorem schemeModuleTensorSymmetry_unit_leftUnitor (T : X.Modules) :
    (schemeModuleTensorSymmetry T (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (schemeModuleTensorUnitLeftIso T).hom = (schemeModuleTensorUnitRightIso T).hom := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  letI : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.symmetricCategory
  change F.map (β_ T.val (𝟙_ _)).hom ≫
      (F.map (λ_ T.val).hom ≫ adj.counit.app T) =
    F.map (ρ_ T.val).hom ≫ adj.counit.app T
  rw [← Category.assoc, ← F.map_comp, CategoryTheory.braiding_leftUnitor]

/-- The comparison followed by the actual unitor cancels precisely the
inner sheafification, by its genuine triangle identity. -/
theorem schemeModuleTensorRightComparison_unit_normalization
    (P : PresheafOfModules X.ringCatSheaf.obj) :
    letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    schemeModuleTensorSheafificationRightComparison P (SheafOfModules.unit X.ringCatSheaf) ≫
      (schemeModuleTensorUnitRightIso (F.obj P)).hom =
        F.map (ρ_ P).hom := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  have hr := rightUnitor_naturality (adj.unit.app P)
  have ht : F.map (adj.unit.app P) ≫ adj.counit.app (F.obj P) = 𝟙 (F.obj P) :=
    adj.left_triangle_components P
  change F.map ((adj.unit.app P) ⊗ₘ (𝟙 (𝟙_ _))) ≫
      (F.map (ρ_ (F.obj P).val).hom ≫ adj.counit.app (F.obj P)) = F.map (ρ_ P).hom
  calc
    _ = F.map (((adj.unit.app P) ⊗ₘ (𝟙 (𝟙_ _))) ≫
          (ρ_ (F.obj P).val).hom) ≫ adj.counit.app (F.obj P) := by
      rw [← Category.assoc, ← F.map_comp]
    _ = F.map ((ρ_ P).hom ≫ adj.unit.app P) ≫ adj.counit.app (F.obj P) :=
      congrArg (fun a => F.map a ≫ adj.counit.app (F.obj P)) hr
    _ = F.map (ρ_ P).hom := by
      rw [F.map_comp, Category.assoc, ht, Category.comp_id]

/-- Canonical kernel map, with SAME actual evaluation and the existing
contraction. The needed comparison is internally derived from M geometry. -/
def schemeModuleRankOneDualKernelMap
    (M L : X.Modules) (hM : schemeModuleLocallyRankOne M) :
    schemeModuleTensor M (schemeModuleTensor L (SchemeModuleInternalHom.dual M)) ⟶ L := by
  let D := SchemeModuleInternalHom.dual M
  letI := schemeModuleLocallyRankOne_rightComparison_isIso
    (PresheafOfModules.Monoidal.tensorObj L.val D.val) M hM
  exact (schemeModuleTensorSymmetry M (schemeModuleTensor L D)).hom ≫
    schemeModuleTensorContraction L D M (schemeModuleRankOneSwappedDualPairingIso M hM)

/-- The canonical kernel map is invertible for every actual L. Both
comparison and inverse-pairing tensor invertibility are internally geometric. -/
theorem schemeModuleRankOneDualKernelMap_isIso
    (M L : X.Modules) (hM : schemeModuleLocallyRankOne M) :
    IsIso (schemeModuleRankOneDualKernelMap M L hM) := by
  classical
  let D := SchemeModuleInternalHom.dual M
  let e := schemeModuleRankOneSwappedDualPairingIso M hM
  letI := schemeModuleLocallyRankOne_rightComparison_isIso
    (PresheafOfModules.Monoidal.tensorObj L.val D.val) M hM
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  have hc : (Opens.grothendieckTopology X).CoversTop B := by
    apply (Opens.coversTop_iff X B).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  let eD (x : X) := SchemeModuleInternalHom.dualOverUnitIso (B x) (eB x)
  letI : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (𝟙 L.val)
        (schemeModuleTensorPairingRaw D M e))) :=
    schemeModuleTensorPairingRaw_tensor_isIso_of_coversTop B hc L D M e eD eB
  letI := schemeModuleTensorContraction_isIso_of_pairingTensorMap_isIso L D M e
  change IsIso ((schemeModuleTensorSymmetry M (schemeModuleTensor L D)).hom ≫
    schemeModuleTensorContraction L D M e)
  infer_instance

/-- Canonical I tensor(L tensor D) Iso L; its forward map is exactly the
preceding SAME evaluation/contraction map, with no chosen arbitrary inverse. -/
def schemeModuleRankOneDualKernelIso
    (M L : X.Modules) (hM : schemeModuleLocallyRankOne M) :
    schemeModuleTensor M (schemeModuleTensor L (SchemeModuleInternalHom.dual M)) ≅ L := by
  letI := schemeModuleRankOneDualKernelMap_isIso M L hM
  exact asIso (schemeModuleRankOneDualKernelMap M L hM)

end PfaffianDescent

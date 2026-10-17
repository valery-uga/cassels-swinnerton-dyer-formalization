import PfaffianDescent.CorayAffineRankOneSectionCokernelModel
import PfaffianDescent.CorayStalkSupportClosedGluing
import PfaffianDescent.SchemeModuleLocallyRankOneTensor

/-! Closed actual support of the original unit-to-rank-one cokernel.
The affine finite-module model and the covering charts are constructed
from local rank-one geometry. No support or quasicoherence certificate.
SOURCE ONLY / UNVERIFIED: root owns all compiler checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every original unit-to-rank-one cokernel has closed nonzero-stalk
support, including the zero map. Its finite local module models are
internally constructed on genuine affine refinements of the unit charts. -/
theorem schemeModuleUnitHom_cokernel_stalkSupport_isClosed
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    IsClosed (schemeModuleStalkSupport (cokernel φ)) := by
  classical
  have hcharts : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (M.over U.1 ≅ (SheafOfModules.unit X.ringCatSheaf).over U.1) := by
    intro x
    obtain ⟨V, hxV, ⟨eV⟩⟩ := hM x
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
    exact ⟨⟨U, hU⟩, hxU, ⟨SchemeModuleInternalHom.overUnitChartRestrict M
      (homOfLE (show U ≤ V from hUV)) eV⟩⟩
  let B : X → X.affineOpens := fun x => Classical.choose (hcharts x)
  have hB (x : X) : x ∈ (B x).1 := (Classical.choose_spec (hcharts x)).1
  let e (x : X) : M.over (B x).1 ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x).1 :=
    Classical.choice (Classical.choose_spec (hcharts x)).2
  let Y : X → Scheme.{u} := fun x => (B x).1.toScheme
  let f : ∀ x, Y x ⟶ X := fun x => (B x).1.ι
  have hcover : ∀ x : X, ∃ j, ∃ y : Y j, f j y = x :=
    fun x => ⟨x, ⟨x, hB x⟩, rfl⟩
  apply schemeModuleStalkSupport_isClosed_of_open_cover (cokernel φ) Y f hcover
  intro x
  exact (affineOpenUnitHomCokernel_sections_finite_and_stalkSupport_isClosed
    M (B x).1 (B x).2 (e x) φ).2

end PfaffianDescent.Coray

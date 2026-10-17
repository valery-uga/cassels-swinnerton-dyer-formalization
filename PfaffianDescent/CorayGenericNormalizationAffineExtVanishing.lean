import PfaffianDescent.CorayGenericNormalizationAffineQuasicoherent
import PfaffianDescent.AffineOpenCohomology

/-! Actual affine section-representer Ext for the actual normalization quotient.
Quasicoherence of the precise canonical restriction is derived internally.
This is a local Ext theorem, not global normalization-Q Ext vanishing.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u

/-- Ext in degrees one and two from the actual section representer of each
actual affine open into the actual global normalization quotient vanishes.
Only ordinary integral and locally noetherian geometry and the Ext
infrastructure are assumed; the exact fromSpec restriction is proved QC. -/
theorem genericNormalizationQuotientSheaf_affine_sectionRepresenter_ext_one_and_two_subsingleton
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules] (U : X.Opens) (hU : IsAffineOpen U) :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U)
      (genericNormalizationQuotientSheaf X) 1) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U)
      (genericNormalizationQuotientSheaf X) 2) := by
  exact sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen_of_restrict
    U hU (genericNormalizationQuotientSheaf X)
    (genericNormalizationQuotientSheaf_restrictFromSpec_isQuasicoherent X U hU)

end PfaffianDescent.Coray

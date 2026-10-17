import PfaffianDescent.VoisinFixedLinearSystemUniversalFamily
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Actual relative evaluation coefficients on three trivializing charts

The entries are restrictions of actual global bundle sections, expressed in
actual bundle trivializations and pulled back along the three marked maps.
They are regular functions on the configuration chart.  Their field-valued
specialization is proved from functorial evaluation of these same functions.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A literal relative evaluation matrix on a common configuration chart. -/
def serreThreePointRelativeEvaluationMatrix
    {X B : Scheme.{u}} {M : X.Modules} {ι : Type u}
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (chart : Fin 3 → C.ι)
    (marked : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
    (sections : Fin 9 → M.sections) :
    Matrix (Fin 3 × ι) (Fin 9) Γ(B, ⊤) := fun row col =>
  (marked row.1).appTop
    (BundleSectionZeroLocus.sectionCoordinateOfFreeIso ι
      (BundleSectionZeroLocus.localFreeIsoOfOver (C.U (chart row.1)) ι
        (C.trivialization (chart row.1)))
      (BundleSectionZeroLocus.restrictSectionToOpen (C.U (chart row.1))
        (sections col)) row.2)

/-- Specialization is evaluation of the literal restricted section coordinate
at the actual marked field-valued point. -/
theorem serreThreePointRelativeEvaluationMatrix_fieldPoint
    {X B : Scheme.{u}} {M : X.Modules} {ι : Type u}
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (chart : Fin 3 → C.ι)
    (marked : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
    (sections : Fin 9 → M.sections)
    {F : Type u} [Field F] (b : Spec (.of F) ⟶ B)
    (row : Fin 3 × ι) (col : Fin 9) :
    fieldPointΓevaluation b
      (serreThreePointRelativeEvaluationMatrix C chart marked sections row col) =
    fieldPointΓevaluation (b ≫ marked row.1)
      (BundleSectionZeroLocus.sectionCoordinateOfFreeIso ι
        (BundleSectionZeroLocus.localFreeIsoOfOver (C.U (chart row.1)) ι
          (C.trivialization (chart row.1)))
        (BundleSectionZeroLocus.restrictSectionToOpen (C.U (chart row.1))
          (sections col)) row.2) := by
  exact (fieldPointΓevaluation_comp b (marked row.1) _).symm

end PfaffianDescent

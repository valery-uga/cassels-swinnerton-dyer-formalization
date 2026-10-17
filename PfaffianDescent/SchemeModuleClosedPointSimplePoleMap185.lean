import PfaffianDescent.ActualSimplePoleDualFactor185
import PfaffianDescent.SchemeModuleClosedPointSectionFactor183
import PfaffianDescent.CorayPerfectOwnNormalizationPointIdealRankOne

/-! SOURCE ONLY / UNVERIFIED. The SAME actual point support internally
constructs v, and genuine DVR geometry internally supplies rank-one I_P.
The explicit dual contraction constructs t with delta≫t=original phi.
The whole original cokernel is retained; no trace formula is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine point-support-to-simple-pole map on the SAME scheme and
SAME original M and phi. No factor or unit square is a premise. -/
theorem schemeModuleUnitHom_closedPoint_exists_simplePoleMap185
    [IsIntegral X] [IsLocallyNoetherian X]
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (P : closedPoints X)
    [IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    (hP : P.1 ∈ Coray.schemeModuleStalkSupport (cokernel φ)) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∃ t : SchemeModuleInternalHom.dual (show X.Modules from closedImmersionModule i) ⟶ M,
      SchemeModuleInternalHom.unitToHom (closedImmersionModuleToUnit i) ≫ t = φ := by
  classical
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let I : X.Modules := closedImmersionModule i
  let j : I ⟶ SheafOfModules.unit X.ringCatSheaf := closedImmersionModuleToUnit i
  have hI : schemeModuleLocallyRankOne I :=
    Coray.closedPointIdeal_locallyRankOne_of_stalk_isDVR X P
  obtain ⟨v, hv⟩ := schemeModuleUnitHom_closedPoint_exists_idealTensor_factor183 M hM φ P hP
  refine ⟨schemeModuleSimplePoleDualFactor185 I M hI v, ?_⟩
  exact (schemeModuleSimplePoleDualFactor_unitSquare185 I M hI j v).trans hv

/-- Literal original-section specialization. Whole Q remains the cokernel
of this SAME original section morphism; no reduced replacement appears. -/
theorem schemeModuleTopSectionHom_closedPoint_exists_simplePoleMap185
    [IsIntegral X] [IsLocallyNoetherian X]
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (P : closedPoints X)
    [IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    (hP : P.1 ∈ Coray.schemeModuleStalkSupport (cokernel (schemeModuleTopSectionHom M s))) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∃ t : SchemeModuleInternalHom.dual (show X.Modules from closedImmersionModule i) ⟶ M,
      SchemeModuleInternalHom.unitToHom (closedImmersionModuleToUnit i) ≫ t =
        schemeModuleTopSectionHom M s :=
  schemeModuleUnitHom_closedPoint_exists_simplePoleMap185 M hM
    (schemeModuleTopSectionHom M s) P hP

end PfaffianDescent

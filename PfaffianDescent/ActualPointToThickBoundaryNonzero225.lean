import PfaffianDescent.ActualUnitCokernelConnectingNaturality184
import PfaffianDescent.SchemeModuleClosedPointSimplePoleMap185
import PfaffianDescent.SchemeModuleInternalHomIncrementExact

/-! Transfer to the SAME original thick cokernel. These intermediate cuts
expose the point connecting value as an input; the original geometric
factory224 must construct that value before applying them. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open IdealSheafDataModule SchemeModuleInternalHom
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native extension naturality transfers a nonzero actual section value
to nonzero of the literal target global connecting AddHom. -/
theorem actualUnitCokernel_globalBoundaryNonzero_of_value225
    {X : Scheme.{u}} [HasExt.{u} X.Modules] {A B : X.Modules}
    (delta : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ A)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ B)
    (t : A ⟶ B) (ht : delta ≫ t = phi)
    (hdelta : (ShortComplex.cokernelSequence delta).ShortExact)
    (hphi : (ShortComplex.cokernelSequence phi).ShortExact)
    (c : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ cokernel delta)
    (hc : (Ext.mk₀.{u} c).comp hdelta.extClass (zero_add 1) ≠ 0) :
    hphi.extClass.postcomp
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0 := by
  intro hzero
  have hvalue := DFunLike.congr_fun hzero
    (Ext.mk₀.{u} (c ≫ actualUnitCokernelMap184 delta phi t ht))
  change (Ext.mk₀.{u} (c ≫ actualUnitCokernelMap184 delta phi t ht)).comp
    hphi.extClass (zero_add 1) = 0 at hvalue
  exact hc ((actualUnitCokernel_unitHomConnecting_eq184
    delta phi t ht hdelta hphi c).trans hvalue)

/-- Genuine point-support geometry constructs the simple-pole map into
the SAME original line module and section. Point nonvanishing remains an
explicit intermediate input; the target cokernel is never reduced. -/
theorem schemeModuleUnitHom_closedPoint_globalBoundaryNonzero225
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules]
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M)
    (hphi : (ShortComplex.cokernelSequence phi).ShortExact)
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    (hP : P.1 ∈ Coray.schemeModuleStalkSupport (cokernel phi)) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∀ (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
      (c : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
        (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃),
      (Ext.mk₀.{u} c).comp hS.extClass (zero_add 1) ≠ 0 →
      hphi.extClass.postcomp
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (zero_add 1) ≠ 0 := by
  dsimp only
  intro hS c hc
  obtain ⟨t, ht⟩ := schemeModuleUnitHom_closedPoint_exists_simplePoleMap185 M hM phi P hP
  exact actualUnitCokernel_globalBoundaryNonzero_of_value225
    (unitToHom (closedImmersionModuleToUnit (X.fromSpecResidueField P.1)))
    phi t ht hS hphi c hc

end PfaffianDescent

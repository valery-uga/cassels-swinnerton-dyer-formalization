import PfaffianDescent.CubicPointCompatibleNegativeThreeResidueEquiv
import PfaffianDescent.PointCartierNativeStalkResidueNonzero
import PfaffianDescent.FieldPointTwistQuotient

/-! # Actual positive-three closed-point coordinates

The existing smooth surface calculation applies directly to the actual
positive-twisted point source and the unit coefficient. This detects the
actual stalk of a globally nonzero connecting class without transporting
it through an inverse twist.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def cubicClosedPointSerreLocalFree_positiveCoordinate
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Ext.{u} (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).X₃
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 2 ≃+ L := by
  let I := equationIdeal p hp
  let V : ULift.{u} (Fin 4) → (hypersurface p hp).Opens :=
    fun j => quotientCoordinateOpen I j.down
  have hV : (Opens.grothendieckTopology (hypersurface p hp)).CoversTop V := by
    apply (Opens.coversTop_iff _ _).mpr
    apply TopologicalSpace.IsOpenCover.mk
    simpa [V, iSup_ulift] using quotientCoordinateOpen_iSup I
  exact fieldPointExtTwoCoordinateAddEquivOfSmoothCubicSurfaceLocalTarget p hp hp0 i
    (positiveSheafOfModules (grading I) 3) V hV
    (fun j => overFunctorIsoUnit_of_restrictIsoUnit (V j)
      (quotientCoordinatePositiveTwistUnitIso_all I j.down 3))
    (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
    (fun j => Scheme.Modules.restrictUnitIso (V j).ι)

theorem cubicClosedPointSerreLocalFree_positiveCoordinate_presentation
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Nonempty (FieldPointExtResiduePresentation i default
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).X₃
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
      (cubicClosedPointSerreLocalFree_positiveCoordinate K p hp hp0 i)) := by
  let I := equationIdeal p hp
  let V : ULift.{u} (Fin 4) → (hypersurface p hp).Opens :=
    fun j => quotientCoordinateOpen I j.down
  have hV : (Opens.grothendieckTopology (hypersurface p hp)).CoversTop V := by
    apply (Opens.coversTop_iff _ _).mpr
    apply TopologicalSpace.IsOpenCover.mk
    simpa [V, iSup_ulift] using quotientCoordinateOpen_iSup I
  exact fieldPointExtTwoCoordinateAddEquivOfSmoothCubicSurfaceLocalTarget_residuePresentation
    p hp hp0 i (positiveSheafOfModules (grading I) 3) V hV
    (fun j => overFunctorIsoUnit_of_restrictIsoUnit (V j)
      (quotientCoordinatePositiveTwistUnitIso_all I j.down 3))
    (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
    (fun j => Scheme.Modules.restrictUnitIso (V j).ι)

theorem cubicClosedPointSerreLocalFree_positive_stalk_ne_zero
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).X₃
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 2) (hz : z ≠ 0) :
    schemeModuleStalkModuleExtMap (hypersurface p hp) (i default) _ _ 2 z ≠ 0 := by
  let e := cubicClosedPointSerreLocalFree_positiveCoordinate K p hp hp0 i
  let d := Classical.choice
    (cubicClosedPointSerreLocalFree_positiveCoordinate_presentation K p hp hp0 i)
  apply pointCartierNativeStalkResidue_local_ne_zero i default _ _ e d z
  intro hezero
  apply hz
  apply e.injective
  simpa only [map_zero] using hezero

def cubicClosedPointSerreLocalFree_positiveTwistStalkIso
    (K : Type u) [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ hypersurface p hp) :
    (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3) ≅
      ModuleCat.of ((hypersurface p hp).presheaf.stalk (i default))
        ((hypersurface p hp).presheaf.stalk (i default)) := by
  let I := equationIdeal p hp
  have hcover : ∃ j : Fin 4, i default ∈ quotientCoordinateOpen I j := by
    have hx : i default ∈ (⨆ j : Fin 4, quotientCoordinateOpen I j) := by
      rw [quotientCoordinateOpen_iSup I]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  let j := Classical.choose hcover
  exact schemeModuleLocalUnitStalkIso (quotientCoordinateOpen I j)
    ⟨i default, Classical.choose_spec hcover⟩
    (positiveSheafOfModules (grading I) 3) (quotientCoordinatePositiveTwistUnitIso_all I j 3)

def cubicClosedPointSerreLocalFree_positivePointStalkIso
    (K : Type u) [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (f g : (hypersurface p hp).presheaf.stalk (i default))
    (hspan : Ideal.span ({f, g} : Set _) =
      IsLocalRing.maximalIdeal ((hypersurface p hp).presheaf.stalk (i default))) :
    (schemeModuleStalkModuleFunctor (hypersurface p hp) (i default)).obj
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).X₃ ≅
      ModuleCat.of ((hypersurface p hp).presheaf.stalk (i default))
        (((hypersurface p hp).presheaf.stalk (i default)) ⧸ Ideal.span ({f, g} : Set _)) := by
  let I := equationIdeal p hp
  have hcover : ∃ j : Fin 4, i default ∈ quotientCoordinateOpen I j := by
    have hx : i default ∈ (⨆ j : Fin 4, quotientCoordinateOpen I j) := by
      rw [quotientCoordinateOpen_iSup I]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  let j := Classical.choose hcover
  exact fieldPointPushforwardTwistStalkQuotientIsoOfLocalTrivialization i default
    (positiveSheafOfModules (grading I) 3) (quotientCoordinateOpen I j)
    (Classical.choose_spec hcover)
    (overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j)
      (quotientCoordinatePositiveTwistUnitIso_all I j 3)) f g hspan

end PfaffianDescent.ProjectiveNegativeTwist

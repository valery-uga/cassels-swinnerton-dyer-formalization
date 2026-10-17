import PfaffianDescent.CubicSurfacePointTargetExtCoordinate
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-! # The actual canonical-target point Ext coordinate on a smooth cubic -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- An actual residue-field coordinate for the canonical-target Ext group of a
closed point on a smooth cubic surface, with the chart and all parameters constructed. -/
def cubicCanonicalPointExtTwoCoordinate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2 ≃+ L := by
  let I := equationIdeal p hp
  let V : ULift.{u} (Fin 4) → (hypersurface p hp).Opens :=
    fun j => quotientCoordinateOpen I j.down
  have hV : (Opens.grothendieckTopology (hypersurface p hp)).CoversTop V := by
    apply (Opens.coversTop_iff _ _).mpr
    apply TopologicalSpace.IsOpenCover.mk
    simpa [V, iSup_ulift] using quotientCoordinateOpen_iSup I
  exact fieldPointExtTwoCoordinateAddEquivOfSmoothCubicSurfaceLocalTarget p hp hp0 i
    (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) V hV
    (fun j => PfaffianDescent.SheafOfModules.overFunctor_globalUnitIso (V j)
      (Iso.refl (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)))
    (sheafOfModules (grading I) 1)
    (fun j => quotientCoordinateNegativeTwistUnitIso_all I j.down 1)

end PfaffianDescent.ProjectiveNegativeTwist

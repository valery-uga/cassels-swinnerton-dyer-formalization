import PfaffianDescent.CubicSurfacePointExtCoordinate
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-!
# Actual twist point Ext coordinates on smooth cubics

The standard coordinate cover and its twist trivializations are supplied by
the verified projective twist construction. No cover data is assumed here.
-/

noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The point-supported Ext² coordinate for an actual intrinsic negative
twist, with the affine parameters and all local trivializations constructed. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfSmoothCubicNegativeTwist
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (m : ℕ) [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Ext.{u} (closedImmersionIdealTwistSequence i (sheafOfModules (grading (equationIdeal p hp)) m)).X₃
      (show (hypersurface p hp).Modules from
        SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 2 ≃+ L := by
  let I := equationIdeal p hp
  let V : ULift.{u} (Fin 4) → (hypersurface p hp).Opens :=
    fun j => quotientCoordinateOpen I j.down
  have hV : (Opens.grothendieckTopology (hypersurface p hp)).CoversTop V := by
    apply (Opens.coversTop_iff _ _).mpr
    apply TopologicalSpace.IsOpenCover.mk
    simpa [V, iSup_ulift] using quotientCoordinateOpen_iSup I
  exact fieldPointExtTwoCoordinateAddEquivOfSmoothCubicSurface p hp hp0 i
    (sheafOfModules (grading I) m) V hV
    (fun j => overFunctorIsoUnit_of_restrictIsoUnit (V j)
      (quotientCoordinateNegativeTwistUnitIso_all I j.down m))
set_option backward.isDefEq.respectTransparency false in
/-- The point-supported Ext² coordinate for an actual intrinsic positive
twist, with the affine parameters and all local trivializations constructed. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfSmoothCubicPositiveTwist
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (m : ℕ) [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Ext.{u} (closedImmersionIdealTwistSequence i (positiveSheafOfModules (grading (equationIdeal p hp)) m)).X₃
      (show (hypersurface p hp).Modules from
        SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 2 ≃+ L := by
  let I := equationIdeal p hp
  let V : ULift.{u} (Fin 4) → (hypersurface p hp).Opens :=
    fun j => quotientCoordinateOpen I j.down
  have hV : (Opens.grothendieckTopology (hypersurface p hp)).CoversTop V := by
    apply (Opens.coversTop_iff _ _).mpr
    apply TopologicalSpace.IsOpenCover.mk
    simpa [V, iSup_ulift] using quotientCoordinateOpen_iSup I
  exact fieldPointExtTwoCoordinateAddEquivOfSmoothCubicSurface p hp hp0 i
    (positiveSheafOfModules (grading I) m) V hV
    (fun j => overFunctorIsoUnit_of_restrictIsoUnit (V j)
      (quotientCoordinatePositiveTwistUnitIso_all I j.down m))
end PfaffianDescent.ProjectiveNegativeTwist

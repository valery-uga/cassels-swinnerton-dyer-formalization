import PfaffianDescent.CubicSurfacePointResiduePresentation
import PfaffianDescent.CubicCanonicalPointExtCoordinate

/-! # Actual residue presentation of the constructed canonical point coordinate -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The canonical-target point coordinate is the actual residue map for
internally constructed local parameters and source/target stalk coordinates. -/
theorem cubicCanonicalPointExtTwoCoordinate_residuePresentation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Nonempty (FieldPointExtResiduePresentation i default
      (closedImmersionIdealTwistSequence i
        (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1)
      (cubicCanonicalPointExtTwoCoordinate K p hp hp0 i)) := by
  let I := equationIdeal p hp
  let V : ULift.{u} (Fin 4) → (hypersurface p hp).Opens :=
    fun j => quotientCoordinateOpen I j.down
  have hV : (Opens.grothendieckTopology (hypersurface p hp)).CoversTop V := by
    apply (Opens.coversTop_iff _ _).mpr
    apply TopologicalSpace.IsOpenCover.mk
    simpa [V, iSup_ulift] using quotientCoordinateOpen_iSup I
  exact fieldPointExtTwoCoordinateAddEquivOfSmoothCubicSurfaceLocalTarget_residuePresentation p hp hp0 i
    (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) V hV
    (fun j => PfaffianDescent.SheafOfModules.overFunctor_globalUnitIso (V j)
      (Iso.refl (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)))
    (sheafOfModules (grading I) 1)
    (fun j => quotientCoordinateNegativeTwistUnitIso_all I j.down 1)

end PfaffianDescent.ProjectiveNegativeTwist

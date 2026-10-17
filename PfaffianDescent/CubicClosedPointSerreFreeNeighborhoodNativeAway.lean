import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodAway
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-! # Native positive-three Serre affine neighborhoods away from the point -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFreeNeighborhood_native_exists_away
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (x : hypersurface p hp) (hx : x ≠ i default) :
    ∃ (W : (hypersurface p hp).Opens), x ∈ W ∧ IsAffineOpen W ∧
      Nonempty (SheafOfModules.free (R := (hypersurface p hp).ringCatSheaf.over W)
        (ULift.{u} (Fin 2)) ≅ e.E.over W) := by
  let I := equationIdeal p hp
  let V := quotientCoordinateOpenLifted I
  have hV : (Opens.grothendieckTopology (hypersurface p hp)).CoversTop V := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  let eV := fun j : ULift.{u} (Fin 4) =>
    overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I j.down)
      (quotientCoordinatePositiveTwistUnitIso_all I j.down 3)
  exact cubicClosedPointSerreFreeNeighborhood_exists_away i
    (positiveSheafOfModules (grading I) 3) V hV eV e x hx

end PfaffianDescent.ProjectiveNegativeTwist

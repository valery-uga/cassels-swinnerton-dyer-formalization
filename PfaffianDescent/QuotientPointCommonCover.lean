import PfaffianDescent.CommonPointAffineCover
import PfaffianDescent.VoisinQuotientCechExtComparison

/-!
# The point-adapted cover and the actual projective coordinate cover

This is the common cover used to compare local point Koszul cocycles with
the intrinsic projective-quotient cohomology calculation. The projective
covering and affinity inputs are discharged by the proved coordinate-open
theorems.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {σ : Type} [Finite σ]

local notation "AA" => MvPolynomial.homogeneousSubmodule σ K

/-- Intersections with the actual lifted projective coordinate family. -/
def quotientPointCommonOpens (I : HomogeneousIdeal AA)
    (U : (Proj (grading I)).Opens) (x : Proj (grading I)) :
    PointAdaptedAffineCover.Index (Proj (grading I)) x × ULift.{u} σ →
      (Proj (grading I)).Opens :=
  PointAdaptedAffineCover.commonOpens U x
    (fun j : ULift.{u} σ => quotientCoordinateOpen I j.down)

theorem quotientPointCommonOpens_coversTop (I : HomogeneousIdeal AA)
    (U : (Proj (grading I)).Opens) (x : Proj (grading I)) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set (Proj (grading I)))) :
    (Opens.grothendieckTopology (Proj (grading I))).CoversTop
      (quotientPointCommonOpens I U x) :=
  PointAdaptedAffineCover.commonOpens_coversTop U x hx hxclosed _
    (quotientCoordinateOpenTop_coversTop I)

theorem quotientPointCommonOpens_isAffineOpen (I : HomogeneousIdeal AA)
    [IsAffineHom (pullback.diagonal (terminal.from (Proj (grading I))))]
    (U : (Proj (grading I)).Opens) (hU : IsAffineOpen U) (x : Proj (grading I))
    (a : PointAdaptedAffineCover.Index (Proj (grading I)) x × ULift.{u} σ) :
    IsAffineOpen (quotientPointCommonOpens I U x a) := by
  apply PointAdaptedAffineCover.commonOpens_isAffineOpen U hU x
    (fun j : ULift.{u} σ => quotientCoordinateOpen I j.down)
  intro j
  simpa using quotientCoordinateOpen_cech_inter_affine I 0 (fun _ : Fin 1 => j.down)

/-- The actual chain map to the projective coordinate-cover chain. -/
def quotientPointCommonToCoordinateChain (I : HomogeneousIdeal AA)
    (U : (Proj (grading I)).Opens) (x : Proj (grading I)) :
    sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
        (quotientPointCommonOpens I U x) ⟶
      quotientSectionRepresenterCechChain I :=
  PointAdaptedAffineCover.commonToOtherChain U x
    (fun j : ULift.{u} σ => quotientCoordinateOpen I j.down)

end PfaffianDescent.ProjectiveNegativeTwist

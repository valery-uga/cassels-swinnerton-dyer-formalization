import PfaffianDescent.QuotientPointCommonCover
import PfaffianDescent.PointPrincipalAffineCover
import PfaffianDescent.SchemeCoverIntrinsicCohomology

/-! # Actual common refinement of the residue and projective coordinate covers -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {σ : Type} [Finite σ]
local notation "AA" => MvPolynomial.homogeneousSubmodule σ K

/-- Keep both principal-open labels while intersecting with coordinate opens. -/
def quotientPrincipalPointCommonOpens (I : HomogeneousIdeal AA)
    (U : (Proj (grading I)).Opens) (x : Proj (grading I))
    (q f : Γ(Proj (grading I), U)) :
    PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x × ULift.{u} σ →
      (Proj (grading I)).Opens := fun a =>
  PointAdaptedAffineCover.principalOpens U x q f a.1 ⊓ quotientCoordinateOpen I a.2.down

theorem quotientPrincipalPointCommonOpens_coversTop (I : HomogeneousIdeal AA)
    (U : (Proj (grading I)).Opens) (x : Proj (grading I)) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set (Proj (grading I))))
    (q f : Γ(Proj (grading I), U)) :
    (Opens.grothendieckTopology (Proj (grading I))).CoversTop
      (quotientPrincipalPointCommonOpens I U x q f) := by
  apply (Opens.coversTop_iff _ _).mpr
  have hp := (Opens.coversTop_iff _ _).mp
    (PointAdaptedAffineCover.principalOpens_coversTop U x hx hxclosed q f)
  have hc := (Opens.coversTop_iff _ _).mp (quotientCoordinateOpenTop_coversTop I)
  apply top_unique
  intro z hz
  have hzP : z ∈ ⨆ a, PointAdaptedAffineCover.principalOpens U x q f a := by
    rw [hp]; trivial
  have hzC : z ∈ ⨆ b : ULift.{u} σ, quotientCoordinateOpen I b.down := by
    rw [hc]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hzP
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hzC
  exact (le_iSup (quotientPrincipalPointCommonOpens I U x q f) (a, b)) ⟨ha, hb⟩

theorem quotientPrincipalPointCommonOpens_isAffineOpen (I : HomogeneousIdeal AA)
    [IsAffineHom (pullback.diagonal (terminal.from (Proj (grading I))))]
    (U : (Proj (grading I)).Opens) (hU : IsAffineOpen U)
    (x : Proj (grading I)) (q f : Γ(Proj (grading I), U))
    (a : PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x × ULift.{u} σ) :
    IsAffineOpen (quotientPrincipalPointCommonOpens I U x q f a) := by
  apply (PointAdaptedAffineCover.principalOpens_isAffineOpen U hU x q f a.1).inf
  simpa using quotientCoordinateOpen_cech_inter_affine I 0 (fun _ : Fin 1 => a.2.down)

def quotientPrincipalPointCommonToPrincipalChain (I : HomogeneousIdeal AA)
    (U : (Proj (grading I)).Opens) (x : Proj (grading I))
    (q f : Γ(Proj (grading I), U)) :
    sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
        (quotientPrincipalPointCommonOpens I U x q f) ⟶
      sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
        (PointAdaptedAffineCover.principalOpens U x q f) :=
  sectionRepresenterCechRefinement _ _ _ Prod.fst (fun _ => homOfLE inf_le_left)

def quotientPrincipalPointCommonToCoordinateChain (I : HomogeneousIdeal AA)
    (U : (Proj (grading I)).Opens) (x : Proj (grading I))
    (q f : Γ(Proj (grading I), U)) :
    sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
        (quotientPrincipalPointCommonOpens I U x q f) ⟶
      quotientSectionRepresenterCechChain I :=
  sectionRepresenterCechRefinement _ _ _ Prod.snd (fun _ => homOfLE inf_le_right)

set_option backward.isDefEq.respectTransparency false in
/-- Pull back the actual residue cocycle along the common-cover chain map. -/
def quotientPrincipalPointCommonCocycle (I : HomogeneousIdeal AA)
    (U : (Proj (grading I)).Opens) (x : Proj (grading I))
    (q f : Γ(Proj (grading I), U)) (Y : (Proj (grading I)).Modules)
    (z : DegreeTwoCocycle ((sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
      (PointAdaptedAffineCover.principalOpens U x q f)).d 3 2) (Y := Y)) :
    DegreeTwoCocycle ((sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
      (quotientPrincipalPointCommonOpens I U x q f)).d 3 2) (Y := Y) := by
  let r := quotientPrincipalPointCommonToPrincipalChain I U x q f
  exact DegreeTwoCocycle.precompAddHom _ _ (r.f 2) (r.f 3) (r.comm 3 2).symm z

set_option backward.isDefEq.respectTransparency false in
/-- The residue cocycle has exactly the same intrinsic class on the common cover. -/
theorem quotientPrincipalPointCommon_preserves_intrinsic_class
    (I : HomogeneousIdeal AA) [hExt : HasExt.{u} (Proj (grading I)).Modules]
    (U : (Proj (grading I)).Opens) (x : Proj (grading I)) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set (Proj (grading I))))
    (q f : Γ(Proj (grading I), U)) (Y : (Proj (grading I)).Modules)
    (z : DegreeTwoCocycle ((sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
      (PointAdaptedAffineCover.principalOpens U x q f)).d 3 2) (Y := Y)) :
    letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
    schemeCoverDegreeTwoToCohomology (PointAdaptedAffineCover.principalOpens U x q f)
      (PointAdaptedAffineCover.principalOpens_coversTop U x hx hxclosed q f) Y z =
    schemeCoverDegreeTwoToCohomology (quotientPrincipalPointCommonOpens I U x q f)
      (quotientPrincipalPointCommonOpens_coversTop I U x hx hxclosed q f) Y
      (quotientPrincipalPointCommonCocycle I U x q f Y z) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
  exact @schemeCoverDegreeTwoToCohomology_refinement
    (Proj (grading I)) (PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x)
    (PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x × ULift.{u} σ)
    (PointAdaptedAffineCover.principalOpens U x q f)
    (quotientPrincipalPointCommonOpens I U x q f)
    (PointAdaptedAffineCover.principalOpens_coversTop U x hx hxclosed q f)
    (quotientPrincipalPointCommonOpens_coversTop I U x hx hxclosed q f)
    Prod.fst (fun _ => homOfLE inf_le_left) hExt Y z

end PfaffianDescent.ProjectiveNegativeTwist

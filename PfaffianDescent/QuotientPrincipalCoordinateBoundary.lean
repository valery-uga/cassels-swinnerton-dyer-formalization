import PfaffianDescent.QuotientPrincipalCommonExtOneVanishing
import PfaffianDescent.QuotientCoverCohomologyRepresentative
import PfaffianDescent.CechBoundaryDifference

/-! # Coordinate representatives of point cocycles with an actual boundary witness -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {σ : Type} [Finite σ]
local notation "AA" => MvPolynomial.homogeneousSubmodule σ K

set_option backward.isDefEq.respectTransparency false in
def quotientPrincipalPointCommonCoordinateCocycle (I : HomogeneousIdeal AA)
    (U : (Proj (grading I)).Opens) (x : Proj (grading I))
    (q f : Γ(Proj (grading I), U)) (m : ℕ) (z : QuotientCechDegreeTwoCocycle I m) :
    DegreeTwoCocycle ((sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
      (quotientPrincipalPointCommonOpens I U x q f)).d 3 2)
      (Y := sheafOfModules (grading I) m) := by
  let r := quotientPrincipalPointCommonToCoordinateChain I U x q f
  exact DegreeTwoCocycle.precompAddHom _ _ (r.f 2) (r.f 3) (r.comm 3 2).symm z

set_option backward.isDefEq.respectTransparency false in
theorem quotientPrincipalPointCommon_coordinate_preserves_intrinsic_class
    (I : HomogeneousIdeal AA) [hExt : HasExt.{u} (Proj (grading I)).Modules]
    (U : (Proj (grading I)).Opens) (x : Proj (grading I)) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set (Proj (grading I))))
    (q f : Γ(Proj (grading I), U)) (m : ℕ) (z : QuotientCechDegreeTwoCocycle I m) :
    letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
    schemeCoverDegreeTwoToCohomology
      (fun j : ULift.{u} σ => quotientCoordinateOpen I j.down)
      (quotientCoordinateOpenTop_coversTop I) (sheafOfModules (grading I) m) z =
    schemeCoverDegreeTwoToCohomology (quotientPrincipalPointCommonOpens I U x q f)
      (quotientPrincipalPointCommonOpens_coversTop I U x hx hxclosed q f)
      (sheafOfModules (grading I) m)
      (quotientPrincipalPointCommonCoordinateCocycle I U x q f m z) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
  exact @schemeCoverDegreeTwoToCohomology_refinement
    (Proj (grading I)) (ULift.{u} σ)
    (PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x × ULift.{u} σ)
    (fun j : ULift.{u} σ => quotientCoordinateOpen I j.down)
    (quotientPrincipalPointCommonOpens I U x q f)
    (quotientCoordinateOpenTop_coversTop I)
    (quotientPrincipalPointCommonOpens_coversTop I U x hx hxclosed q f)
    Prod.snd (fun _ => homOfLE inf_le_right) hExt (sheafOfModules (grading I) m) z

set_option backward.isDefEq.respectTransparency false in
/-- Construct a coordinate representative with equality of the actual
common-cover intrinsic classes. -/
theorem exists_quotient_coordinate_common_class_of_principal
    (I : HomogeneousIdeal AA) [hExt : HasExt.{u} (Proj (grading I)).Modules]
    (U : (Proj (grading I)).Opens) (x : Proj (grading I)) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set (Proj (grading I))))
    (q f : Γ(Proj (grading I), U)) (m : ℕ)
    (z : DegreeTwoCocycle ((sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
      (PointAdaptedAffineCover.principalOpens U x q f)).d 3 2)
      (Y := sheafOfModules (grading I) m)) :
    letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
    ∃ w : QuotientCechDegreeTwoCocycle I m,
      schemeCoverDegreeTwoToCohomology (quotientPrincipalPointCommonOpens I U x q f)
        (quotientPrincipalPointCommonOpens_coversTop I U x hx hxclosed q f)
        (sheafOfModules (grading I) m)
        (quotientPrincipalPointCommonCocycle I U x q f (sheafOfModules (grading I) m) z) =
      schemeCoverDegreeTwoToCohomology (quotientPrincipalPointCommonOpens I U x q f)
        (quotientPrincipalPointCommonOpens_coversTop I U x hx hxclosed q f)
        (sheafOfModules (grading I) m)
        (quotientPrincipalPointCommonCoordinateCocycle I U x q f m w) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
  let Y := sheafOfModules (grading I) m
  obtain ⟨w, hw⟩ := (@quotient_coordinateCover_intrinsic_surjective
    K inferInstance σ inferInstance I hExt m)
      (schemeCoverDegreeTwoToCohomology (PointAdaptedAffineCover.principalOpens U x q f)
        (PointAdaptedAffineCover.principalOpens_coversTop U x hx hxclosed q f) Y z)
  have hp := quotientPrincipalPointCommon_preserves_intrinsic_class (hExt := hExt) I U x hx hxclosed q f Y z
  have hc := quotientPrincipalPointCommon_coordinate_preserves_intrinsic_class (hExt := hExt) I U x hx hxclosed q f m w
  exact ⟨w, hp.symm.trans (hw.symm.trans hc)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Boundary detection on the actual common cover with its acyclicity
proved from the affine geometry. -/
theorem quotientPrincipalPointCommon_class_eq_iff_boundary
    (I : HomogeneousIdeal AA) [hExt : HasExt.{u} (Proj (grading I)).Modules]
    [IsAffineHom (pullback.diagonal (terminal.from (Proj (grading I))))]
    (U : (Proj (grading I)).Opens) (hU : IsAffineOpen U)
    (x : Proj (grading I)) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set (Proj (grading I))))
    (q f : Γ(Proj (grading I), U)) (m : ℕ)
    (z z' : DegreeTwoCocycle ((sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
      (quotientPrincipalPointCommonOpens I U x q f)).d 3 2)
      (Y := sheafOfModules (grading I) m)) :
    letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
    schemeCoverDegreeTwoToCohomology (quotientPrincipalPointCommonOpens I U x q f)
      (quotientPrincipalPointCommonOpens_coversTop I U x hx hxclosed q f)
      (sheafOfModules (grading I) m) z =
    schemeCoverDegreeTwoToCohomology (quotientPrincipalPointCommonOpens I U x q f)
      (quotientPrincipalPointCommonOpens_coversTop I U x hx hxclosed q f)
      (sheafOfModules (grading I) m) z' ↔
    ∃ b : (sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
        (quotientPrincipalPointCommonOpens I U x q f)).X 1 ⟶ sheafOfModules (grading I) m,
      (sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
        (quotientPrincipalPointCommonOpens I U x q f)).d 2 1 ≫ b = z.1 - z'.1 := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
  let Y := sheafOfModules (grading I) m
  let W := quotientPrincipalPointCommonOpens I U x q f
  let hW := quotientPrincipalPointCommonOpens_coversTop I U x hx hxclosed q f
  let hz : Subsingleton (Ext.{u} (C := (Proj (grading I)).Modules)
      ((sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf W).X 0) Y 1) :=
    quotientPrincipalPointCommon_degree_zero_ext_one_subsingleton I U hU x q f m
  exact @schemeCoverDegreeTwoToCohomology_eq_iff_boundary_difference
    (Proj (grading I))
    (PointAdaptedAffineCover.PrincipalIndex (Proj (grading I)) x × ULift.{u} σ)
    W hW hExt Y hz z z'

set_option backward.isDefEq.respectTransparency false in
/-- Every principal point cocycle has a projective coordinate representative
whose actual common-cover difference is an actual degree-one boundary.
Neither the representative nor its boundary is a hypothesis. -/
theorem exists_quotient_coordinate_cocycle_boundary_of_principal
    (I : HomogeneousIdeal AA) [hExt : HasExt.{u} (Proj (grading I)).Modules]
    [IsAffineHom (pullback.diagonal (terminal.from (Proj (grading I))))]
    (U : (Proj (grading I)).Opens) (hU : IsAffineOpen U)
    (x : Proj (grading I)) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set (Proj (grading I))))
    (q f : Γ(Proj (grading I), U)) (m : ℕ)
    (z : DegreeTwoCocycle ((sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
      (PointAdaptedAffineCover.principalOpens U x q f)).d 3 2)
      (Y := sheafOfModules (grading I) m)) :
    ∃ w : QuotientCechDegreeTwoCocycle I m,
      Nonempty (DegreeTwoBoundaryDifference
        (sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
          (quotientPrincipalPointCommonOpens I U x q f))
        (sheafOfModules (grading I) m)
        (quotientPrincipalPointCommonCocycle I U x q f (sheafOfModules (grading I) m) z)
        (quotientPrincipalPointCommonCoordinateCocycle I U x q f m w)) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
  obtain ⟨w, hw⟩ := exists_quotient_coordinate_common_class_of_principal
    (hExt := hExt) I U x hx hxclosed q f m z
  obtain ⟨b, hb⟩ := (quotientPrincipalPointCommon_class_eq_iff_boundary
    (hExt := hExt) I U hU x hx hxclosed q f m
    (quotientPrincipalPointCommonCocycle I U x q f (sheafOfModules (grading I) m) z)
    (quotientPrincipalPointCommonCoordinateCocycle I U x q f m w)).mp hw
  exact ⟨w, ⟨⟨b, hb⟩⟩⟩

end PfaffianDescent.ProjectiveNegativeTwist

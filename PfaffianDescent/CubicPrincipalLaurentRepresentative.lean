import PfaffianDescent.CubicSurfaceCechLaurentEvaluation
import PfaffianDescent.QuotientPrincipalCoordinateBoundary

/-! # Laurent evaluation of the actual principal point-cover class -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentCechExact
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- An actual principal-cover class admits a coordinate representative
and the native Laurent formula. -/
theorem exists_cubic_principal_laurent_representative
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [IsAffineHom (pullback.diagonal (terminal.from (Proj (grading (equationIdeal p hp)))))]
    (U : (Proj (grading (equationIdeal p hp))).Opens) (hU : IsAffineOpen U)
    (x : Proj (grading (equationIdeal p hp))) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set (Proj (grading (equationIdeal p hp)))))
    (q f : Γ(Proj (grading (equationIdeal p hp)), U))
    (z : DegreeTwoCocycle ((sectionRepresenterCechChain
      (Proj (grading (equationIdeal p hp))).ringCatSheaf
      (PointAdaptedAffineCover.principalOpens U x q f)).d 3 2)
      (Y := sheafOfModules (grading (equationIdeal p hp)) 3)) :
    letI : HasExt.{u} (SheafOfModules.{u}
      (Proj (grading (equationIdeal p hp))).ringCatSheaf) := hExt
    ∃ (w : QuotientCechDegreeTwoCocycle (equationIdeal p hp) 3)
      (d : CubicNegativeThreeCechLift K p hp (cubicSurfaceCocycleToPushforward K p hp 3 w)),
      cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
        (schemeCoverDegreeTwoToCohomology (PointAdaptedAffineCover.principalOpens U x q f)
          (PointAdaptedAffineCover.principalOpens_coversTop U x hx hxclosed q f)
          (sheafOfModules (grading (equationIdeal p hp)) 3) z) =
      (p3QuadraticDualCoordinateEquiv K).symm
        (p3NegativeSixTopResidueCoordinates K (cubicNegativeThreeLiftRawBoundary K p hp
          (cubicSurfaceCocycleToPushforward K p hp 3 w) d)) := by
  letI : HasExt.{u} (SheafOfModules.{u}
      (Proj (grading (equationIdeal p hp))).ringCatSheaf) := hExt
  obtain ⟨w, hw⟩ := exists_quotient_coordinate_common_class_of_principal
    (hExt := hExt) (equationIdeal p hp) U x hx hxclosed q f 3 z
  obtain ⟨d⟩ := exists_cubic_negative_three_cech_lift K p hp hp0
    (cubicSurfaceCocycleToPushforward K p hp 3 w)
  refine ⟨w, d, ?_⟩
  have hpclass := quotientPrincipalPointCommon_preserves_intrinsic_class
    (hExt := hExt) (equationIdeal p hp) U x hx hxclosed q f
    (sheafOfModules (grading (equationIdeal p hp)) 3) z
  have hcclass := quotientPrincipalPointCommon_coordinate_preserves_intrinsic_class
    (hExt := hExt) (equationIdeal p hp) U x hx hxclosed q f 3 w
  have heq := hpclass.trans (hw.trans hcclass.symm)
  rw [heq, schemeCoverDegreeTwoToCohomology_quotient_coordinateCover]
  exact cubicSurface_negative_three_dual_eq_raw_residue_coordinates K p hp hp0 w d

end PfaffianDescent.ProjectiveNegativeTwist

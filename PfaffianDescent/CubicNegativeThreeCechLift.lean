import PfaffianDescent.CechCoefficientLiftConstruction
import PfaffianDescent.VoisinCubicPushforwardCechExtComparison

/-! # Constructed coefficient lifts for the actual cubic restriction sequence -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Actual lift data for O(-6) -> O(-3) -> i_*O_S(-3). -/
abbrev CubicNegativeThreeCechLift
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 3) :=
  CechCoefficientLift (p3SectionRepresenterCechChain K)
    (hypersurfaceTwistRestrictionSequence p hp 3) z

set_option backward.isDefEq.respectTransparency false in
/-- The proved ambient acyclicity constructs the lift and its actual
negative-six degree-three cocycle; no lift is supplied as a hypothesis. -/
theorem exists_cubic_negative_three_cech_lift
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 3) :
    Nonempty (CubicNegativeThreeCechLift K p hp z) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let S := hypersurfaceTwistRestrictionSequence p hp 3
  have hS : S.ShortExact := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 3
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      ((p3SectionRepresenterCechChain K).X 2) S.X₁ 1) :=
    (p3_sectionRepresenterCechChain_ext_one_two_three_subsingleton K 6 2).1
  exact exists_cech_coefficient_lift (p3SectionRepresenterCechChain K) S hS z
end PfaffianDescent.ProjectiveNegativeTwist

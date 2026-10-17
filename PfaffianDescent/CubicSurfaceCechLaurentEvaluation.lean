import PfaffianDescent.CubicIntrinsicRepresentativeTransport
import PfaffianDescent.QuotientCoverIntrinsicComparison

/-! # Intrinsic surface Cech representatives and the native Laurent formula -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentCechExact
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Transport the actual coordinate-cover cocycle into the ambient
pushforward Cech complex, using the proved section identifications. -/
def cubicSurfaceCocycleToPushforward
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ)
    (w : QuotientCechDegreeTwoCocycle (equationIdeal p hp) m) :
    CubicPushforwardAbstractDegreeTwoCocycle K p hp m :=
  (cubicPushforwardAbstractCocycleEquivRaw K p hp m).symm
    ((cubicPushforwardDegreeTwoCocycleEquivQuotient K p hp m).symm
      (cubicQuotientDegreeTwoCocycleEquivRaw K (equationIdeal p hp) m w))

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic comparison acts on the actual surface coordinate-cover
class as the corresponding ambient cocycle class, with no comparison premise. -/
theorem cubicIntrinsicCohomologyTwoEquivPushforward_coordinate_cocycle
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [IsDomain (CoordinateRing (equationIdeal p hp))] (m : ℕ)
    (w : QuotientCechDegreeTwoCocycle (equationIdeal p hp) m) :
    cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 m
      ((Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules)
        (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)).inv).comp
        (quotientCechDegreeTwoToAugmentedExt (equationIdeal p hp) m w) (zero_add 2)) =
    (Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
      (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m
        (cubicSurfaceCocycleToPushforward K p hp m w)) (zero_add 2) := by
  let r := (cubicQuotientDegreeTwoCocycleEquivRaw K (equationIdeal p hp) m) w
  let a := (cubicPushforwardDegreeTwoCocycleEquivQuotient K p hp m).symm r
  have hi : cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m a =
      quotientCechDegreeTwoToAugmentedExt (equationIdeal p hp) m w := by
    change quotientCechDegreeTwoToAugmentedExt (equationIdeal p hp) m
      ((cubicQuotientDegreeTwoCocycleEquivRaw K (equationIdeal p hp) m).symm
        ((cubicPushforwardDegreeTwoCocycleEquivQuotient K p hp m) a)) = _
    rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  have ht := cubicIntrinsicCohomologyTwoEquivPushforward_raw K p hp hp0 m a
  rw [hi] at ht
  exact ht

set_option backward.isDefEq.respectTransparency false in
/-- The full intrinsic quadratic-dual vector of an actual surface cocycle
is the Laurent residue vector of its constructed ambient boundary. -/
theorem cubicSurface_negative_three_dual_eq_raw_residue_coordinates
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (w : QuotientCechDegreeTwoCocycle (equationIdeal p hp) 3)
    (d : CubicNegativeThreeCechLift K p hp (cubicSurfaceCocycleToPushforward K p hp 3 w)) :
    cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
      ((Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules)
        (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)).inv).comp
        (quotientCechDegreeTwoToAugmentedExt (equationIdeal p hp) 3 w) (zero_add 2)) =
    (p3QuadraticDualCoordinateEquiv K).symm
      (p3NegativeSixTopResidueCoordinates K
        (cubicNegativeThreeLiftRawBoundary K p hp
          (cubicSurfaceCocycleToPushforward K p hp 3 w) d)) := by
  change cubicPushforwardNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
    (cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 3 _) = _
  rw [cubicIntrinsicCohomologyTwoEquivPushforward_coordinate_cocycle]
  exact cubicNegativeThree_dual_quadratic_eq_raw_residue_coordinates K p hp hp0 _ d

end PfaffianDescent.ProjectiveNegativeTwist

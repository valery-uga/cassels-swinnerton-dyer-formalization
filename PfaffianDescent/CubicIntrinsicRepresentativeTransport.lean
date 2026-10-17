import PfaffianDescent.CubicCechLaurentEvaluation

/-! # Evaluation of the intrinsic cubic comparison on actual representatives -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u v

private theorem quotientAddEquivOfEq_mk {G : Type u} [AddCommGroup G]
    (N N' : AddSubgroup G) (h : N = N') (g : G) :
    QuotientAddGroup.quotientAddEquivOfEq h (QuotientAddGroup.mk g) =
      (QuotientAddGroup.mk g : G ⧸ N') := by
  subst N'
  rfl

namespace ProjectiveNegativeTwist
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic quotient equivalence sends a literal raw representative
 to its Cech class with the canonical unit source. -/
theorem cubicPushforwardRaw_intrinsic_quotient_mk
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules] (m : ℕ)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp m) :
    cubicPushforwardRawDegreeTwoQuotientEquivCohomologyTwo K p hp m
      (QuotientAddGroup.mk w) =
    (extPrecompIsoOfIso
      (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)))
      (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m w) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic-to-pushforward comparison transports an actual raw
representative, including both canonical unit-source maps. -/
theorem cubicIntrinsicCohomologyTwoEquivPushforward_raw
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [IsDomain (CoordinateRing (equationIdeal p hp))] (m : ℕ)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp m) :
    cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 m
      ((extPrecompIsoOfIso
        (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)))
        (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m w)) =
    (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K))
      (cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp m w) := by
  let E := cubicPushforwardRawDegreeTwoQuotientEquivCohomologyTwo K p hp m
  let x : CubicPushforwardRawDegreeTwoCocycle K p hp m ⧸
      (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m).ker :=
    QuotientAddGroup.mk w
  have hx : E.symm ((extPrecompIsoOfIso
      (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)))
      (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m w)) = x := by
    rw [← cubicPushforwardRaw_intrinsic_quotient_mk K p hp m w]
    exact E.symm_apply_apply x
  change cubicPushforwardRawDegreeTwoQuotientEquivAmbientCohomologyTwo K p hp hp0 m
    (QuotientAddGroup.quotientAddEquivOfEq
      (cubicPushforwardRaw_intrinsicKer_eq_ambientKer K p hp hp0 m)
      (E.symm _)) = _
  rw [hx, quotientAddEquivOfEq_mk]
  rfl

end ProjectiveNegativeTwist
end PfaffianDescent

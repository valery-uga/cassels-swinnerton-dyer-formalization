import PfaffianDescent.P3CanonicalTraceScalar
import PfaffianDescent.CubicQuadraticCanonicalTrace

/-! # Actual scalar multiplication on the cubic canonical restriction sequence -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

def cubicScalarHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (c : K) :
    grading (equationIdeal p hp) 0 :=
  ⟨quotientGradedRingHom (equationIdeal p hp) (p3ScalarHomogeneous K c),
    (quotientGradedRingHom (equationIdeal p hp)).2 (p3ScalarHomogeneous K c).2⟩

set_option backward.isDefEq.respectTransparency false in
theorem cubicScalarMultiplication_left_square
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (c : K) :
    mulHomogeneous PS ⟨p, hp⟩ 1 ≫ mulHomogeneous PS (p3ScalarHomogeneous K c) 1 =
      mulHomogeneous PS (p3ScalarHomogeneous K c) 4 ≫ mulHomogeneous PS ⟨p, hp⟩ 1 := by
  ext U z
  apply Subtype.ext
  funext x
  change algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (MvPolynomial.C c) *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) p * z.1 x) =
    algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) p *
      (algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (MvPolynomial.C c) * z.1 x)
  ring

set_option backward.isDefEq.respectTransparency false in
theorem cubicScalarMultiplication_right_square
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (c : K) :
    mulHomogeneous PS (p3ScalarHomogeneous K c) 1 ≫ hypersurfaceTwistToPushforward p hp 1 =
      hypersurfaceTwistToPushforward p hp 1 ≫
        (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
          (mulHomogeneous (grading (equationIdeal p hp)) (cubicScalarHomogeneous K p hp c) 1) := by
  exact gradedRingHomTwistToPushforward_mulHomogeneous PS (grading (equationIdeal p hp))
    (quotientGradedRingHom (equationIdeal p hp))
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp)) (p3ScalarHomogeneous K c) 1

set_option backward.isDefEq.respectTransparency false in
def cubicScalarRestrictionDiagram
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal p hp))] (c : K) :
    hypersurfaceTwistRestrictionSequence p hp 1 ⟶ hypersurfaceTwistRestrictionSequence p hp 1 where
  τ₁ := mulHomogeneous PS (p3ScalarHomogeneous K c) 4
  τ₂ := mulHomogeneous PS (p3ScalarHomogeneous K c) 1
  τ₃ := (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
    (mulHomogeneous (grading (equationIdeal p hp)) (cubicScalarHomogeneous K p hp c) 1)
  comm₁₂ := (cubicScalarMultiplication_left_square K p hp c).symm
  comm₂₃ := cubicScalarMultiplication_right_square K p hp c

set_option backward.isDefEq.respectTransparency false in
theorem cubicScalarRestriction_connecting_naturality
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] [HasExt.{u} (Proj PS).Modules]
    (c : K) (z : schemeModuleCohomology (Proj PS) (cubicPushforwardTwist K p hp 1) 2) :
    cubicPushforwardNegativeOneCohomologyTwoEquivAmbientNegativeFourThree K p hp hp0
        (z.comp (Ext.mk₀ (cubicScalarRestrictionDiagram K p hp c).τ₃) (add_zero 2)) =
      (cubicPushforwardNegativeOneCohomologyTwoEquivAmbientNegativeFourThree K p hp hp0 z).comp
        (Ext.mk₀ (mulHomogeneous PS (p3ScalarHomogeneous K c) 4)) (add_zero 3) := by
  let hs := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1
  let phi := cubicScalarRestrictionDiagram K p hp c
  have hn := hs.extClass_naturality hs phi
  change hs.extClass.comp (Ext.mk₀ phi.τ₁) (add_zero 1) =
    (Ext.mk₀ phi.τ₃).comp hs.extClass (zero_add 1) at hn
  change (z.comp (Ext.mk₀ phi.τ₃) (add_zero 2)).comp hs.extClass (show 2 + 1 = 3 by rfl) =
    (z.comp hs.extClass (show 2 + 1 = 3 by rfl)).comp (Ext.mk₀ phi.τ₁) (add_zero 3)
  rw [Ext.comp_assoc_of_second_deg_zero _ _ _ rfl,
    Ext.comp_assoc_of_third_deg_zero _ _ _ rfl, ← hn]

set_option backward.isDefEq.respectTransparency false in
/-- The actual pushforward canonical trace respects scalar multiplication. -/
theorem cubicPushforwardCanonicalTrace_scalar_multiplication
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] [HasExt.{u} (Proj PS).Modules]
    (c : K) (z : schemeModuleCohomology (Proj PS) (cubicPushforwardTwist K p hp 1) 2) :
    cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0
        (z.comp (Ext.mk₀ (cubicScalarRestrictionDiagram K p hp c).τ₃) (add_zero 2)) =
      c * cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0 z := by
  rw [cubicPushforwardNegativeOne_trace_apply_connecting,
    cubicPushforwardNegativeOne_trace_apply_connecting]
  exact (congrArg (p3NegativeFourCohomologyThreeTraceEquiv K)
    (cubicScalarRestriction_connecting_naturality K p hp hp0 c z)).trans
    (p3NegativeFourCohomologyTrace_scalar_multiplication K c _)

end PfaffianDescent.ProjectiveNegativeTwist

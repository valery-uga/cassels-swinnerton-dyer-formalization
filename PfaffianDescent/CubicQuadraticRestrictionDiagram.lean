import PfaffianDescent.GradedTwistMultiplicationRestriction
import PfaffianDescent.CubicQuadraticMultiplicationSquare
import PfaffianDescent.CubicCanonicalCohomologyTrace

/-! # The actual cubic restriction diagram under quadratic multiplication -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

def cubicQuadraticRestriction (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : homogeneousSubmodule (Fin 4) K 2) : grading (equationIdeal p hp) 2 :=
  ⟨quotientGradedRingHom (equationIdeal p hp) q,
    (quotientGradedRingHom (equationIdeal p hp)).2 q.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The right square uses the ACTUAL pushforward of the surface
multiplication map and the ACTUAL restriction morphisms. -/
theorem cubicQuadraticMultiplication_right_square
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : homogeneousSubmodule (Fin 4) K 2) :
    mulHomogeneous PS q 1 ≫ hypersurfaceTwistToPushforward p hp 1 =
    hypersurfaceTwistToPushforward p hp 3 ≫
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
        (mulHomogeneous (grading (equationIdeal p hp)) (cubicQuadraticRestriction K p hp q) 1) := by
  exact gradedRingHomTwistToPushforward_mulHomogeneous PS (grading (equationIdeal p hp))
    (quotientGradedRingHom (equationIdeal p hp))
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp)) q 1

set_option backward.isDefEq.respectTransparency false in
/-- Quadratic multiplication is an actual morphism between the cubic
negative-three and negative-one restriction short complexes. -/
def cubicQuadraticRestrictionDiagram
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (q : homogeneousSubmodule (Fin 4) K 2) :
    hypersurfaceTwistRestrictionSequence p hp 3 ⟶ hypersurfaceTwistRestrictionSequence p hp 1 where
  τ₁ := mulHomogeneous PS q 4
  τ₂ := mulHomogeneous PS q 1
  τ₃ := (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
    (mulHomogeneous (grading (equationIdeal p hp)) (cubicQuadraticRestriction K p hp q) 1)
  comm₁₂ := (cubicQuadraticMultiplication_left_square K p hp q).symm
  comm₂₃ := cubicQuadraticMultiplication_right_square K p hp q

set_option backward.isDefEq.respectTransparency false in
/-- The two ACTUAL cubic connecting maps commute with quadratic
multiplication. Naturality is proved from the constructed short-complex
morphism rather than supplied as a compatibility hypothesis. -/
theorem cubicQuadraticRestriction_connecting_naturality
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules] (q : homogeneousSubmodule (Fin 4) K 2)
    (z : schemeModuleCohomology (Proj PS) (cubicPushforwardTwist K p hp 3) 2) :
    cubicPushforwardNegativeOneCohomologyTwoEquivAmbientNegativeFourThree K p hp hp0
      (z.comp (Ext.mk₀ (cubicQuadraticRestrictionDiagram K p hp q).τ₃) (add_zero 2)) =
    (cubicPushforwardNegativeThreeCohomologyTwoEquivAmbientNegativeSixThree K p hp hp0 z).comp
      (Ext.mk₀ (mulHomogeneous PS q 4)) (add_zero 3) := by
  let h3 := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 3
  let h1 := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1
  let phi := cubicQuadraticRestrictionDiagram K p hp q
  have hn := h3.extClass_naturality h1 phi
  change h3.extClass.comp (Ext.mk₀ phi.τ₁) (add_zero 1) =
    (Ext.mk₀ phi.τ₃).comp h1.extClass (zero_add 1) at hn
  change (z.comp (Ext.mk₀ phi.τ₃) (add_zero 2)).comp h1.extClass (show 2 + 1 = 3 by rfl) =
    (z.comp h3.extClass (show 2 + 1 = 3 by rfl)).comp (Ext.mk₀ phi.τ₁) (add_zero 3)
  rw [Ext.comp_assoc_of_second_deg_zero _ _ _ rfl,
    Ext.comp_assoc_of_third_deg_zero _ _ _ rfl, ← hn]

end PfaffianDescent.ProjectiveNegativeTwist

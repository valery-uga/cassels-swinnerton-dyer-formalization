import PfaffianDescent.CubicPushforwardMultiplicationExtNaturality
import PfaffianDescent.ExtSourceIsoCoefficientNaturality
import PfaffianDescent.CubicIntrinsicRepresentativeTransport

/-! # Actual multiplication through the intrinsic/pushforward cohomology comparison -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
theorem cubicPushforwardRawDegreeTwoToIntrinsicExt_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp (m + d)) :
    (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp (m + d) w).comp
        (Ext.mk₀ (mulHomogeneous (grading (equationIdeal p hp)) q m)) (add_zero 2) =
      cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m
        (cubicPushforwardRawCocycleMultiply K p hp m d q w) := by
  change (cubicQuotientRawDegreeTwoToAugmentedExtHom K (equationIdeal p hp) (m + d)
      (cubicPushforwardRawCocycleToQuotient K p hp (m + d) w)).comp _ _ =
    cubicQuotientRawDegreeTwoToAugmentedExtHom K (equationIdeal p hp) m
      (cubicPushforwardRawCocycleToQuotient K p hp m _)
  rw [cubicPushforwardRawCocycleMultiply_toQuotient]
  exact cubicQuotientRawDegreeTwoToAugmentedExt_mulHomogeneous K p hp m d q _

set_option backward.isDefEq.respectTransparency false in
theorem cubicPushforwardRaw_intrinsic_unit_class_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp (m + d)) :
    ((extPrecompIsoOfIso (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)))
      (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp (m + d) w)).comp
        (Ext.mk₀ (mulHomogeneous (grading (equationIdeal p hp)) q m)) (add_zero 2) =
    (extPrecompIsoOfIso (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)))
      (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp m
        (cubicPushforwardRawCocycleMultiply K p hp m d q w)) := by
  rw [extPrecompIsoOfIso_postcomp,
    cubicPushforwardRawDegreeTwoToIntrinsicExt_mulHomogeneous]

set_option backward.isDefEq.respectTransparency false in
theorem cubicPushforwardRaw_ambient_unit_class_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj PS).Modules]
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp (m + d)) :
    ((extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K))
      (cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp (m + d) w)).comp
        (Ext.mk₀ ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
          (mulHomogeneous (grading (equationIdeal p hp)) q m))) (add_zero 2) =
    (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K))
      (cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp m
        (cubicPushforwardRawCocycleMultiply K p hp m d q w)) := by
  rw [extPrecompIsoOfIso_postcomp,
    cubicPushforwardRawDegreeTwoToAmbientExt_mulHomogeneous]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication commutes with the actual intrinsic-to-pushforward
cohomology equivalence, proved using its common raw representative. -/
theorem cubicIntrinsicCohomologyTwoEquivPushforward_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (z : schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
      (sheafOfModules (grading (equationIdeal p hp)) (m + d)) 2) :
    cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 m
        (z.comp (Ext.mk₀ (mulHomogeneous (grading (equationIdeal p hp)) q m)) (add_zero 2)) =
      (cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 (m + d) z).comp
        (Ext.mk₀ ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
          (mulHomogeneous (grading (equationIdeal p hp)) q m))) (add_zero 2) := by
  let E : Ext.{u} (quotientSectionRepresenterCechTarget (equationIdeal p hp))
      (sheafOfModules (grading (equationIdeal p hp)) (m + d)) 2 ≃+
      schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
        (sheafOfModules (grading (equationIdeal p hp)) (m + d)) 2 :=
    extPrecompIsoOfIso (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp))
  obtain ⟨a, rfl⟩ := E.surjective z
  obtain ⟨w, rfl⟩ := cubicPushforwardRawDegreeTwoToAugmentedExt_surjective K p hp (m + d) a
  change cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 m
      (((extPrecompIsoOfIso (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)))
        (cubicPushforwardRawDegreeTwoToAugmentedExtHom K p hp (m + d) w)).comp _ _) = _
  rw [cubicPushforwardRaw_intrinsic_unit_class_mulHomogeneous K p hp m d q w,
    cubicIntrinsicCohomologyTwoEquivPushforward_raw,
    cubicIntrinsicCohomologyTwoEquivPushforward_raw,
    cubicPushforwardRaw_ambient_unit_class_mulHomogeneous]

end PfaffianDescent.ProjectiveNegativeTwist

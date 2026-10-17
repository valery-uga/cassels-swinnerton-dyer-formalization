import PfaffianDescent.CubicCechMultiplicationExtNaturality

/-! # Multiplication on actual ambient pushforward classes -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

def cubicPushforwardRawCocycleMultiply
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp (m + d)) :
    CubicPushforwardRawDegreeTwoCocycle K p hp m :=
  ⟨(cubicPushforwardCechMultiplication K p hp m d q).f 2 w.1, by
    change (cubicPushforwardNegativeTwistCechComplex K p hp m).d 2 3
      ((cubicPushforwardCechMultiplication K p hp m d q).f 2 w.1) = 0
    have h := CategoryTheory.congr_fun
      ((cubicPushforwardCechMultiplication K p hp m d q).comm 2 3) w.1
    have hw : (cubicPushforwardNegativeTwistCechComplex K p hp (m + d)).d 2 3 w.1 = 0 := w.2
    simpa only [ConcreteCategory.comp_apply, hw, map_zero] using h⟩

theorem cubicPushforwardRawCocycleMultiply_toQuotient
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp (m + d)) :
    cubicPushforwardRawCocycleToQuotient K p hp m (cubicPushforwardRawCocycleMultiply K p hp m d q w) =
      cubicIntrinsicRawCocycleMultiply K p hp m d q
        (cubicPushforwardRawCocycleToQuotient K p hp (m + d) w) := by
  apply Subtype.ext
  exact CategoryTheory.congr_fun (cubicPushforwardCechTermIso_mulHomogeneous K p hp m d 2 q) w.1

set_option backward.isDefEq.respectTransparency false in
theorem cubicPushforwardAbstractCocycleEquivRaw_symm_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp (m + d)) :
    (cubicPushforwardAbstractCocycleEquivRaw K p hp m).symm
        (cubicPushforwardRawCocycleMultiply K p hp m d q w) =
      DegreeTwoCocycle.postcompAddHom ((p3SectionRepresenterCechChain K).d 3 2)
        ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
          (mulHomogeneous (grading (equationIdeal p hp)) q m))
        ((cubicPushforwardAbstractCocycleEquivRaw K p hp (m + d)).symm w) := by
  apply Subtype.ext
  exact smallCoverSectionHomEquiv_symm_coefficientMap (Proj PS).ringCatSheaf (p3StandardOpen K)
    ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
      (mulHomogeneous (grading (equationIdeal p hp)) q m)) 2 w.1

set_option backward.isDefEq.respectTransparency false in
theorem cubicPushforwardAbstractDegreeTwoToAugmentedExt_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hExt : HasExt.{u} (Proj PS).Modules]
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp (m + d)) :
    (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp (m + d) z).comp
        (Ext.mk₀ ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
          (mulHomogeneous (grading (equationIdeal p hp)) q m))) (add_zero 2) =
      cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m
        (DegreeTwoCocycle.postcompAddHom ((p3SectionRepresenterCechChain K).d 3 2)
          ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
            (mulHomogeneous (grading (equationIdeal p hp)) q m)) z) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  unfold cubicPushforwardAbstractDegreeTwoToAugmentedExt
  apply augmentedChainDegreeTwoToExt_postcomp

set_option backward.isDefEq.respectTransparency false in
theorem cubicPushforwardRawDegreeTwoToAmbientExt_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj PS).Modules]
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicPushforwardRawDegreeTwoCocycle K p hp (m + d)) :
    (cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp (m + d) w).comp
        (Ext.mk₀ ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
          (mulHomogeneous (grading (equationIdeal p hp)) q m))) (add_zero 2) =
      cubicPushforwardRawDegreeTwoToAmbientExtHom K p hp m
        (cubicPushforwardRawCocycleMultiply K p hp m d q w) := by
  change (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp (m + d)
      ((cubicPushforwardAbstractCocycleEquivRaw K p hp (m + d)).symm w)).comp _ _ =
    cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp m
      ((cubicPushforwardAbstractCocycleEquivRaw K p hp m).symm _)
  rw [cubicPushforwardAbstractDegreeTwoToAugmentedExt_mulHomogeneous,
    cubicPushforwardAbstractCocycleEquivRaw_symm_mulHomogeneous]

end PfaffianDescent.ProjectiveNegativeTwist

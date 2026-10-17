import PfaffianDescent.CubicCechCoefficientMultiplication
import PfaffianDescent.DegreeTwoResolutionNaturality

/-! # Actual cubic Cech multiplication commutes with intrinsic Ext classes -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

def cubicIntrinsicRawCocycleMultiply
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicQuotientRawDegreeTwoCocycle K (equationIdeal p hp) (m + d)) :
    CubicQuotientRawDegreeTwoCocycle K (equationIdeal p hp) m :=
  ⟨(cubicIntrinsicCechMultiplication K p hp m d q).f 2 w.1, by
    change (quotientNegativeTwistCechComplex (equationIdeal p hp) m).d 2 3
      ((cubicIntrinsicCechMultiplication K p hp m d q).f 2 w.1) = 0
    have h := CategoryTheory.congr_fun
      ((cubicIntrinsicCechMultiplication K p hp m d q).comm 2 3) w.1
    have hw : (quotientNegativeTwistCechComplex (equationIdeal p hp) (m + d)).d 2 3 w.1 = 0 := w.2
    simpa only [ConcreteCategory.comp_apply, hw, map_zero] using h⟩

set_option backward.isDefEq.respectTransparency false in
theorem cubicQuotientAbstractCocycleOfRaw_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicQuotientRawDegreeTwoCocycle K (equationIdeal p hp) (m + d)) :
    cubicQuotientAbstractCocycleOfRaw K (equationIdeal p hp) m
        (cubicIntrinsicRawCocycleMultiply K p hp m d q w) =
      DegreeTwoCocycle.postcompAddHom ((quotientSectionRepresenterCechChain (equationIdeal p hp)).d 3 2)
        (mulHomogeneous (grading (equationIdeal p hp)) q m)
        (cubicQuotientAbstractCocycleOfRaw K (equationIdeal p hp) (m + d) w) := by
  apply Subtype.ext
  exact smallCoverSectionHomEquiv_symm_coefficientMap
    (Proj (grading (equationIdeal p hp))).ringCatSheaf
    (quotientCoordinateOpen (equationIdeal p hp))
    (mulHomogeneous (grading (equationIdeal p hp)) q m) 2 w.1

set_option backward.isDefEq.respectTransparency false in
theorem quotientCechDegreeTwoToAugmentedExt_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (z : QuotientCechDegreeTwoCocycle (equationIdeal p hp) (m + d)) :
    (quotientCechDegreeTwoToAugmentedExt (equationIdeal p hp) (m + d) z).comp
        (Ext.mk₀ (mulHomogeneous (grading (equationIdeal p hp)) q m)) (add_zero 2) =
      quotientCechDegreeTwoToAugmentedExt (equationIdeal p hp) m
        (DegreeTwoCocycle.postcompAddHom ((quotientSectionRepresenterCechChain (equationIdeal p hp)).d 3 2)
          (mulHomogeneous (grading (equationIdeal p hp)) q m) z) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading (equationIdeal p hp))).ringCatSheaf) := hExt
  letI : Epi (quotientSectionRepresenterCechAugmentation (equationIdeal p hp)) :=
    (quotientSectionRepresenterCech_augmentation_exact_and_epi (equationIdeal p hp)).2
  unfold quotientCechDegreeTwoToAugmentedExt
  apply augmentedChainDegreeTwoToExt_postcomp

set_option backward.isDefEq.respectTransparency false in
theorem cubicQuotientRawDegreeTwoToAugmentedExt_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (m d : ℕ) (q : grading (equationIdeal p hp) d)
    (w : CubicQuotientRawDegreeTwoCocycle K (equationIdeal p hp) (m + d)) :
    (cubicQuotientRawDegreeTwoToAugmentedExtHom K (equationIdeal p hp) (m + d) w).comp
        (Ext.mk₀ (mulHomogeneous (grading (equationIdeal p hp)) q m)) (add_zero 2) =
      cubicQuotientRawDegreeTwoToAugmentedExtHom K (equationIdeal p hp) m
        (cubicIntrinsicRawCocycleMultiply K p hp m d q w) := by
  change (quotientCechDegreeTwoToAugmentedExt (equationIdeal p hp) (m + d)
      (cubicQuotientAbstractCocycleOfRaw K (equationIdeal p hp) (m + d) w)).comp _ _ =
    quotientCechDegreeTwoToAugmentedExt (equationIdeal p hp) m
      (cubicQuotientAbstractCocycleOfRaw K (equationIdeal p hp) m _)
  rw [quotientCechDegreeTwoToAugmentedExt_mulHomogeneous,
    cubicQuotientAbstractCocycleOfRaw_mulHomogeneous]

end PfaffianDescent.ProjectiveNegativeTwist

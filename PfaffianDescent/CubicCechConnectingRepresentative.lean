import PfaffianDescent.CubicNegativeThreeCechLift
import PfaffianDescent.P3AbstractTopRawCocycle

/-! # The actual cubic connecting class represented by a raw Laurent cocycle -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The raw negative-six boundary cocycle from an actual cubic coefficient lift. -/
def cubicNegativeThreeLiftRawBoundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 3)
    (d : CubicNegativeThreeCechLift K p hp z) : P3RawTopCocycle K 6 :=
  p3RawTopCocycleOfAbstract K 6 d.boundary

set_option backward.isDefEq.respectTransparency false in
/-- For the actual cubic sequence, its Ext connecting map is the actual raw
negative-six top cocycle obtained from lifting and taking the differential. -/
theorem cubicNegativeThree_augmented_connecting_eq_raw_boundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 3)
    (d : CubicNegativeThreeCechLift K p hp z) :
    (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 3 z).comp
      (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 3).extClass
      (show 2 + 1 = 3 by rfl) =
    p3RawTopCocycleToAugmentedExt K 6 (cubicNegativeThreeLiftRawBoundary K p hp z d) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  let S := hypersurfaceTwistRestrictionSequence p hp 3
  let hS := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 3
  have h : (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 3 z).comp
      hS.extClass (show 2 + 1 = 3 by rfl) =
      p3AbstractTopCocycleToAugmentedExt K 6 d.boundary :=
    augmentedChainDegreeTwoToExt_comp_coefficient_extension
      (p3SectionRepresenterCechTarget K)
      ((p3SectionRepresenterCechChain K).X 0)
      ((p3SectionRepresenterCechChain K).X 1)
      ((p3SectionRepresenterCechChain K).X 2)
      ((p3SectionRepresenterCechChain K).X 3)
      ((p3SectionRepresenterCechChain K).X 4)
      (p3SectionRepresenterCechAugmentation K)
      ((p3SectionRepresenterCechChain K).d 1 0)
      ((p3SectionRepresenterCechChain K).d 2 1)
      ((p3SectionRepresenterCechChain K).d 3 2)
      ((p3SectionRepresenterCechChain K).d 4 3)
      (sectionRepresenterCech_d_one_zero_comp_augmentation
        (Proj PS).ringCatSheaf (fun j : ULift.{u} (Fin 4) => p3StandardOpen K j.down)
        ⊤ isTerminalTop)
      ((p3SectionRepresenterCechChain K).d_comp_d 2 1 0)
      ((p3SectionRepresenterCechChain K).d_comp_d 3 2 1)
      ((p3SectionRepresenterCechChain K).d_comp_d 4 3 2)
      (p3SectionRepresenterCech_augmentation_exact K)
      (p3SectionRepresenterCech_exact_one K)
      (p3SectionRepresenterCech_exact_two K)
      (p3SectionRepresenterCech_exact_three K)
      S hS z d.lift d.boundary d.lift_comp d.differential_comp
  exact h.trans (p3RawTopCocycleToAugmentedExt_ofAbstract K 6 d.boundary).symm
end PfaffianDescent.ProjectiveNegativeTwist

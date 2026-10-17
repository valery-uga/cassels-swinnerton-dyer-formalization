import PfaffianDescent.CubicCanonicalCohomologyTrace
import PfaffianDescent.CechCoefficientLiftConstruction
import PfaffianDescent.P3AbstractTopRawCocycle
import PfaffianDescent.CubicSurfaceCechLaurentEvaluation

/-! # The canonical cubic trace on actual constructed Cech representatives -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Actual lift data for O(-4) -> O(-1) -> i_*O_S(-1). -/
abbrev CubicNegativeOneCechLift
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 1) :=
  CechCoefficientLift (p3SectionRepresenterCechChain K)
    (hypersurfaceTwistRestrictionSequence p hp 1) z

set_option backward.isDefEq.respectTransparency false in
/-- The proved ambient acyclicity constructs the lift and its actual
negative-four degree-three cocycle; no lift is supplied as a hypothesis. -/
theorem exists_cubic_negative_one_cech_lift
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 1) :
    Nonempty (CubicNegativeOneCechLift K p hp z) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let S := hypersurfaceTwistRestrictionSequence p hp 1
  have hS : S.ShortExact := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      ((p3SectionRepresenterCechChain K).X 2) S.X₁ 1) :=
    (p3_sectionRepresenterCechChain_ext_one_two_three_subsingleton K 4 2).1
  exact exists_cech_coefficient_lift (p3SectionRepresenterCechChain K) S hS z
/-- The raw negative-four boundary cocycle from an actual cubic coefficient lift. -/
def cubicNegativeOneLiftRawBoundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 1)
    (d : CubicNegativeOneCechLift K p hp z) : P3RawTopCocycle K 4 :=
  p3RawTopCocycleOfAbstract K 4 d.boundary

set_option backward.isDefEq.respectTransparency false in
/-- For the actual cubic sequence, its Ext connecting map is the actual raw
negative-four top cocycle obtained from lifting and taking the differential. -/
theorem cubicNegativeOne_augmented_connecting_eq_raw_boundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 1)
    (d : CubicNegativeOneCechLift K p hp z) :
    (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 1 z).comp
      (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).extClass
      (show 2 + 1 = 3 by rfl) =
    p3RawTopCocycleToAugmentedExt K 4 (cubicNegativeOneLiftRawBoundary K p hp z d) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  let S := hypersurfaceTwistRestrictionSequence p hp 1
  let hS := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1
  have h : (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 1 z).comp
      hS.extClass (show 2 + 1 = 3 by rfl) =
      p3AbstractTopCocycleToAugmentedExt K 4 d.boundary :=
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
  exact h.trans (p3RawTopCocycleToAugmentedExt_ofAbstract K 4 d.boundary).symm
set_option backward.isDefEq.respectTransparency false in
/-- The canonical augmentation/unit transport commutes with the ACTUAL
cubic connecting equivalence and its raw boundary representative. -/
theorem cubicNegativeOne_intrinsic_connecting_eq_raw_boundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 1)
    (d : CubicNegativeOneCechLift K p hp z) :
    cubicPushforwardNegativeOneCohomologyTwoEquivAmbientNegativeFourThree K p hp hp0
      ((Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
        (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 1 z) (zero_add 2)) =
    (Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
      (p3RawTopCocycleToAugmentedExt K 4 (cubicNegativeOneLiftRawBoundary K p hp z d))
      (zero_add 3) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let g : (show (Proj PS).Modules from SheafOfModules.unit (Proj PS).ringCatSheaf) ⟶
      p3SectionRepresenterCechTarget K := (p3SectionRepresenterCechTargetIsoUnit K).inv
  let c := cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 1 z
  let a := p3RawTopCocycleToAugmentedExt K 4 (cubicNegativeOneLiftRawBoundary K p hp z d)
  let hS := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1
  have haug : c.comp hS.extClass (show 2 + 1 = 3 by rfl) = a :=
    cubicNegativeOne_augmented_connecting_eq_raw_boundary K p hp hp0 z d
  change ((Ext.mk₀ g).comp c (zero_add 2)).comp hS.extClass (show 2 + 1 = 3 by rfl) =
    (Ext.mk₀ g).comp a (zero_add 3)
  rw [Ext.comp_assoc _ _ _ (zero_add 2) rfl rfl, haug]


set_option backward.isDefEq.respectTransparency false in
/-- The canonical cubic trace evaluates the actual constructed boundary by
its single canonical Laurent coefficient. -/
theorem cubicNegativeOne_trace_eq_raw_boundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 1)
    (d : CubicNegativeOneCechLift K p hp z) :
    cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0
      ((Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
        (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 1 z) (zero_add 2)) =
    p3NegativeFourRawTrace K (cubicNegativeOneLiftRawBoundary K p hp z d).1 := by
  change p3NegativeFourCohomologyThreeTraceEquiv K
    (cubicPushforwardNegativeOneCohomologyTwoEquivAmbientNegativeFourThree K p hp hp0 _) = _
  rw [cubicNegativeOne_intrinsic_connecting_eq_raw_boundary]
  exact p3NegativeFourCohomologyThreeTraceEquiv_raw K _

set_option backward.isDefEq.respectTransparency false in
/-- The actual surface coordinate-cover cocycle has the same normalized
trace after intrinsic-to-ambient transport. -/
theorem cubicSurface_negative_one_trace_eq_raw_boundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (w : QuotientCechDegreeTwoCocycle (equationIdeal p hp) 1)
    (d : CubicNegativeOneCechLift K p hp (cubicSurfaceCocycleToPushforward K p hp 1 w)) :
    cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0
      ((Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules)
        (quotientSectionRepresenterCechTargetIsoUnit (equationIdeal p hp)).inv).comp
        (quotientCechDegreeTwoToAugmentedExt (equationIdeal p hp) 1 w) (zero_add 2)) =
    p3NegativeFourRawTrace K
      (cubicNegativeOneLiftRawBoundary K p hp (cubicSurfaceCocycleToPushforward K p hp 1 w) d).1 := by
  change cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0
    (cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 1 _) = _
  rw [cubicIntrinsicCohomologyTwoEquivPushforward_coordinate_cocycle]
  exact cubicNegativeOne_trace_eq_raw_boundary K p hp hp0 _ d

end PfaffianDescent.ProjectiveNegativeTwist

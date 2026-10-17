import PfaffianDescent.CubicCechConnectingRepresentative
import PfaffianDescent.P3CechLaurentPairingEvaluation

/-! # Native cubic cohomology duality evaluated on constructed Cech boundaries -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentCechExact
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The canonical augmentation/unit transport commutes with the ACTUAL
cubic connecting equivalence and its raw boundary representative. -/
theorem cubicNegativeThree_intrinsic_connecting_eq_raw_boundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 3)
    (d : CubicNegativeThreeCechLift K p hp z) :
    cubicPushforwardNegativeThreeCohomologyTwoEquivAmbientNegativeSixThree K p hp hp0
      ((Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
        (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 3 z) (zero_add 2)) =
    (Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
      (p3RawTopCocycleToAugmentedExt K 6 (cubicNegativeThreeLiftRawBoundary K p hp z d))
      (zero_add 3) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let g : (show (Proj PS).Modules from SheafOfModules.unit (Proj PS).ringCatSheaf) ⟶
      p3SectionRepresenterCechTarget K := (p3SectionRepresenterCechTargetIsoUnit K).inv
  let c := cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 3 z
  let a := p3RawTopCocycleToAugmentedExt K 6 (cubicNegativeThreeLiftRawBoundary K p hp z d)
  let hS := hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 3
  have haug : c.comp hS.extClass (show 2 + 1 = 3 by rfl) = a :=
    cubicNegativeThree_augmented_connecting_eq_raw_boundary K p hp hp0 z d
  change ((Ext.mk₀ g).comp c (zero_add 2)).comp hS.extClass (show 2 + 1 = 3 by rfl) =
    (Ext.mk₀ g).comp a (zero_add 3)
  rw [Ext.comp_assoc _ _ _ (zero_add 2) rfl rfl, haug]

set_option backward.isDefEq.respectTransparency false in
/-- The native cubic duality evaluates every quadratic monomial as the
actual Laurent residue of its constructed negative-six boundary cocycle. -/
theorem cubicNegativeThree_dual_quadratic_raw_boundary_monomial
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 3)
    (d : CubicNegativeThreeCechLift K p hp z) (b : P3QuadraticExponent) :
    cubicPushforwardNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
      ((Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
        (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 3 z) (zero_add 2))
      (p3QuadraticMonomialBasis K b) =
    p3NegativeSixRawResidue K b (cubicNegativeThreeLiftRawBoundary K p hp z d).1 := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let w := cubicNegativeThreeLiftRawBoundary K p hp z d
  let a := p3RawTopCocycleToAugmentedExt K 6 w
  let E : Ext.{u} (C := (Proj PS).Modules) (p3SectionRepresenterCechTarget K)
      (sheafOfModules PS 6) 3 ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 6) 3 :=
    extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
  have heval : p3NegativeSixCohomologyThreeDualQuadraticEquiv K (E a)
      (p3QuadraticMonomialBasis K b) = p3NegativeSixRawResidue K b w.1 := by
    change p3NegativeSixAugmentedExtDualQuadraticEquiv K (E.symm (E a))
      (p3QuadraticMonomialBasis K b) = _
    rw [E.symm_apply_apply]
    exact p3NegativeSixAugmentedExtDualQuadraticEquiv_raw_monomial K w b
  have hc := cubicNegativeThree_intrinsic_connecting_eq_raw_boundary K p hp hp0 z d
  exact (congrArg (fun x => p3NegativeSixCohomologyThreeDualQuadraticEquiv K x
    (p3QuadraticMonomialBasis K b)) hc).trans heval

set_option backward.isDefEq.respectTransparency false in
/-- The entire native quadratic dual vector is the actual Laurent residue
coordinate vector of the constructed cubic boundary. -/
theorem cubicNegativeThree_dual_quadratic_eq_raw_residue_coordinates
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 3)
    (d : CubicNegativeThreeCechLift K p hp z) :
    cubicPushforwardNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
      ((Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
        (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 3 z) (zero_add 2)) =
    (p3QuadraticDualCoordinateEquiv K).symm
      (p3NegativeSixTopResidueCoordinates K (cubicNegativeThreeLiftRawBoundary K p hp z d)) := by
  apply (p3QuadraticMonomialBasis K).ext
  intro b
  let w := cubicNegativeThreeLiftRawBoundary K p hp z d
  let D := p3QuadraticDualCoordinateEquiv K
  let r := p3NegativeSixTopResidueCoordinates K w
  have hd := congrFun (D.apply_symm_apply r) b
  have hv : D.symm r (p3QuadraticMonomialBasis K b) = p3NegativeSixRawResidue K b w.1 :=
    (p3QuadraticDualCoordinateEquiv_apply K (D.symm r) b).symm.trans hd
  exact (cubicNegativeThree_dual_quadratic_raw_boundary_monomial K p hp hp0 z d b).trans hv.symm

set_option backward.isDefEq.respectTransparency false in
/-- A representative and its full native residue formula exist without
any supplied coefficient lifts or comparison equalities. -/
theorem exists_cubic_negative_three_residue_representative
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : CubicPushforwardAbstractDegreeTwoCocycle K p hp 3) :
    ∃ d : CubicNegativeThreeCechLift K p hp z,
      cubicPushforwardNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
        ((Ext.mk₀ (C := (Proj PS).Modules) (p3SectionRepresenterCechTargetIsoUnit K).inv).comp
          (cubicPushforwardAbstractDegreeTwoToAugmentedExt K p hp 3 z) (zero_add 2)) =
      (p3QuadraticDualCoordinateEquiv K).symm
        (p3NegativeSixTopResidueCoordinates K (cubicNegativeThreeLiftRawBoundary K p hp z d)) := by
  obtain ⟨d⟩ := exists_cubic_negative_three_cech_lift (hExt := hExt) K p hp hp0 z
  exact ⟨d, cubicNegativeThree_dual_quadratic_eq_raw_residue_coordinates
    (hExt := hExt) K p hp hp0 z d⟩
end PfaffianDescent.ProjectiveNegativeTwist

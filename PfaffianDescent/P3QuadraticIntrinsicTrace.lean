import PfaffianDescent.P3CechMultiplicationExtNaturality
import PfaffianDescent.P3CechLaurentPairingEvaluation

/-! # Intrinsic quadratic duality is canonical trace after multiplication -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentCechExact
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

theorem p3NegativeSixAugmentedExtDualQuadraticEquiv_raw
    [HasExt.{u} (Proj PS).Modules] (w : P3RawTopCocycle K 6) :
    p3NegativeSixAugmentedExtDualQuadraticEquiv K (p3RawTopCocycleToAugmentedExt K 6 w) =
      (p3QuadraticDualCoordinateEquiv K).symm (p3NegativeSixTopResidueCoordinates K w) := by
  apply (p3QuadraticMonomialBasis K).ext
  intro b
  have hd := congrFun ((p3QuadraticDualCoordinateEquiv K).apply_symm_apply
    (p3NegativeSixTopResidueCoordinates K w)) b
  have hv := (p3QuadraticDualCoordinateEquiv_apply K
    ((p3QuadraticDualCoordinateEquiv K).symm (p3NegativeSixTopResidueCoordinates K w)) b).symm.trans hd
  exact (p3NegativeSixAugmentedExtDualQuadraticEquiv_raw_monomial K w b).trans hv.symm

set_option backward.isDefEq.respectTransparency false in
/-- The full native augmented Ext pairing is the actual canonical trace
after postcomposition by quadratic multiplication. -/
theorem p3NegativeSixAugmentedExtDualQuadraticEquiv_eq_trace_multiplication
    [HasExt.{u} (Proj PS).Modules]
    (z : Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS 6) 3)
    (q : PS 2) :
    p3NegativeSixAugmentedExtDualQuadraticEquiv K z q =
      p3NegativeFourAugmentedExtTraceEquiv K
        (z.comp (Ext.mk₀ (mulHomogeneous PS q 4)) (add_zero 3)) := by
  obtain ⟨w, rfl⟩ := p3RawTopCocycleToAugmentedExt_surjective K 6 z
  rw [p3RawTopCocycleToAugmentedExt_mulHomogeneous K 4 2 q w,
    p3NegativeSixAugmentedExtDualQuadraticEquiv_raw]
  exact p3NegativeSix_raw_quadratic_pairing_eq_augmented_trace K w q

set_option backward.isDefEq.respectTransparency false in
/-- Intrinsic ambient cohomology has the same equality, including the
canonical transport from the augmentation source to the unit module. -/
theorem p3NegativeSixCohomologyThreeDualQuadraticEquiv_eq_trace_multiplication
    [HasExt.{u} (Proj PS).Modules]
    (z : schemeModuleCohomology (Proj PS) (sheafOfModules PS 6) 3) (q : PS 2) :
    p3NegativeSixCohomologyThreeDualQuadraticEquiv K z q =
      p3NegativeFourCohomologyThreeTraceEquiv K
        (z.comp (Ext.mk₀ (mulHomogeneous PS q 4)) (add_zero 3)) := by
  let E : Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS 6) 3 ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 6) 3 :=
    extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
  obtain ⟨a, rfl⟩ := E.surjective z
  change p3NegativeSixAugmentedExtDualQuadraticEquiv K (E.symm (E a)) q =
    p3NegativeFourAugmentedExtTraceEquiv K
      ((extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)).symm
        ((E a).comp (Ext.mk₀ (mulHomogeneous PS q 4)) (add_zero 3)))
  rw [E.symm_apply_apply]
  change _ = p3NegativeFourAugmentedExtTraceEquiv K
    ((Ext.mk₀ (p3SectionRepresenterCechTargetIsoUnit K).hom).comp
      (((Ext.mk₀ (p3SectionRepresenterCechTargetIsoUnit K).inv).comp a (zero_add 3)).comp
        (Ext.mk₀ (mulHomogeneous PS q 4)) (add_zero 3)) (zero_add 3))
  rw [← Ext.comp_assoc _ _ _ (zero_add 3) (add_zero 3) (by omega),
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 3) (by omega),
    Ext.mk₀_comp_mk₀]
  simp only [Iso.hom_inv_id, Ext.mk₀_id_comp]
  exact p3NegativeSixAugmentedExtDualQuadraticEquiv_eq_trace_multiplication K a q

end PfaffianDescent.ProjectiveNegativeTwist

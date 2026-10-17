import PfaffianDescent.P3CechMultiplicationExtNaturality
import PfaffianDescent.ExtSourceIsoCoefficientNaturality

/-! # Scalar compatibility of the actual canonical ambient trace -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

def p3ScalarHomogeneous (c : K) : PS 0 :=
  ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C (Fin 4) c⟩

theorem polynomialToLaurent_C (c : K) :
    polynomialToLaurent (K := K) (MvPolynomial.C c) = AddMonoidAlgebra.single 0 c := by
  change polynomialToLaurent (K := K) (MvPolynomial.monomial 0 c) = _
  rw [polynomialToLaurent_monomial, map_zero]

theorem p3NegativeFourTopTrace_scalar_multiplication (c : K) (w : P3RawTopCocycle K 4) :
    p3NegativeFourTopTrace K (p3RawTopCocycleMultiply K 4 0 (p3ScalarHomogeneous K c) w) =
      c * p3NegativeFourTopTrace K w := by
  change (p3NegativeTwistCechTermToLaurent K 4 3
    ((p3NegativeTwistCechMultiplication K 4 0 (p3ScalarHomogeneous K c)).f 3 w.1) id).coeff
      (p3SerreDualExponent 0) =
    c * ((p3NegativeTwistCechTermToLaurent K 4 3 w.1) id).coeff (p3SerreDualExponent 0)
  rw [p3NegativeTwistCechMultiplication_toLaurent K 4 0 3 (p3ScalarHomogeneous K c) w.1 id]
  change (polynomialToLaurent (K := K) (MvPolynomial.C c) *
    ((p3NegativeTwistCechTermToLaurent K 4 3 w.1) id)).coeff (p3SerreDualExponent 0) = _
  rw [polynomialToLaurent_C]
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]

set_option backward.isDefEq.respectTransparency false in
theorem p3NegativeFourAugmentedExtTrace_scalar_multiplication
    [HasExt.{u} (Proj PS).Modules]
    (c : K) (z : Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS 4) 3) :
    p3NegativeFourAugmentedExtTraceEquiv K
        (z.comp (Ext.mk₀ (mulHomogeneous PS (p3ScalarHomogeneous K c) 4)) (add_zero 3)) =
      c * p3NegativeFourAugmentedExtTraceEquiv K z := by
  obtain ⟨w, rfl⟩ := p3RawTopCocycleToAugmentedExt_surjective K 4 z
  rw [p3RawTopCocycleToAugmentedExt_mulHomogeneous K 4 0 (p3ScalarHomogeneous K c) w,
    p3NegativeFourAugmentedExtTraceEquiv_raw, p3NegativeFourAugmentedExtTraceEquiv_raw]
  exact p3NegativeFourTopTrace_scalar_multiplication K c w

theorem p3NegativeFourCohomologyTrace_unit_class
    [HasExt.{u} (Proj PS).Modules]
    (z : Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS 4) 3) :
    p3NegativeFourCohomologyThreeTraceEquiv K
        (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K) z) =
      p3NegativeFourAugmentedExtTraceEquiv K z := by
  change p3NegativeFourAugmentedExtTraceEquiv K
    ((extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)).symm
      (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K) z)) = _
  rw [AddEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Actual multiplication by a ground-field scalar scales the intrinsic
canonical trace by that scalar. No linearity compatibility is assumed. -/
theorem p3NegativeFourCohomologyTrace_scalar_multiplication
    [HasExt.{u} (Proj PS).Modules] (c : K)
    (z : schemeModuleCohomology (Proj PS) (sheafOfModules PS 4) 3) :
    p3NegativeFourCohomologyThreeTraceEquiv K
        (z.comp (Ext.mk₀ (mulHomogeneous PS (p3ScalarHomogeneous K c) 4)) (add_zero 3)) =
      c * p3NegativeFourCohomologyThreeTraceEquiv K z := by
  let E : Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS 4) 3 ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 4) 3 :=
    extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
  obtain ⟨a, rfl⟩ := E.surjective z
  have h := extPrecompIsoOfIso_postcomp (p3SectionRepresenterCechTargetIsoUnit K) a
    (mulHomogeneous PS (p3ScalarHomogeneous K c) 4)
  calc
    _ = p3NegativeFourCohomologyThreeTraceEquiv K
        (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
          (a.comp (Ext.mk₀ (mulHomogeneous PS (p3ScalarHomogeneous K c) 4)) (add_zero 3))) :=
      congrArg (p3NegativeFourCohomologyThreeTraceEquiv K) h
    _ = _ := by
      rw [p3NegativeFourCohomologyTrace_unit_class, p3NegativeFourCohomologyTrace_unit_class]
      exact p3NegativeFourAugmentedExtTrace_scalar_multiplication K c a

end PfaffianDescent.ProjectiveNegativeTwist

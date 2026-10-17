import PfaffianDescent.VoisinP3TopCechExtComparison

/-! # Actual top-cohomology vanishing for the negative-one twist -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization LaurentCechCore LaurentCechExact
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- A negative-one top cocycle is a boundary because a full-negative
Laurent exponent has degree at most minus four. -/
theorem p3NegativeOneRawCocycle_is_boundary (w : P3RawTopCocycle K 1) :
    ∃ z : (p3NegativeTwistCechComplex (K := K) 1).X 2,
      (p3NegativeTwistCechComplex (K := K) 1).d 2 3 z = w.1 := by
  let wL := p3NegativeTwistCechTermToLaurent K 1 3 w.1
  have hp : ∀ a : LaurentLocalization.LaurentExponent,
      totalDegree a = -1 → negativeSupport a ≠ Set.univ := by
    intro a ha hf
    have hr := p3SerreDualExponent_polynomialExponent_of_negativeSupport a hf
    have ht := congrArg totalDegree hr
    rw [p3SerreDualExponent_totalDegree, ha] at ht
    omega
  have hs : ∀ f (a : LaurentLocalization.LaurentExponent),
      a ∈ (wL f).coeff.support → totalDegree a = -1 ∧ negativeSupport a ⊆ Set.range f := by
    intro f a ha
    exact p3NegativeTwistCechTermToLaurent_support_properties K 1 3 w.1 f a ha
  have hc : ∀ f, tupleD3 wL f = 0 := by
    intro f
    rw [← congrFun (p3NegativeTwistCechTermToLaurent_d_three K 1 w.1) f, w.2]
    simp
  obtain ⟨zL, hzL, hdiff⟩ :=
    laurent_tuple_exact_three_of_degree_of_no_full_support K (-1) hp wL hs hc
  obtain ⟨z, hz⟩ := exists_p3NegativeTwistCechTermToLaurent_eq_of_support K 1 2 zL hzL
  refine ⟨z, ?_⟩
  apply p3NegativeTwistCechTermToLaurent_injective K 1 3
  rw [p3NegativeTwistCechTermToLaurent_d_two, hz]
  funext f
  exact hdiff f

/-- The actual third cohomology of O(-1) on P-three vanishes. -/
theorem p3NegativeOne_cohomology_three_subsingleton
    [HasExt.{u} (Proj PS).Modules] :
    Subsingleton (schemeModuleCohomology (Proj PS) (sheafOfModules PS 1) 3) := by
  have hAug : Subsingleton
      (Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS 1) 3) := by
    apply subsingleton_of_forall_eq 0
    intro z
    obtain ⟨w, rfl⟩ := p3RawTopCocycleToAugmentedExt_surjective K 1 z
    apply (p3RawTopCocycleToAugmentedExt_eq_zero_iff K 1 w).2
    exact p3NegativeOneRawCocycle_is_boundary K w
  exact (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)).toEquiv.subsingleton_congr.mp hAug

end PfaffianDescent.ProjectiveNegativeTwist

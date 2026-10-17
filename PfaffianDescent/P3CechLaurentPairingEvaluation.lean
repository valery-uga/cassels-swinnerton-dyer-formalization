import PfaffianDescent.VoisinP3TopCechExtComparison

/-! # Evaluation of the native ambient duality on actual raw cocycles -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
namespace PfaffianDescent
universe u t

private def kernelEqQuotientEquiv {G : Type u} {H : Type t}
    [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (hf : Function.Surjective f)
    (N : AddSubgroup G) (h : f.ker = N) : G ⧸ N ≃+ H := by
  rw [← h]
  exact QuotientAddGroup.quotientKerEquivOfSurjective f hf

private theorem kernelEqQuotientEquiv_mk {G : Type u} {H : Type t}
    [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (hf : Function.Surjective f)
    (N : AddSubgroup G) (h : f.ker = N) (g : G) :
    kernelEqQuotientEquiv f hf N h (QuotientAddGroup.mk g) = f g := by
  subst N
  rfl

namespace ProjectiveNegativeTwist
open LaurentCechExact
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The native quotient-to-Ext equivalence sends the literal representative
to its actual augmented Cech class. -/
theorem p3NegativeSixTopCechQuotientEquivAugmentedExt_mk
    [hExt : HasExt.{u} (Proj PS).Modules] (w : P3RawTopCocycle K 6) :
    p3NegativeSixTopCechQuotientEquivAugmentedExt K (QuotientAddGroup.mk w) =
      p3RawTopCocycleToAugmentedExt K 6 w := by
  exact kernelEqQuotientEquiv_mk
    (p3RawTopCocycleToAugmentedExtHom K 6)
    (p3RawTopCocycleToAugmentedExt_surjective K 6)
    (p3NegativeSixTopResidueCoordinates K).ker
    (p3NegativeSixRawTopCocycleToAugmentedExt_ker_eq_residue_ker K) w

set_option backward.isDefEq.respectTransparency false in
/-- Each quadratic monomial evaluates the native Ext duality by its actual
Laurent residue coefficient, with all quotient transports canceled. -/
theorem p3NegativeSixAugmentedExtDualQuadraticEquiv_raw_monomial
    [hExt : HasExt.{u} (Proj PS).Modules]
    (w : P3RawTopCocycle K 6) (b : P3QuadraticExponent) :
    p3NegativeSixAugmentedExtDualQuadraticEquiv K
      (p3RawTopCocycleToAugmentedExt K 6 w) (p3QuadraticMonomialBasis K b) =
      p3NegativeSixRawResidue K b w.1 := by
  let x : p3NegativeSixTopCocycles K ⧸ (p3NegativeSixTopResidueCoordinates K).ker :=
    QuotientAddGroup.mk w
  let E := p3NegativeSixTopCechQuotientEquivAugmentedExt K
  let R := p3NegativeSixTopCechCohomologyResidueEquiv K
  let D := p3QuadraticDualCoordinateEquiv K
  have hx : E.symm (p3RawTopCocycleToAugmentedExt K 6 w) = x := by
    rw [← p3NegativeSixTopCechQuotientEquivAugmentedExt_mk K w]
    exact E.symm_apply_apply x
  change D.symm (R (E.symm (p3RawTopCocycleToAugmentedExt K 6 w)))
    (p3QuadraticMonomialBasis K b) = _
  rw [hx]
  have hd := congrFun (D.apply_symm_apply (R x)) b
  have hd' : (D.symm (R x)) (p3QuadraticMonomialBasis K b) = R x b :=
    (p3QuadraticDualCoordinateEquiv_apply K (D.symm (R x)) b).symm.trans hd
  exact hd'
end ProjectiveNegativeTwist
end PfaffianDescent

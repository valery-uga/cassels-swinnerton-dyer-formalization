import PfaffianDescent.VoisinP3TopCechSerreDuality
import Mathlib.Algebra.MonoidAlgebra.Module

/-! # The quadratic Laurent residue pairing is actual multiplication -/
noncomputable section
open MvPolynomial
namespace PfaffianDescent.LaurentCechExact
open LaurentLocalization
universe u
variable (K : Type u) [Field K]

/-- Multiply by a quadratic and extract the coefficient whose four
exponents are all minus one. -/
def p3QuadraticLaurentResidueLinearMap (w : LaurentPolynomial K) :
    Module.Dual K (homogeneousSubmodule (Fin 4) K 2) where
  toFun q := (polynomialToLaurent (K := K) (q : MvPolynomial (Fin 4) K) * w).coeff
    (p3SerreDualExponent 0)
  map_add' q q' := by
    change (polynomialToLaurent (K := K) ((q : MvPolynomial (Fin 4) K) + (q' : MvPolynomial (Fin 4) K)) * w).coeff _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' c q := by
    change (polynomialToLaurent (K := K) (c • (q : MvPolynomial (Fin 4) K)) * w).coeff _ = _
    have hs : polynomialToLaurent (K := K) (c • (q : MvPolynomial (Fin 4) K)) =
        c • polynomialToLaurent (K := K) (q : MvPolynomial (Fin 4) K) := by
      ext a
      change (Finsupp.mapDomain exponentToInt
        (c • AddMonoidAlgebra.coeff (q : MvPolynomial (Fin 4) K))) a =
        (c • Finsupp.mapDomain exponentToInt
          (AddMonoidAlgebra.coeff (q : MvPolynomial (Fin 4) K))) a
      rw [Finsupp.mapDomain_smul]
    rw [hs, smul_mul_assoc, AddMonoidAlgebra.coeff_smul_apply]
    rfl

/-- Multiplication by a monomial shifts the distinguished residue
coefficient to its Serre-dual exponent, with no extra scalar or sign. -/
theorem p3QuadraticLaurentResidueLinearMap_monomial
    (w : LaurentPolynomial K) (b : P3QuadraticExponent) :
    p3QuadraticLaurentResidueLinearMap K w (p3QuadraticMonomialBasis K b) =
      w.coeff (p3SerreDualExponent b) := by
  change (polynomialToLaurent (K := K)
    ((p3QuadraticMonomialBasis K b : homogeneousSubmodule (Fin 4) K 2) :
      MvPolynomial (Fin 4) K) * w).coeff (p3SerreDualExponent 0) = _
  rw [p3QuadraticMonomialBasis_apply_coe, polynomialToLaurent_monomial,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  simp [p3SerreDualExponent, sub_eq_add_neg]

/-- The full quadratic dual vector of Laurent coefficients is the
actual multiply-then-extract functional. -/
theorem p3QuadraticLaurentResidueLinearMap_eq_dual_coordinates
    (w : LaurentPolynomial K) :
    p3QuadraticLaurentResidueLinearMap K w =
      (p3QuadraticDualCoordinateEquiv K).symm
        (fun b : P3QuadraticExponent => w.coeff (p3SerreDualExponent b)) := by
  apply (p3QuadraticMonomialBasis K).ext
  intro b
  rw [p3QuadraticLaurentResidueLinearMap_monomial]
  let c := fun b : P3QuadraticExponent => w.coeff (p3SerreDualExponent b)
  have h := congrFun ((p3QuadraticDualCoordinateEquiv K).apply_symm_apply c) b
  exact h.symm.trans (p3QuadraticDualCoordinateEquiv_apply K
    ((p3QuadraticDualCoordinateEquiv K).symm c) b)

end PfaffianDescent.LaurentCechExact

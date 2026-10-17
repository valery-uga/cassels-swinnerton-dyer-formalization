import PfaffianDescent.PolynomialMatrixDescent
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.Basic

namespace PfaffianDescent
open MvPolynomial
open scoped TensorProduct
section
variable {K L σ m n : Type*} [Field K] [Field L] [Algebra K L]

/-- The canonical identification of polynomial vectors after extension of coefficients. -/
noncomputable def polynomialVectorBaseChange (K L σ n : Type*)
    [Field K] [Field L] [Algebra K L] [Fintype n] :
    (L ⊗[K] (n → MvPolynomial σ K)) ≃ₗ[L] (n → MvPolynomial σ L) := by
  classical
  exact (TensorProduct.piRight K L L (fun _ : n => MvPolynomial σ K)).trans
    (LinearEquiv.piCongrRight fun _ => (MvPolynomial.algebraTensorAlgEquiv K L).toLinearEquiv)

@[simp] lemma polynomialVectorBaseChange_tmul [Fintype n]
    (a : L) (v : n → MvPolynomial σ K) :
    polynomialVectorBaseChange K L σ n (a ⊗ₜ[K] v) =
      fun i => a • MvPolynomial.map (algebraMap K L) (v i) := by
  funext i
  exact MvPolynomial.algebraTensorAlgEquiv_tmul K L a (v i)

variable [Fintype m] [Fintype n]

/-- Under the canonical tensor identification, a polynomial matrix is base changed
by applying the field map to each coefficient. -/
theorem polynomialVectorBaseChange_matrix
    (A : Matrix m n (MvPolynomial σ K)) (z : L ⊗[K] (n → MvPolynomial σ K)) :
    polynomialVectorBaseChange K L σ m
        ((A.mulVecLin.restrictScalars K).baseChange L z) =
      (A.map (MvPolynomial.map (algebraMap K L))).mulVec
        (polynomialVectorBaseChange K L σ n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Matrix.mulVec_zero]
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, polynomialVectorBaseChange_tmul,
      polynomialVectorBaseChange_tmul]
    have hs := ((A.map (MvPolynomial.map (algebraMap K L))).mulVecLin.restrictScalars L).map_smul
      a (fun i => MvPolynomial.map (algebraMap K L) (v i))
    apply Eq.trans _ hs.symm
    funext i
    exact congrArg (fun p : MvPolynomial σ L => a • p)
      (RingHom.map_mulVec (MvPolynomial.map (algebraMap K L)) A v i)
  | add x y hx hy =>
    rw [map_add, map_add, map_add, Matrix.mulVec_add, hx, hy]

end
end PfaffianDescent

import PfaffianDescent.PolynomialCoefficientRetraction
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K L σ m n o : Type*} [Field K] [Field L] [Algebra K L]
variable [Fintype n]

/-- Projection of coefficients commutes with a matrix defined over the ground field. -/
lemma polynomialCoefficientMap_mulVec (phi : L →ₗ[K] K)
    (A : Matrix m n (MvPolynomial σ K)) (v : n → MvPolynomial σ L) :
    (fun i => polynomialCoefficientMap phi
      ((A.map (MvPolynomial.map (algebraMap K L))).mulVec v i)) =
      A.mulVec (fun j => polynomialCoefficientMap phi (v j)) := by
  funext i
  change polynomialCoefficientMap phi (∑ j, MvPolynomial.map (algebraMap K L) (A i j) * v j) =
    ∑ j, A i j * polynomialCoefficientMap phi (v j)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => polynomialCoefficientMap_mul phi (A i j) (v j))

/-- A polynomial linear system over a field has a solution if it has one after extending that field. -/
theorem polynomial_matrix_solution_descends
    (A : Matrix m n (MvPolynomial σ K)) (b : m → MvPolynomial σ K)
    (h : ∃ v : n → MvPolynomial σ L,
      (A.map (MvPolynomial.map (algebraMap K L))).mulVec v =
        fun i => MvPolynomial.map (algebraMap K L) (b i)) :
    ∃ v : n → MvPolynomial σ K, A.mulVec v = b := by
  obtain ⟨phi, hphi⟩ := exists_field_linear_retraction (K := K) (L := L)
  obtain ⟨v, hv⟩ := h
  refine ⟨fun j => polynomialCoefficientMap phi (v j), ?_⟩
  rw [← polynomialCoefficientMap_mulVec, hv]
  funext i
  exact polynomialCoefficientMap_map phi hphi (b i)

/-- Solvability of a polynomial matrix equation is unchanged by field extension. -/
theorem polynomial_matrix_solution_iff
    (A : Matrix m n (MvPolynomial σ K)) (b : m → MvPolynomial σ K) :
    (∃ v : n → MvPolynomial σ L,
      (A.map (MvPolynomial.map (algebraMap K L))).mulVec v =
        fun i => MvPolynomial.map (algebraMap K L) (b i)) ↔
    ∃ v : n → MvPolynomial σ K, A.mulVec v = b := by
  constructor
  · exact polynomial_matrix_solution_descends A b
  · rintro ⟨v, hv⟩
    refine ⟨fun j => MvPolynomial.map (algebraMap K L) (v j), ?_⟩
    funext i
    exact (RingHom.map_mulVec (MvPolynomial.map (algebraMap K L)) A v i).symm.trans
      (congrArg (MvPolynomial.map (algebraMap K L)) (congrFun hv i))

variable [Fintype m]

/-- The vanishing of a ground-field polynomial matrix on a vector is reflected by field extension. -/
lemma polynomial_matrix_kernel_map
    (B : Matrix o m (MvPolynomial σ K)) (v : m → MvPolynomial σ K) :
    (B.map (MvPolynomial.map (algebraMap K L))).mulVec
        (fun i => MvPolynomial.map (algebraMap K L) (v i)) = 0 ↔
      B.mulVec v = 0 := by
  constructor
  · intro h
    funext i
    apply MvPolynomial.map_injective (algebraMap K L)
      (FaithfulSMul.algebraMap_injective K L)
    rw [RingHom.map_mulVec]
    exact (congrFun h i).trans (map_zero _).symm
  · intro h
    funext i
    exact (RingHom.map_mulVec (MvPolynomial.map (algebraMap K L)) B v i).symm.trans
      ((congrArg (MvPolynomial.map (algebraMap K L)) (congrFun h i)).trans (map_zero _))

/-- Exactness of polynomial matrices descends along an arbitrary field extension. -/
theorem polynomial_matrix_exactness_descends
    (A : Matrix m n (MvPolynomial σ K)) (B : Matrix o m (MvPolynomial σ K))
    (h : LinearMap.range (A.map (MvPolynomial.map (algebraMap K L))).mulVecLin =
      LinearMap.ker (B.map (MvPolynomial.map (algebraMap K L))).mulVecLin) :
    LinearMap.range A.mulVecLin = LinearMap.ker B.mulVecLin := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    apply (polynomial_matrix_kernel_map (L := L) B (A.mulVec w)).mp
    change (fun i => MvPolynomial.map (algebraMap K L) (A.mulVec w i)) ∈
      LinearMap.ker (B.map (MvPolynomial.map (algebraMap K L))).mulVecLin
    rw [← h]
    refine ⟨fun i => MvPolynomial.map (algebraMap K L) (w i), ?_⟩
    funext i
    exact (RingHom.map_mulVec (MvPolynomial.map (algebraMap K L)) A w i).symm
  · intro hv
    have hvL := (polynomial_matrix_kernel_map (L := L) B v).mpr hv
    have hr : (fun i => MvPolynomial.map (algebraMap K L) (v i)) ∈
        LinearMap.range (A.map (MvPolynomial.map (algebraMap K L))).mulVecLin := by
      rw [h]
      exact hvL
    exact polynomial_matrix_solution_descends (L := L) A v hr

/-- Injectivity of a polynomial matrix also descends from an extension field. -/
theorem polynomial_matrix_injectivity_descends
    (A : Matrix m n (MvPolynomial σ K))
    (h : Function.Injective (A.map (MvPolynomial.map (algebraMap K L))).mulVecLin) :
    Function.Injective A.mulVecLin := by
  intro v w hvw
  have he : (fun i => MvPolynomial.map (algebraMap K L) (v i)) =
      fun i => MvPolynomial.map (algebraMap K L) (w i) := by
    apply h
    funext i
    exact (RingHom.map_mulVec (MvPolynomial.map (algebraMap K L)) A v i).symm.trans
      ((congrArg (MvPolynomial.map (algebraMap K L)) (congrFun hvw i)).trans
        (RingHom.map_mulVec (MvPolynomial.map (algebraMap K L)) A w i))
  funext i
  exact MvPolynomial.map_injective (algebraMap K L)
    (FaithfulSMul.algebraMap_injective K L) (congrFun he i)

end
end PfaffianDescent

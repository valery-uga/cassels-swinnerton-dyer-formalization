import PfaffianDescent.PolynomialMatrixDescent

namespace PfaffianDescent
open MvPolynomial
section
variable {K L σ m n : Type*} [Field K] [Field L] [Algebra K L]

/-- A linear projection of coefficients preserves homogeneous degree. -/
lemma polynomialCoefficientMap_homogeneous (phi : L →ₗ[K] K)
    {p : MvPolynomial σ L} {d : ℕ} (hp : p.IsHomogeneous d) :
    (polynomialCoefficientMap phi p).IsHomogeneous d := by
  intro e he
  apply hp
  intro hz
  apply he
  rw [polynomialCoefficientMap_coeff, hz, map_zero]

/-- Homogeneous degree is both preserved and reflected by extension of the coefficient field. -/
lemma polynomial_map_homogeneous_iff (p : MvPolynomial σ K) (d : ℕ) :
    (MvPolynomial.map (algebraMap K L) p).IsHomogeneous d ↔ p.IsHomogeneous d := by
  constructor
  · intro hp e he
    apply hp
    rw [coeff_map]
    exact (map_ne_zero (algebraMap K L)).mpr he
  · intro hp e he
    apply hp
    intro hz
    apply he
    rw [coeff_map, hz, map_zero]

/-- Homogeneous solutions, allowing a different degree in each column, descend
along any extension of the coefficient field. -/
theorem homogeneous_polynomial_matrix_solution_descends [Fintype n]
    (A : Matrix m n (MvPolynomial σ K)) (b : m → MvPolynomial σ K) (d : n → ℕ)
    (h : ∃ v : n → MvPolynomial σ L, (∀ j, (v j).IsHomogeneous (d j)) ∧
      (A.map (MvPolynomial.map (algebraMap K L))).mulVec v =
        fun i => MvPolynomial.map (algebraMap K L) (b i)) :
    ∃ v : n → MvPolynomial σ K, (∀ j, (v j).IsHomogeneous (d j)) ∧ A.mulVec v = b := by
  obtain ⟨phi, hphi⟩ := exists_field_linear_retraction (K := K) (L := L)
  obtain ⟨v, hd, hv⟩ := h
  refine ⟨fun j => polynomialCoefficientMap phi (v j),
    fun j => polynomialCoefficientMap_homogeneous phi (hd j), ?_⟩
  rw [← polynomialCoefficientMap_mulVec, hv]
  funext i
  exact polynomialCoefficientMap_map phi hphi (b i)

/-- Vanishing of the constant coefficient, the minimality condition for a graded
polynomial matrix, is reflected by coefficient extension. -/
lemma polynomial_map_constantCoeff_zero_iff (p : MvPolynomial σ K) :
    constantCoeff (MvPolynomial.map (algebraMap K L) p) = 0 ↔ constantCoeff p = 0 := by
  change coeff 0 (MvPolynomial.map (algebraMap K L) p) = 0 ↔ coeff 0 p = 0
  rw [coeff_map]
  exact (FaithfulSMul.algebraMap_injective K L).eq_iff' (map_zero _)

end
end PfaffianDescent

import PfaffianDescent.GeneratorBasisChange
import PfaffianDescent.HomogeneousProjection

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K σ n : Type*} [Field K] [Fintype n] [DecidableEq n]

lemma constant_matrix_inv_mulVec (D : Matrix n n K) (hD : IsUnit D.det)
    (v : n → MvPolynomial σ K) :
    (D⁻¹.map C).mulVec ((D.map C).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul D hD]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

lemma constant_matrix_mul_invVec (D : Matrix n n K) (hD : IsUnit D.det)
    (v : n → MvPolynomial σ K) :
    (D.map C).mulVec ((D⁻¹.map C).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_nonsing_inv D hD]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

lemma constant_matrix_homogeneous (D : Matrix n n K) (d : ℕ)
    (v : n → MvPolynomial σ K) (hv : ∀ i, (v i).IsHomogeneous d) (i : n) :
    ((D.map C).mulVec v i).IsHomogeneous d := by
  change (∑ j, C (D i j) * v j) ∈ homogeneousSubmodule σ K d
  exact Submodule.sum_mem _ (fun j _ => (hv j).C_mul (D i j))

/-- A constant change of quadratic generators is the inverse change of
coordinates on their free coefficient module. -/
lemma polynomial_linearCombination_generator_change (u q : n → MvPolynomial σ K)
    (D : Matrix n n K) (hD : ∀ j, q j = ∑ i, D i j • u i)
    (v : n → MvPolynomial σ K) :
    Fintype.linearCombination (MvPolynomial σ K) q v =
      Fintype.linearCombination (MvPolynomial σ K) u ((D.map C).mulVec v) := by
  have hq : q = (D.map C).transpose.mulVec u := by
    funext j
    rw [hD]
    change (∑ i, D i j • u i) = ∑ i, C (D i j) * u i
    simp only [MvPolynomial.smul_eq_C_mul]
  change dotProduct v q = dotProduct ((D.map C).mulVec v) u
  rw [hq, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end
end PfaffianDescent

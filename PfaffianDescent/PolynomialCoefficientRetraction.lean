import PfaffianDescent.HomogeneousProjection
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace PfaffianDescent
open MvPolynomial
section
variable {K L σ : Type*} [Field K] [Field L] [Algebra K L]

/-- Apply a ground-field linear map independently to every polynomial coefficient. -/
noncomputable def polynomialCoefficientMap (phi : L →ₗ[K] K) :
    MvPolynomial σ L →ₗ[K] MvPolynomial σ K :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap phi ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] lemma polynomialCoefficientMap_coeff (phi : L →ₗ[K] K)
    (f : MvPolynomial σ L) (d : σ →₀ ℕ) :
    coeff d (polynomialCoefficientMap phi f) = phi (coeff d f) := rfl

@[simp] lemma polynomialCoefficientMap_C (phi : L →ₗ[K] K) (c : L) :
    polynomialCoefficientMap phi (C (σ := σ) c) = C (σ := σ) (phi c) := by
  classical
  ext d
  rw [polynomialCoefficientMap_coeff, coeff_C, coeff_C]
  split_ifs <;> simp

/-- Coefficient projection commutes with multiplication by a polynomial defined over the ground field. -/
lemma polynomialCoefficientMap_mul (phi : L →ₗ[K] K)
    (p : MvPolynomial σ K) (q : MvPolynomial σ L) :
    polynomialCoefficientMap phi (MvPolynomial.map (algebraMap K L) p * q) =
      p * polynomialCoefficientMap phi q := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [polynomialCoefficientMap_coeff, coeff_mul, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro ab _
  rw [coeff_map, polynomialCoefficientMap_coeff]
  simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using
    phi.map_smul (coeff ab.1 p) (coeff ab.2 q)

lemma polynomialCoefficientMap_C_mul_map (phi : L →ₗ[K] K)
    (c : L) (q : MvPolynomial σ K) :
    polynomialCoefficientMap phi (C c * MvPolynomial.map (algebraMap K L) q) =
      C (phi c) * q := by
  rw [mul_comm, polynomialCoefficientMap_mul, polynomialCoefficientMap_C, mul_comm]

lemma polynomialCoefficientMap_map (phi : L →ₗ[K] K)
    (hphi : ∀ a : K, phi (algebraMap K L a) = a) (p : MvPolynomial σ K) :
    polynomialCoefficientMap phi (MvPolynomial.map (algebraMap K L) p) = p := by
  apply MvPolynomial.ext
  intro d
  rw [polynomialCoefficientMap_coeff, coeff_map, hphi]

/-- Every field extension admits a ground-field linear coefficient retraction. -/
theorem exists_field_linear_retraction :
    ∃ phi : L →ₗ[K] K, ∀ a : K, phi (algebraMap K L a) = a := by
  have hi : Function.Injective (Algebra.linearMap K L) :=
    FaithfulSMul.algebraMap_injective K L
  obtain ⟨phi, hphi⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi)
  exact ⟨phi, fun a => LinearMap.congr_fun hphi a⟩

end
end PfaffianDescent

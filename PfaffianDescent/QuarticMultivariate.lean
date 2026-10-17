import PfaffianDescent.MultivariateCubic
import PfaffianDescent.QuarticCycle

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The degree-four theorem for mathlib's actual multivariate cubic polynomials. -/
theorem homogeneous_cubic_degree_four_descent (f : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hdim : finrank K L = 4)
    (p : Vec L 4) (hp : p ≠ 0) (hF : MvPolynomial.eval₂ (algebraMap K L) p f = 0) :
    ∃ x : Vec K 4, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  obtain ⟨c, rfl⟩ := homogeneous_cubic_has_tensor f hf
  rw [Cubic.eval_toMvPolynomial] at hF
  obtain ⟨x, hx, he⟩ := cubic_degree_four_descent hdim c p hp hF
  refine ⟨x, hx, ?_⟩
  change MvPolynomial.eval₂ (RingHom.id K) x c.toMvPolynomial = 0
  rw [Cubic.eval_toMvPolynomial]
  exact he

end

section
variable {K : Type*} [Field K] [CharZero K]

/-- The main effective-cycle theorem for ordinary homogeneous cubic equations.
In particular it applies to every smooth cubic surface over a characteristic-zero field. -/
theorem homogeneous_cubic_effective_degree_four_to_point {ι : Type*} [Fintype ι]
    (L : ι → Type*) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (w : ι → ℕ) (p : ∀ i, Vec (L i) 4)
    (hp : ∀ i, w i ≠ 0 → p i ≠ 0)
    (hF : ∀ i, w i ≠ 0 → MvPolynomial.eval₂ (algebraMap K (L i)) (p i) f = 0)
    (hdegree : ∑ i, w i * finrank K (L i) = 4) :
    ∃ x : Vec K 4, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  obtain ⟨c, rfl⟩ := homogeneous_cubic_has_tensor f hf
  have he : ∀ i, w i ≠ 0 → (c.map (algebraMap K (L i))).eval (p i) = 0 := by
    intro i hi
    simpa only [Cubic.eval_toMvPolynomial] using hF i hi
  obtain ⟨x, hx, hcx⟩ := effective_degree_four_to_point L c w p hp he hdegree
  refine ⟨x, hx, ?_⟩
  change MvPolynomial.eval₂ (RingHom.id K) x c.toMvPolynomial = 0
  rw [Cubic.eval_toMvPolynomial]
  exact hcx

end
end PfaffianDescent

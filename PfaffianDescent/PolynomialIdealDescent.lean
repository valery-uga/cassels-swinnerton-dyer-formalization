import PfaffianDescent.PolynomialCoefficientRetraction
import PfaffianDescent.PolynomialLinearChange

/-!
# Descent of finite polynomial ideal membership

A relation among finitely many polynomials defined over a field may be found
after extending scalars.  A linear coefficient retraction carries that
relation back to the ground field.
-/

namespace PfaffianDescent

open MvPolynomial

variable {k K σ ι : Type*} [Field k] [Field K] [Algebra k K] [Fintype ι]

theorem polynomial_mem_span_map_range_descends
    (Q : ι → MvPolynomial σ k) (F : MvPolynomial σ k)
    (hF : MvPolynomial.map (algebraMap k K) F ∈
      Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap k K) (Q i)))) :
    F ∈ Ideal.span (Set.range Q) := by
  obtain ⟨phi, hphi⟩ := exists_field_linear_retraction (K := k) (L := K)
  rw [Ideal.mem_span_range_iff_exists_fun] at hF ⊢
  obtain ⟨c, hc⟩ := hF
  refine ⟨fun i => polynomialCoefficientMap phi (c i), ?_⟩
  calc
    ∑ i, polynomialCoefficientMap phi (c i) * Q i =
        ∑ i, polynomialCoefficientMap phi
          (c i * MvPolynomial.map (algebraMap k K) (Q i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm (c i), polynomialCoefficientMap_mul]
      ring
    _ = polynomialCoefficientMap phi
        (∑ i, c i * MvPolynomial.map (algebraMap k K) (Q i)) := by
      rw [map_sum]
    _ = polynomialCoefficientMap phi (MvPolynomial.map (algebraMap k K) F) := by
      rw [hc]
    _ = F := polynomialCoefficientMap_map phi hphi F

/-- The same descent after an invertible coordinate change over the extension
field.  This is the form used by the geometric tangent-net calculation. -/
theorem polynomial_mem_span_of_algEquiv_map_range_descends
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (Q : ι → MvPolynomial σ k) (F : MvPolynomial σ k)
    (hF : E (MvPolynomial.map (algebraMap k K) F) ∈
      Ideal.span (Set.range (fun i =>
        E (MvPolynomial.map (algebraMap k K) (Q i))))) :
    F ∈ Ideal.span (Set.range Q) := by
  apply polynomial_mem_span_map_range_descends (k := k) (K := K) (σ := σ) Q F
  rw [Ideal.mem_span_range_iff_exists_fun] at hF ⊢
  obtain ⟨c, hc⟩ := hF
  refine ⟨fun i => E.symm (c i), ?_⟩
  apply E.injective
  simp only [map_sum, map_mul, E.apply_symm_apply]
  exact hc

/-- Specialization of the preceding result to an invertible linear change of
homogeneous coordinates. -/
theorem polynomial_mem_span_of_linearSubstitution_map_range_descends
    (M : Matrix (Fin n) (Fin n) K) (hM : IsUnit M.det)
    (Q : ι → MvPolynomial (Fin n) k) (F : MvPolynomial (Fin n) k)
    (hF : linearSubstitution M (MvPolynomial.map (algebraMap k K) F) ∈
      Ideal.span (Set.range (fun i =>
        linearSubstitution M (MvPolynomial.map (algebraMap k K) (Q i))))) :
    F ∈ Ideal.span (Set.range Q) := by
  exact polynomial_mem_span_of_algEquiv_map_range_descends
    (linearSubstitutionEquiv M hM) Q F hF

end PfaffianDescent

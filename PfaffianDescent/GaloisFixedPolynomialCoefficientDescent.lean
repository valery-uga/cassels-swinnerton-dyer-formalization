import PfaffianDescent.QuarticGaloisPairDescent

/-! SOURCE ONLY, UNVERIFIED. Actual polynomial coefficients descend from
being fixed by every Galois automorphism. No polynomial lift certificate. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial
universe u v
variable {k E : Type u} [Field k] [Field E] [Algebra k E] [IsGalois k E]

theorem galois_fixed_polynomial_descends {J : Type v}
    (q : MvPolynomial J E)
    (hfix : ∀ g : E ≃ₐ[k] E, MvPolynomial.map g.toRingHom q = q) :
    ∃ Q : MvPolynomial J k, MvPolynomial.map (algebraMap k E) Q = q := by
  classical
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro a ha
  obtain ⟨d, hd, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
  exact galois_fixed_element_descends (q.coeff d) (fun g => by
    have h := congrArg (fun p : MvPolynomial J E => p.coeff d) (hfix g)
    rw [MvPolynomial.coeff_map] at h
    change g (q.coeff d) = q.coeff d at h
    exact h)

end PfaffianDescent

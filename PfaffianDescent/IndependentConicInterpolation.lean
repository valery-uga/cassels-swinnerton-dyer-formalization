import PfaffianDescent.ConicThroughFive

namespace PfaffianDescent
open Module

/-- Elementary interpolation, independent of degree-five descent: fewer than
six evaluation conditions on the six coefficients of a plane conic. -/
theorem exists_conic_through_algebra_finrank_lt_six
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] (hdim : finrank K A < 6) (x : Fin 3 → A) :
    ∃ q : MvPolynomial (Fin 3) K,
      q ≠ 0 ∧ q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K A) x = 0 := by
  let E : (Fin 6 → K) →ₗ[K] A :=
    (MvPolynomial.aeval x).toLinearMap.comp conicPolynomial
  have hker : LinearMap.ker E ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hdim)
  obtain ⟨c, hc, hcnz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨conicPolynomial c, ?_, conicPolynomial_homogeneous c, hc⟩
  intro h
  apply hcnz
  apply conicPolynomial_injective
  exact h.trans (map_zero conicPolynomial).symm

end PfaffianDescent

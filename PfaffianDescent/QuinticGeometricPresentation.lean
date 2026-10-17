import PfaffianDescent.QuinticGeometricPosition
import PfaffianDescent.FivePointAlgebraPresentation

namespace PfaffianDescent

/-- The note's noncoplanar degree-five presentation, with the splitting field,
conjugate general position, and ground-field matrices all constructed internally. -/
theorem quintic_geometric_pfaffian_presentation
    {K A : Type*} [Field K] [CharZero K] [Field A] [Algebra K A] [FiniteDimensional K A]
    (hdim : Module.finrank K A = 5) (p : Vec A 4) (hp : LinearIndependent K p)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (hF : MvPolynomial.eval₂ (algebraMap K A) p f = 0) :
    ∃ P : Fin 4 → Mat K 6, (∀ i, IsAlternating (P i)) ∧ (pfaffianCubic P).toMvPolynomial = f := by
  let ev := quinticSplittingEmbeddings hdim
  exact five_point_algebra_polynomial_presentation hdim ev ev.injective p
    (quintic_independent_coordinates_general_position hdim p hp) f hf hF

end PfaffianDescent

import PfaffianDescent.ConicCubicHilbert
import PfaffianDescent.ProjectiveFiniteOfHilbertBound

namespace PfaffianDescent
open AlgebraicGeometry Module
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K]

/-- A relatively prime plane conic and cubic define an actual finite projective
intersection scheme over the ground field. -/
theorem conic_cubic_intersection_finite (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f) :
    IsFinite (toBase (conicCubicHomogeneousIdeal q f hq hf)) := by
  apply projective_finite_of_hilbert_bound (conicCubicHomogeneousIdeal q f hq hf) 5 6
  intro n hn
  change finrank K (conicCubicComponent q f n) ≤ 6
  have h := conic_cubic_hilbert_six q f hq hf hq0 hrel (n-5)
  rw [Nat.sub_add_cancel hn] at h
  exact h.le

end
end PfaffianDescent

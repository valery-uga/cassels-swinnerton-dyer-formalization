import PfaffianDescent.ConicCubicFiniteIntersection
import PfaffianDescent.ProjectiveLengthOfHilbertAnyField

namespace PfaffianDescent
open AlgebraicGeometry Module
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K]

/-- The actual projective intersection of a coprime plane conic and cubic
is finite of scheme-theoretic length six. -/
theorem conic_cubic_intersection_length_six_anyField (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f) :
    letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
    AllCharacteristics.finiteSchemeRank (toBase (conicCubicHomogeneousIdeal q f hq hf)) = 6 := by
  letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
  apply projective_length_of_eventual_hilbert_anyField (conicCubicHomogeneousIdeal q f hq hf) 5 6
  intro n hn
  change finrank K (conicCubicComponent q f n) = 6
  have h := conic_cubic_hilbert_six q f hq hf hq0 hrel (n-5)
  rwa [Nat.sub_add_cancel hn] at h

end
end PfaffianDescent

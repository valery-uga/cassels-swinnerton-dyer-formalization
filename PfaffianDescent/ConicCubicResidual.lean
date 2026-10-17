import PfaffianDescent.ConicCubicLength
import PfaffianDescent.FiniteSchemeResidual

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K] [Infinite K]

/-- For the actual conic/cubic intersection, removing any length-five closed
subscheme gives its annihilator residual subscheme of length one. -/
theorem conic_cubic_residual_length_one (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f)
    {Z : Scheme.{u}} (i : Z ⟶ scheme (conicCubicHomogeneousIdeal q f hq hf))
    [IsClosedImmersion i]
    (hZ : letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
      AllCharacteristics.finiteSchemeRank (i ≫ toBase (conicCubicHomogeneousIdeal q f hq hf)) = 5) :
    letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
    AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i (toBase (conicCubicHomogeneousIdeal q f hq hf)) ≫
        toBase (conicCubicHomogeneousIdeal q f hq hf)) = 1 := by
  letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
  exact finite_scheme_residual_length_one i _
    (conic_cubic_intersection_length_six q f hq hf hq0 hrel) hZ

/-- The residual closed subscheme supplies a rational point on the actual
projective intersection of a conic and cubic. -/
theorem conic_cubic_residual_section (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f)
    {Z : Scheme.{u}} (i : Z ⟶ scheme (conicCubicHomogeneousIdeal q f hq hf))
    [IsClosedImmersion i]
    (hZ : letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
      AllCharacteristics.finiteSchemeRank (i ≫ toBase (conicCubicHomogeneousIdeal q f hq hf)) = 5) :
    ∃ s : Spec (.of K) ⟶ scheme (conicCubicHomogeneousIdeal q f hq hf),
      s ≫ toBase (conicCubicHomogeneousIdeal q f hq hf) = 𝟙 _ := by
  letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
  obtain ⟨s, hs⟩ := finite_scheme_residual_section i _
    (conic_cubic_intersection_length_six q f hq hf hq0 hrel) hZ
  exact ⟨s ≫ finiteClosedResidualι i _, (Category.assoc _ _ _).trans hs⟩

end
end PfaffianDescent

import PfaffianDescent.FiniteProjectiveChart
import PfaffianDescent.LinearChartCoordinates

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K] [Infinite K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite projective closed subscheme has global normalized homogeneous
coordinates generating its actual finite algebra and satisfying every
homogeneous equation of its ambient projective scheme. -/
theorem finite_projective_closed_subscheme_coordinates
    (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ p : σ → Γ(Z, ⊤), Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) p) ∧
      ∀ (q : MvPolynomial σ K) (d : ℕ), q.IsHomogeneous d → q ∈ I.toIdeal →
        q.eval₂ (algebraMap K Γ(Z, ⊤)) p = 0 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨z, hz, g, hgs, hg, _⟩ := finite_projective_closed_subscheme_chart I i
  let p : σ → Γ(Z, ⊤) := fun j => g (linearChartCoordinate I z hz j)
  have he : eval₂Hom (algebraMap K Γ(Z, ⊤)) p =
      g.comp (eval₂Hom (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
        (linearChartCoordinate I z hz)) := by
    apply RingHom.ext
    intro q
    change q.eval₂ (algebraMap K Γ(Z, ⊤)) p = g (q.eval₂ _ _)
    rw [hom_eval₂, hg]
  refine ⟨p, ?_, ?_⟩
  · rw [he]
    exact hgs.comp (eval₂_linearChartCoordinate_surjective I z hz)
  · intro q d hq hI
    change eval₂Hom (algebraMap K Γ(Z, ⊤)) p q = 0
    rw [he, RingHom.comp_apply]
    rw [show eval₂Hom _ (linearChartCoordinate I z hz) q = 0 from
      eval₂_linearChartCoordinate_eq_zero I z hz q hq hI, map_zero]

end
end PfaffianDescent

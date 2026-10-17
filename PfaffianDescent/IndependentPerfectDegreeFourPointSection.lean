import PfaffianDescent.IndependentPerfectNoncoplanarClosedQuarticSection
import PfaffianDescent.IndependentCoplanarQuarticPoint

/- SOURCE ONLY / UNVERIFIED. Chapter4 perfect-field degree-four point
statement, assembled solely from independent coplanar and tangent-net
noncoplanar branches. No Chapter3/strong degree-four endpoint shortcut. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem independent_perfectField_degree_four_closed_point_rational_section
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (h4 : (hypersurfaceToBase p hp).residueDegree x.1 = 4) :
    ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  classical
  by_cases hplane : ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c) ∈
        x.1.asHomogeneousIdeal.toIdeal
  · obtain ⟨c, hc, hcx⟩ := hplane
    exact cubic_coplanar_degree_four_independent_conic_secant_descent p hp x h4 c hc hcx
  · exact independent_perfectField_noncoplanarClosedQuarticPoint_rational_section
      p hp hp0 x h4 hplane

end PfaffianDescent

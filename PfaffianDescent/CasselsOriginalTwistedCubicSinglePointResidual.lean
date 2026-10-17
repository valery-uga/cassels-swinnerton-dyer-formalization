import PfaffianDescent.CasselsOriginalTwistedCubicPrescribedResidual
import PfaffianDescent.CasselsSmallEffectiveCycleSinglePoint
import PfaffianDescent.IndependentCoplanarQuarticPoint
import PfaffianDescent.CoplanarConicDescent

/-! SOURCE ONLY. Complete prescribed Cassels residual under S(k)=empty:
construct the original containing curve and whole rank9 intersection internally,
then identify its actual complement as ONE closed point of the other degree. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Literal SAME-P Cassels containing-curve/residual closed-point conclusion.
The actual intersection-cycle identity is preserved; no residual cycle is
supplied to this original-P endpoint. Noncoplanarity is the manuscript branch
hypothesis after lem:position, rather than a desired construction certificate. -/
theorem perfectField_original_closedPoint_cassels_prescribed_singlePoint_residual
    {K : Type u} [Field K] [PerfectField K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (P : closedPoints (hypersurface F hF))
    (hdim : (hypersurfaceToBase F hF).residueDegree P.1 = 4 ∨
      (hypersurfaceToBase F hF).residueDegree P.1 = 5)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal F hF).toIdeal (homogeneousLinearForm c) ∈
        P.1.asHomogeneousIdeal.toIdeal)
    (hnone : ¬ ∃ s : Spec (.of K) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _) :
    ∃ B : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K),
      QuarticNet.GroundTwistedCubicPresentation B ∧
      ∃ l : Spec (.of ((hypersurface F hF).residueField P.1)) ⟶
          scheme (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF),
        IsClosedImmersion l ∧
        l ≫ casselsTwistedCubicIntersectionToSurface B F hF =
          (hypersurface F hF).fromSpecResidueField P.1 ∧
        ∃ hfinite : IsFinite
            (toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)),
          letI := hfinite
          finiteSchemeRank (toBase
            (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)) = 9 ∧
          ∃ Q : closedPoints (hypersurface F hF),
            pushforwardClosedCycle (casselsTwistedCubicIntersectionToSurface B F hF)
                (finiteSchemeFundamentalCycle (toBase
                  (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF))) =
              Finsupp.single Q 1 + Finsupp.single P 1 ∧
            (hypersurfaceToBase F hF).residueDegree Q.1 =
              9 - (hypersurfaceToBase F hF).residueDegree P.1 := by
  obtain ⟨B, hB, l, hl, hfactor, hcontained | hresidual⟩ :=
    perfectField_original_closedPoint_cassels_containing_curve_and_prescribed_residual
      F hF P hdim hplane
  · exact (hnone hcontained.2).elim
  · obtain ⟨hfinite, hW, r, hcycle, hdegree⟩ := hresidual
    letI := hfinite
    have hsmall : EffectiveZeroCycle.degree (hypersurfaceToBase F hF) r = 4 ∨
        EffectiveZeroCycle.degree (hypersurfaceToBase F hF) r = 5 := by
      rcases hdim with h4 | h5
      · right
        omega
      · left
        omega
    obtain ⟨Q, hsingle, hQ⟩ :=
      cubic_no_section_effective_degree_four_or_five_eq_single F hF hnone r hsmall
    refine ⟨B, hB, l, hl, hfactor, hfinite, hW, Q, ?_, hQ.trans hdegree⟩
    rw [hsingle] at hcycle
    exact hcycle

/-- The standing absence of ground points derives ordinary noncoplanarity
from the actual elementary conic/secant providers. Finite fields are handled
by their genuine cubic-point theorem, not an Infinite-field assumption. -/
theorem cubic_no_section_degree_four_or_five_not_coplanar
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (P : closedPoints (hypersurface F hF))
    (hdim : (hypersurfaceToBase F hF).residueDegree P.1 = 4 ∨
      (hypersurfaceToBase F hF).residueDegree P.1 = 5)
    (hnone : ¬ ∃ s : Spec (.of K) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _) :
    ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal F hF).toIdeal (homogeneousLinearForm c) ∈
        P.1.asHomogeneousIdeal.toIdeal := by
  classical
  rintro ⟨c, hc, hplane⟩
  apply hnone
  rcases hdim with h4 | h5
  · exact cubic_coplanar_degree_four_independent_conic_secant_descent
      F hF P h4 c hc hplane
  · rcases finite_or_infinite K with hfinite | hinfinite
    · letI : Finite K := hfinite
      exact finite_field_cubic_has_rational_section F hF
    · letI : Infinite K := hinfinite
      exact cubic_coplanar_degree_five_conic_descent F hF P h5 c hc hplane

/-- Full original-P endpoint under the manuscript standing S(k)=empty,
with noncoplanarity derived internally and no supplied curve/residual data. -/
theorem perfectField_original_closedPoint_cassels_prescribed_singlePoint_residual_of_no_section
    {K : Type u} [Field K] [PerfectField K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (P : closedPoints (hypersurface F hF))
    (hdim : (hypersurfaceToBase F hF).residueDegree P.1 = 4 ∨
      (hypersurfaceToBase F hF).residueDegree P.1 = 5)
    (hnone : ¬ ∃ s : Spec (.of K) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _) :
    ∃ B : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K),
      QuarticNet.GroundTwistedCubicPresentation B ∧
      ∃ l : Spec (.of ((hypersurface F hF).residueField P.1)) ⟶
          scheme (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF),
        IsClosedImmersion l ∧
        l ≫ casselsTwistedCubicIntersectionToSurface B F hF =
          (hypersurface F hF).fromSpecResidueField P.1 ∧
        ∃ hfinite : IsFinite
            (toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)),
          letI := hfinite
          finiteSchemeRank (toBase
            (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)) = 9 ∧
          ∃ Q : closedPoints (hypersurface F hF),
            pushforwardClosedCycle (casselsTwistedCubicIntersectionToSurface B F hF)
                (finiteSchemeFundamentalCycle (toBase
                  (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF))) =
              Finsupp.single Q 1 + Finsupp.single P 1 ∧
            (hypersurfaceToBase F hF).residueDegree Q.1 =
              9 - (hypersurfaceToBase F hF).residueDegree P.1  := by
  exact perfectField_original_closedPoint_cassels_prescribed_singlePoint_residual
    F hF P hdim (cubic_no_section_degree_four_or_five_not_coplanar F hF P hdim hnone) hnone

end PfaffianDescent

import PfaffianDescent.CasselsOriginalPointContainingTwistedCubic
import PfaffianDescent.FiniteClosedSubschemeCycleComplement
import AllCharacteristics.ClosedPointRank

/-! SOURCE ONLY. The prescribed SAME-P Cassels residual, preserving actual
whole intersection, original surface, and canonical fundamental-cycle equality.
No residual/effectivity/degree/containing-curve conclusion is a final input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The point removed from the WHOLE intersection is exactly ORIGINAL[P]
with coefficient one after projection to the original cubic surface. -/
theorem casselsIntersection_removedOriginalPoint_cycle
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (B : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (P : closedPoints (hypersurface F hF))
    (l : Spec (.of ((hypersurface F hF).residueField P.1)) ⟶
      scheme (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF))
    [IsClosedImmersion l]
    [IsFinite (toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF))]
    (hfactor : l ≫ casselsTwistedCubicIntersectionToSurface B F hF =
      (hypersurface F hF).fromSpecResidueField P.1) :
    pushforwardClosedCycle (casselsTwistedCubicIntersectionToSurface B F hF)
      (pushforwardClosedCycle l (finiteSchemeFundamentalCycle
        (l ≫ toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)))) =
      Finsupp.single P 1 := by
  classical
  let L := (hypersurface F hF).residueField P.1
  let y : closedPoints (Spec (.of L)) :=
    ⟨IsLocalRing.closedPoint L, isClosed_singleton⟩
  have hfund : finiteSchemeFundamentalCycle
      (l ≫ toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)) =
        Finsupp.single y 1 := by
    change fundamentalZeroCycle (Spec (.of L)) = _
    exact fundamentalZeroCycle_Spec_field L y
  have himage : closedPointMap (casselsTwistedCubicIntersectionToSurface B F hF)
      (closedPointMap l y) = P := by
    apply Subtype.ext
    change casselsTwistedCubicIntersectionToSurface B F hF
      (l (IsLocalRing.closedPoint L)) = P.1
    calc
      _ = (hypersurface F hF).fromSpecResidueField P.1
          (IsLocalRing.closedPoint L) :=
        congrArg (fun f => f (IsLocalRing.closedPoint L)) hfactor
      _ = P.1 := (hypersurface F hF).fromSpecResidueField_apply P.1 _
  rw [hfund]
  unfold pushforwardClosedCycle
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, himage]

/-- Native residual consumer: rank9 comes from the actual ground twisted
cubic, and the removed cycle/rank comes from the SAME original closed point.
The factorization is an ordinary geometric helper input, discharged by the
literal original caller below. -/
theorem groundTwistedCubic_originalPoint_prescribed_effective_residual
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (B : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hB : QuarticNet.GroundTwistedCubicPresentation B) (hnot : F ∉ B.toIdeal)
    (P : closedPoints (hypersurface F hF))
    (l : Spec (.of ((hypersurface F hF).residueField P.1)) ⟶
      scheme (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF))
    [IsClosedImmersion l]
    (hfactor : l ≫ casselsTwistedCubicIntersectionToSurface B F hF =
      (hypersurface F hF).fromSpecResidueField P.1) :
    ∃ hfinite : IsFinite
        (toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)),
      letI := hfinite
      finiteSchemeRank (toBase
        (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)) = 9 ∧
      ∃ r : EffectiveZeroCycle (hypersurface F hF),
        pushforwardClosedCycle (casselsTwistedCubicIntersectionToSurface B F hF)
            (finiteSchemeFundamentalCycle (toBase
              (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF))) =
          r + Finsupp.single P 1 ∧
        EffectiveZeroCycle.degree (hypersurfaceToBase F hF) r =
          9 - (hypersurfaceToBase F hF).residueDegree P.1 := by
  obtain ⟨hfinite, hW⟩ := hB.cubicIntersection_finite_rank_nine_anyField F hF hnot
  letI := hfinite
  let J := QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF
  let g := toBase J
  let c := casselsTwistedCubicIntersectionToSurface B F hF
  have hc : c ≫ hypersurfaceToBase F hF = g :=
    casselsTwistedCubicIntersectionToSurface_toBase B F hF
  have hbase : l ≫ g = (hypersurface F hF).fromSpecResidueField P.1 ≫
      hypersurfaceToBase F hF := by
    rw [← hc, ← Category.assoc, hfactor]
  have hP : finiteSchemeRank (l ≫ g) =
      (hypersurfaceToBase F hF).residueDegree P.1 := by
    rw [finiteSchemeRank_eq_finrank, hbase, ← finiteSchemeRank_eq_finrank]
    exact closedPoint_finiteSchemeRank_eq_residueDegree (hypersurfaceToBase F hF) P
  let rW := finiteClosedSubschemeComplementCycle l g
  let r := pushforwardClosedCycle c rW
  have hcycle : pushforwardClosedCycle c (finiteSchemeFundamentalCycle g) =
      r + Finsupp.single P 1 := by
    rw [finiteClosedSubschemeComplementCycle_add l g]
    have hadd : pushforwardClosedCycle c
        (rW + pushforwardClosedCycle l (finiteSchemeFundamentalCycle (l ≫ g))) =
      pushforwardClosedCycle c rW + pushforwardClosedCycle c
        (pushforwardClosedCycle l (finiteSchemeFundamentalCycle (l ≫ g))) := by
      unfold pushforwardClosedCycle
      exact Finsupp.mapDomain_add
    rw [hadd, casselsIntersection_removedOriginalPoint_cycle F hF B P l hfactor]
  have hdegree : EffectiveZeroCycle.degree (hypersurfaceToBase F hF) r =
      9 - (hypersurfaceToBase F hF).residueDegree P.1 := by
    rw [degree_pushforwardClosedCycle, hc, finiteClosedSubschemeComplementCycle_degree,
      hW, hP]
  exact ⟨hfinite, hW, r, hcycle, hdegree⟩

/-- Literal Cassels321--354 from ORIGINAL perfect-field degree4/5 closed P:
construct the containing twisted cubic and SAME-P intersection factorization;
then derive contained-curve or prescribed rank9/effective residual9-degree(P).
No curve, rank, residual identity, effectivity, or rationality certificate occurs
among the hypotheses. -/
theorem perfectField_original_closedPoint_cassels_containing_curve_and_prescribed_residual
    {K : Type u} [Field K] [PerfectField K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (P : closedPoints (hypersurface F hF))
    (hdim : (hypersurfaceToBase F hF).residueDegree P.1 = 4 ∨
      (hypersurfaceToBase F hF).residueDegree P.1 = 5)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal F hF).toIdeal (homogeneousLinearForm c) ∈
        P.1.asHomogeneousIdeal.toIdeal) :
    ∃ B : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K),
      QuarticNet.GroundTwistedCubicPresentation B ∧
      ∃ l : Spec (.of ((hypersurface F hF).residueField P.1)) ⟶
          scheme (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF),
        IsClosedImmersion l ∧
        l ≫ casselsTwistedCubicIntersectionToSurface B F hF =
          (hypersurface F hF).fromSpecResidueField P.1 ∧
        ((F ∈ B.toIdeal ∧
          ∃ s : Spec (.of K) ⟶ hypersurface F hF,
            s ≫ hypersurfaceToBase F hF = 𝟙 _) ∨
        (∃ hfinite : IsFinite
            (toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)),
          letI := hfinite
          finiteSchemeRank (toBase
            (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)) = 9 ∧
          ∃ r : EffectiveZeroCycle (hypersurface F hF),
            pushforwardClosedCycle (casselsTwistedCubicIntersectionToSurface B F hF)
                (finiteSchemeFundamentalCycle (toBase
                  (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF))) =
              r + Finsupp.single P 1 ∧
            EffectiveZeroCycle.degree (hypersurfaceToBase F hF) r =
              9 - (hypersurfaceToBase F hF).residueDegree P.1)) := by
  classical
  obtain ⟨B, hB, l, hl, hfactor⟩ :=
    perfectField_original_closedPoint_exists_containing_twistedCubic F hF P hdim hplane
  letI : IsClosedImmersion l := hl
  refine ⟨B, hB, l, hl, hfactor, ?_⟩
  by_cases hmem : F ∈ B.toIdeal
  · left
    obtain ⟨c, hcAmbient, hcBase, s, hs⟩ := hB.contained_cubic_section F hF hmem
    exact ⟨hmem, s, hs⟩
  · right
    exact groundTwistedCubic_originalPoint_prescribed_effective_residual
      F hF B hB hmem P l hfactor

end PfaffianDescent

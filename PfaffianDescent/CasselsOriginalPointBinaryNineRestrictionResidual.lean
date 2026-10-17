import PfaffianDescent.GroundTwistedCubicActualCubicRestrictionScheme
import PfaffianDescent.CasselsOriginalTwistedCubicPrescribedResidual

/-! SOURCE ONLY. Literal original-P binary-nine/restriction consumer.
The ORIGINAL chosen curve, zero scheme, whole intersection and prescribed
original-P effective residual are internally constructed together. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original residue-field point is carried to the actual native
restriction zero scheme by the SAME whole-intersection Iso, preserving its
EXACT original surface point morphism. No point-lift outcome is input. -/
theorem perfectField_original_closedPoint_binaryNineRestriction_and_prescribedResidual
    {K : Type u} [Field K] [PerfectField K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (P : closedPoints (hypersurface F hF))
    (hdim : (hypersurfaceToBase F hF).residueDegree P.1 = 4 ∨
      (hypersurfaceToBase F hF).residueDegree P.1 = 5)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal F hF).toIdeal (homogeneousLinearForm c) ∈
        P.1.asHomogeneousIdeal.toIdeal) :
    ∃ B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      ∃ hB : QuarticNet.GroundTwistedCubicPresentation B,
      ∃ z : Spec (.of ((hypersurface F hF).residueField P.1)) ⟶
          pullback hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF),
        IsClosedImmersion z ∧
        z ≫ pullback.snd hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) =
          (hypersurface F hF).fromSpecResidueField P.1 ∧
        (((hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K) = 0 ∧
            ∃ s : Spec (.of K) ⟶ hypersurface F hF,
              s ≫ hypersurfaceToBase F hF = 𝟙 _) ∨
          ((hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K) ≠ 0 ∧
            (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K).totalDegree = 9 ∧
            ∃ hfiniteZero : IsFinite
                (pullback.snd hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) ≫
                  hypersurfaceToBase F hF),
              @AllCharacteristics.finiteSchemeRank K _ _
                  (pullback.snd hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) ≫
                    hypersurfaceToBase F hF) hfiniteZero = 9 ∧
              ∃ hfiniteWhole : IsFinite
                  (toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)),
                letI := hfiniteWhole
                AllCharacteristics.finiteSchemeRank
                    (toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF)) = 9 ∧
                ∃ r : AllCharacteristics.EffectiveZeroCycle (hypersurface F hF),
                  AllCharacteristics.pushforwardClosedCycle
                      (casselsTwistedCubicIntersectionToSurface B F hF)
                      (PfaffianDescent.finiteSchemeFundamentalCycle
                        (toBase (QuarticNet.groundTwistedCubicCubicIntersectionIdeal B F hF))) =
                    r + Finsupp.single P 1 ∧
                  AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase F hF) r =
                    9 - (hypersurfaceToBase F hF).residueDegree P.1)) := by
  classical
  obtain ⟨B, hB, l, hl, hfactor⟩ :=
    perfectField_original_closedPoint_exists_containing_twistedCubic F hF P hdim hplane
  letI : IsClosedImmersion l := hl
  let e := hB.actualRestrictedCubicZeroSchemeIso F hF
  let z := l ≫ e.hom
  have hz : IsClosedImmersion z := IsClosedImmersion.comp l e.hom
  have hzfactor : z ≫ pullback.snd hB.actualAmbientParameterMap
      (hypersurfaceToAmbient F hF) = (hypersurface F hF).fromSpecResidueField P.1 := by
    exact (Category.assoc l e.hom _).trans
      ((congrArg (fun q => l ≫ q)
        (hB.actualRestrictedCubicZeroSchemeIso_surface F hF)).trans hfactor)
  refine ⟨B, hB, z, hz, hzfactor, ?_⟩
  by_cases hmem : F ∈ B.toIdeal
  · left
    obtain ⟨c, hcAmbient, hcBase, s, hs⟩ := hB.contained_cubic_section F hF hmem
    exact ⟨(hB.literalRestrictedBinaryNine_zero_iff F hF).mpr hmem, s, hs⟩
  · right
    obtain ⟨hn, hdeg⟩ := hB.literalRestrictedBinaryNine_nonzero_degree F hF hmem
    obtain ⟨hfiniteZero, hZero⟩ := hB.actualRestrictedCubicZeroScheme_finite_rank_nine F hF hmem
    exact ⟨hn, hdeg, hfiniteZero, hZero,
      groundTwistedCubic_originalPoint_prescribed_effective_residual F hF B hB hmem P l hfactor⟩

end PfaffianDescent

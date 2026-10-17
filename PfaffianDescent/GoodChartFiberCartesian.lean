import PfaffianDescent.GoodChartFiberFunctions
import PfaffianDescent.GoodGraphFiberClosedChart

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The computed graph-fiber scheme is the actual fiber of the chosen incidence chart. -/
theorem goodGraphFiber_chart_isPullback :
    IsPullback (goodGraphFiberToIncidenceChart K) (goodGraphFiberToBase K)
      (incidenceChartToTriples K goodChartPermutation) (goodTripleSection K) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk (goodGraphFiberToIncidenceChart K)
    (goodGraphFiberToBase K) (goodGraphFiberToIncidenceChart_triples K))
  refine PullbackCone.IsLimit.mk (goodGraphFiberToIncidenceChart_triples K)
    (fun s => goodChartFiberLift K s.fst s.snd s.condition)
    (fun s => goodChartFiberLift_toChart K s.fst s.snd s.condition)
    (fun s => goodChartFiberLift_toBase K s.fst s.snd s.condition) ?_
  intro s m hm _
  apply (cancel_mono (goodGraphFiberToIncidenceChart K)).mp
  exact hm.trans (goodChartFiberLift_toChart K s.fst s.snd s.condition).symm

noncomputable def goodIncidenceChartFiber : Scheme.{u} :=
  pullback (incidenceChartToTriples K goodChartPermutation) (goodTripleSection K)

/-- An isomorphism of actual schemes, obtained from the universal property on all test schemes. -/
noncomputable def goodGraphFiberChartIso : goodGraphFiberScheme K ≅ goodIncidenceChartFiber K :=
  (goodGraphFiber_chart_isPullback K).isoPullback

lemma goodGraphFiberChartIso_toBase :
    (goodGraphFiberChartIso K).hom ≫ pullback.snd _ _ = goodGraphFiberToBase K :=
  (goodGraphFiber_chart_isPullback K).isoPullback_hom_snd

/-- The graph-fiber chart is the pullback of the chosen open incidence chart. -/
theorem goodGraphFiber_global_chart_isPullback :
    IsPullback (goodGraphFiberToGlobalFiber K) (goodGraphFiberToIncidenceChart K)
      (pullback.fst (incidenceToTriples K) (goodTripleSection K))
      (incidenceChartι K goodChartPermutation) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd (incidenceToTriples K) (goodTripleSection K))
    (h₂₂ := incidenceToTriples K)
  · change IsPullback (goodGraphFiberToGlobalFiber K ≫ goodIncidenceFiberToBase K)
      (goodGraphFiberToIncidenceChart K) (goodTripleSection K)
      (incidenceChartι K goodChartPermutation ≫ incidenceToTriples K)
    rw [goodGraphFiberToGlobalFiber_toBase, incidenceChartι_toTriples]
    exact (goodGraphFiber_chart_isPullback K).flip
  · exact goodGraphFiberToGlobalFiber_toIncidence K
  · exact (IsPullback.of_hasPullback (incidenceToTriples K) (goodTripleSection K)).flip

/-- The finite étale degree-two graph scheme is an actual open subscheme of the full good fiber. -/
instance goodGraphFiberToGlobalFiber_open : IsOpenImmersion (goodGraphFiberToGlobalFiber K) := by
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (goodGraphFiber_global_chart_isPullback K).flip
    (incidenceChartι_isOpenImmersion K goodChartPermutation)

end
end PfaffianDescent

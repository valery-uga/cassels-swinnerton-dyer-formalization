import PfaffianDescent.GoodPairChartFiberFunctions
import PfaffianDescent.GoodPairGraphClosedChart

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

/-- The computed graph-fiber scheme is the actual fiber of the chosen incidence chart. -/
theorem goodPairGraph_chart_isPullback :
    IsPullback (goodPairGraphToIncidenceChart K) (goodPairGraphToBase K)
      (incidenceChartToTriples K goodChartPermutation) (goodPairTripleSection K) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk (goodPairGraphToIncidenceChart K)
    (goodPairGraphToBase K) (goodPairGraphToIncidenceChart_triples K))
  refine PullbackCone.IsLimit.mk (goodPairGraphToIncidenceChart_triples K)
    (fun s => goodPairChartFiberLift K s.fst s.snd s.condition)
    (fun s => goodPairChartFiberLift_toChart K s.fst s.snd s.condition)
    (fun s => goodPairChartFiberLift_toBase K s.fst s.snd s.condition) ?_
  intro s m hm _
  apply (cancel_mono (goodPairGraphToIncidenceChart K)).mp
  exact hm.trans (goodPairChartFiberLift_toChart K s.fst s.snd s.condition).symm

noncomputable def goodPairIncidenceChartFiber : Scheme.{u} :=
  pullback (incidenceChartToTriples K goodChartPermutation) (goodPairTripleSection K)

/-- An isomorphism of actual schemes, obtained from the universal property on all test schemes. -/
noncomputable def goodPairGraphChartIso : goodPairGraphScheme K ≅ goodPairIncidenceChartFiber K :=
  (goodPairGraph_chart_isPullback K).isoPullback

lemma goodPairGraphChartIso_toBase :
    (goodPairGraphChartIso K).hom ≫ pullback.snd _ _ = goodPairGraphToBase K :=
  (goodPairGraph_chart_isPullback K).isoPullback_hom_snd

/-- The graph-fiber chart is the pullback of the chosen open incidence chart. -/
theorem goodPairGraph_global_chart_isPullback :
    IsPullback (goodPairGraphToGlobalFiber K) (goodPairGraphToIncidenceChart K)
      (pullback.fst (incidenceToTriples K) (goodPairTripleSection K))
      (incidenceChartι K goodChartPermutation) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd (incidenceToTriples K) (goodPairTripleSection K))
    (h₂₂ := incidenceToTriples K)
  · change IsPullback (goodPairGraphToGlobalFiber K ≫ goodPairIncidenceFiberToBase K)
      (goodPairGraphToIncidenceChart K) (goodPairTripleSection K)
      (incidenceChartι K goodChartPermutation ≫ incidenceToTriples K)
    rw [goodPairGraphToGlobalFiber_toBase, incidenceChartι_toTriples]
    exact (goodPairGraph_chart_isPullback K).flip
  · exact goodPairGraphToGlobalFiber_toIncidence K
  · exact (IsPullback.of_hasPullback (incidenceToTriples K) (goodPairTripleSection K)).flip

/-- The first-two-form graph scheme is an actual open subscheme of the full first-two-form fiber. -/
instance goodPairGraphToGlobalFiber_open : IsOpenImmersion (goodPairGraphToGlobalFiber K) := by
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (goodPairGraph_global_chart_isPullback K).flip
    (incidenceChartι_isOpenImmersion K goodChartPermutation)

end
end PfaffianDescent

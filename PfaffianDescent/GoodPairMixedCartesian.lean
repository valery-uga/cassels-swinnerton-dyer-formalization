import PfaffianDescent.GoodPairMixedFiberFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

/-- Each of the eight affine slope schemes is the actual fiber of its incidence chart. -/
theorem goodMixedPair_chart_isPullback (h2 : IsUnit (2 : K)) (ε : Fin 3 → Bool) :
    IsPullback (goodMixedPairToIncidenceChart K ε) (goodMixedPairToBase K)
      (incidenceChartToTriples K (goodMixedChartPermutation ε)) (goodPairTripleSection K) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk (goodMixedPairToIncidenceChart K ε)
    (goodMixedPairToBase K) (goodMixedPairToIncidenceChart_triples K ε))
  refine PullbackCone.IsLimit.mk (goodMixedPairToIncidenceChart_triples K ε)
    (fun s => goodMixedPairFiberLift K s.fst s.snd)
    (fun s => goodMixedPairFiberLift_toChart K h2 ε s.fst s.snd s.condition)
    (fun s => goodMixedPairFiberLift_toBase K s.fst s.snd) ?_
  intro s m hm _
  apply (cancel_mono (goodMixedPairToIncidenceChart K ε)).mp
  exact hm.trans (goodMixedPairFiberLift_toChart K h2 ε s.fst s.snd s.condition).symm

noncomputable def goodMixedPairChartIso (h2 : IsUnit (2 : K)) (ε : Fin 3 → Bool) :
    goodMixedPairScheme K ≅
      pullback (incidenceChartToTriples K (goodMixedChartPermutation ε)) (goodPairTripleSection K) :=
  (goodMixedPair_chart_isPullback K h2 ε).isoPullback

lemma goodMixedPair_global_chart_isPullback (h2 : IsUnit (2 : K)) (ε : Fin 3 → Bool) :
    IsPullback (goodMixedPairToGlobalFiber K ε) (goodMixedPairToIncidenceChart K ε)
      (pullback.fst (incidenceToTriples K) (goodPairTripleSection K))
      (incidenceChartι K (goodMixedChartPermutation ε)) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd (incidenceToTriples K) (goodPairTripleSection K))
    (h₂₂ := incidenceToTriples K)
  · change IsPullback (goodMixedPairToGlobalFiber K ε ≫ goodPairIncidenceFiberToBase K)
      (goodMixedPairToIncidenceChart K ε) (goodPairTripleSection K)
      (incidenceChartι K (goodMixedChartPermutation ε) ≫ incidenceToTriples K)
    rw [goodMixedPairToGlobalFiber_toBase, incidenceChartι_toTriples]
    exact (goodMixedPair_chart_isPullback K h2 ε).flip
  · exact goodMixedPairToGlobalFiber_toIncidence K ε
  · exact (IsPullback.of_hasPullback (incidenceToTriples K) (goodPairTripleSection K)).flip

/-- These are open immersions into the actual full scheme-theoretic pair locus. -/
lemma goodMixedPairToGlobalFiber_open (h2 : IsUnit (2 : K)) (ε : Fin 3 → Bool) :
    IsOpenImmersion (goodMixedPairToGlobalFiber K ε) := by
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (goodMixedPair_global_chart_isPullback K h2 ε).flip
    (incidenceChartι_isOpenImmersion K (goodMixedChartPermutation ε))

end
end PfaffianDescent

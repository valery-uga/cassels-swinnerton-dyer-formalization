import PfaffianDescent.GoodPairMixedCoordinates
import PfaffianDescent.GoodPairTripleScheme
import PfaffianDescent.GoodChartIncidencePoints

namespace PfaffianDescent
open Module
section
variable {K : Type*} [Field K] [CharZero K]

/-- Any field-valued incidence chart point over the good triple belongs to the
one of the eight product charts, irrespective of its initial chart label. -/
theorem goodPairIncidenceGraph_overlap
    (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints K)
    (hc : incidenceOriginalCoefficients i p = goodPairTripleSchemeCoefficients K) :
    ∃ ε : Fin 3 → Bool, Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation K (grassmannianChartChange i (goodMixedChartPermutation ε))) p.1) := by
  let e := graphCoordinatePermutation K i.symm
  let W := p.1.graph.map e.toLinearMap
  have hdim : finrank K W = 3 := by
    calc
      finrank K W = finrank K p.1.graph := e.finrank_map_eq _
      _ = finrank K (Fin 3 → K) := (graphSourceEquiv K p.1).finrank_eq
      _ = 3 := Module.finrank_fin_fun K
  have hforms (k : Fin 3) : incidenceOriginalForm i p k = goodPairAmbientAlternatingForm K k := by
    apply (alternatingCoordinates (incidenceAmbientBasis K)).injective
    funext s
    exact congrFun hc (k, s)
  have hiso (k : Fin 2) : alternatingRestriction K _ W
      (goodAmbientAlternatingForm K (k.castLE (by decide))) = 0 := by
    have hne : k.castLE (by decide : 2 ≤ 3) ≠ (2 : Fin 3) := by
      intro h
      have hv := congrArg Fin.val h
      have hk := k.isLt
      simp only [Fin.val_castLE, Fin.val_ofNat] at hv
      omega
    have hb : incidenceOriginalForm i p (k.castLE (by decide)) =
        goodAmbientAlternatingForm K (k.castLE (by decide)) :=
      (hforms _).trans (if_neg hne)
    exact congrArg (alternatingRestriction K _ W) hb |>.symm.trans
      (alternatingTransport_isotropic e p.1.graph W rfl (p.2 _).1 (p.2 _).2)
  obtain ⟨ε, u, hu⟩ := goodAmbientPair_exists_graph W hdim hiso
  refine ⟨ε, ?_⟩
  have he : p.1.graph.map
      (graphCoordinatePermutation K (grassmannianChartChange i (goodMixedChartPermutation ε))).toLinearMap =
      W.map (graphCoordinatePermutation K (goodMixedChartPermutation ε)).toLinearMap := by
    change p.1.graph.map (graphCoordinatePermutation K (grassmannianChartChange i (goodMixedChartPermutation ε))).toLinearMap =
      (p.1.graph.map (graphCoordinatePermutation K i.symm).toLinearMap).map
        (graphCoordinatePermutation K (goodMixedChartPermutation ε)).toLinearMap
    rw [← Submodule.map_comp]
    change p.1.graph.map (graphCoordinatePermutation K (grassmannianChartChange i (goodMixedChartPermutation ε))).toLinearMap =
      p.1.graph.map ((graphCoordinatePermutation K i.symm).trans
        (graphCoordinatePermutation K (goodMixedChartPermutation ε))).toLinearMap
    rw [graphCoordinatePermutation_trans]
    rfl
  apply (graphTransition_overlap_iff _ _).mpr
  rw [he, hu]
  exact graphChartQuotientMap_graph_bijective _

end
end PfaffianDescent

import PfaffianDescent.GoodAmbientIsotropicChart
import PfaffianDescent.GoodChartIncidencePoints

namespace PfaffianDescent
open Module
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Any field-valued incidence chart point over the good triple belongs to the
chosen good chart, irrespective of its initial chart label. -/
theorem goodIncidenceGraph_overlap
    (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints K)
    (hc : incidenceOriginalCoefficients i p = goodTripleSchemeCoefficients K) :
    Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation K (grassmannianChartChange i goodChartPermutation)) p.1) := by
  let e := graphCoordinatePermutation K i.symm
  let W := p.1.graph.map e.toLinearMap
  have hdim : finrank K W = 3 := by
    calc
      finrank K W = finrank K p.1.graph := e.finrank_map_eq _
      _ = finrank K (Fin 3 → K) := (graphSourceEquiv K p.1).finrank_eq
      _ = 3 := Module.finrank_fin_fun K
  have hforms (k : Fin 3) : incidenceOriginalForm i p k = goodAmbientAlternatingForm K k := by
    apply (alternatingCoordinates (incidenceAmbientBasis K)).injective
    funext s
    exact congrFun hc (k, s)
  have hiso (k : Fin 3) : alternatingRestriction K _ W (goodAmbientAlternatingForm K k) = 0 := by
    rw [← hforms k]
    exact alternatingTransport_isotropic e p.1.graph W rfl (p.2 k).1 (p.2 k).2
  obtain ⟨u, hu, _⟩ := goodAmbientIsotropic_exists_graph W hdim hiso
  have he : p.1.graph.map
      (graphCoordinatePermutation K (grassmannianChartChange i goodChartPermutation)).toLinearMap =
      W.map (graphCoordinatePermutation K goodChartPermutation).toLinearMap := by
    change p.1.graph.map (graphCoordinatePermutation K (grassmannianChartChange i goodChartPermutation)).toLinearMap =
      (p.1.graph.map (graphCoordinatePermutation K i.symm).toLinearMap).map
        (graphCoordinatePermutation K goodChartPermutation).toLinearMap
    rw [← Submodule.map_comp]
    change p.1.graph.map (graphCoordinatePermutation K (grassmannianChartChange i goodChartPermutation)).toLinearMap =
      p.1.graph.map ((graphCoordinatePermutation K i.symm).trans
        (graphCoordinatePermutation K goodChartPermutation)).toLinearMap
    rw [graphCoordinatePermutation_trans]
    rfl
  apply (graphTransition_overlap_iff _ _).mpr
  rw [he, hu]
  exact graphChartQuotientMap_graph_bijective _

end
end PfaffianDescent

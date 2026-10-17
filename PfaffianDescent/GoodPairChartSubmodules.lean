import PfaffianDescent.ProjectiveLineCharts
import PfaffianDescent.GoodPairMixedCoordinates

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

/-- The actual ambient submodule of a mixed incidence chart is the direct sum of its three lines. -/
lemma goodMixedChartSubmodule_blocks (ε : Fin 3 → Bool) (u : Fin 3 → R) :
    (grassmannianChartSubmodule R (goodMixedChartPermutation ε) (Matrix.diagonal u)).map
      (goodAmbientBlockEquiv R).toLinearMap = goodBlockMixedGraph R ε u := by
  apply Submodule.map_injective_of_injective (goodBlockCoordinateSwap R ε).injective
  rw [grassmannianChartSubmodule, ← Submodule.map_comp, ← Submodule.map_comp]
  change (Matrix.toLin' (Matrix.diagonal u)).graph.map
    (((graphCoordinatePermutation R (goodMixedChartPermutation ε).symm).trans
      (goodAmbientBlockEquiv R)).trans (goodBlockCoordinateSwap R ε)).toLinearMap = _
  have he : ((graphCoordinatePermutation R (goodMixedChartPermutation ε).symm).trans
      (goodAmbientBlockEquiv R)).trans (goodBlockCoordinateSwap R ε) = goodSplitBlockCoordinates R := by
    apply LinearEquiv.ext
    intro x
    change goodBlockCoordinateSwap R ε (goodAmbientBlockEquiv R
      (graphCoordinatePermutation R (goodMixedChartPermutation ε).symm x)) = _
    rw [← graphCoordinatePermutation_symm, goodMixedChart_inverse_coordinates]
    exact goodBlockCoordinateSwap_involutive R ε _
  rw [he, goodSplitBlockCoordinates_diagonal_graph, goodBlockMixedGraph_map_swap]

/-- Equality of ambient three-spaces gives equality of the represented projective line in each block. -/
lemma goodMixedChartSubmodule_components_eq (ε δ : Fin 3 → Bool) (u v : Fin 3 → R)
    (h : grassmannianChartSubmodule R (goodMixedChartPermutation ε) (Matrix.diagonal u) =
      grassmannianChartSubmodule R (goodMixedChartPermutation δ) (Matrix.diagonal v)) (i : Fin 3) :
    grassmannianChartSubmodule R (lineChartPermutation (ε i)) (lineChartMatrix R (u i)) =
      grassmannianChartSubmodule R (lineChartPermutation (δ i)) (lineChartMatrix R (v i)) := by
  apply Submodule.map_injective_of_injective (lineAmbientCoordinates R).injective
  rw [lineStandardSubmodule_eq_chart, lineStandardSubmodule_eq_chart]
  have hb := congrArg (fun W => W.map (goodAmbientBlockEquiv R).toLinearMap) h
  rw [goodMixedChartSubmodule_blocks, goodMixedChartSubmodule_blocks] at hb
  have hl := congrArg (fun W => goodBlockSubmodule R (Fin 2 → R) W i) hb
  rw [goodBlockMixedGraph_component, goodBlockMixedGraph_component] at hl
  exact hl

/-- Conversely, equality of the three line submodules determines the entire mixed graph. -/
lemma goodMixedChartSubmodule_eq_of_components (ε δ : Fin 3 → Bool) (u v : Fin 3 → R)
    (h : ∀ i : Fin 3,
      grassmannianChartSubmodule R (lineChartPermutation (ε i)) (lineChartMatrix R (u i)) =
        grassmannianChartSubmodule R (lineChartPermutation (δ i)) (lineChartMatrix R (v i))) :
    grassmannianChartSubmodule R (goodMixedChartPermutation ε) (Matrix.diagonal u) =
      grassmannianChartSubmodule R (goodMixedChartPermutation δ) (Matrix.diagonal v) := by
  have hl (i : Fin 3) : lineStandardSubmodule R (ε i) (u i) = lineStandardSubmodule R (δ i) (v i) := by
    have he := congrArg (fun W => W.map (lineAmbientCoordinates R).toLinearMap) (h i)
    rwa [lineStandardSubmodule_eq_chart, lineStandardSubmodule_eq_chart] at he
  apply Submodule.map_injective_of_injective (goodAmbientBlockEquiv R).injective
  rw [goodMixedChartSubmodule_blocks, goodMixedChartSubmodule_blocks]
  ext x
  rw [mem_goodBlockMixedGraph, mem_goodBlockMixedGraph]
  apply forall_congr'
  intro i
  change (x i ∈ lineStandardSubmodule R (ε i) (u i)) ↔ (x i ∈ lineStandardSubmodule R (δ i) (v i))
  rw [hl]

end
end PfaffianDescent

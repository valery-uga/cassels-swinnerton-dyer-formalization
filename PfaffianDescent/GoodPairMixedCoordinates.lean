import PfaffianDescent.GoodPairFieldCharts
import PfaffianDescent.GoodAmbientIsotropicChart

namespace PfaffianDescent
open Module

/-- Swap the two coordinate choices separately in the three blocks. -/
def goodBlockSwapPermutation (ε : Fin 3 → Bool) : Equiv.Perm (Fin 3 ⊕ Fin 3) where
  toFun := Sum.elim (fun i => if ε i then Sum.inr i else Sum.inl i)
    (fun i => if ε i then Sum.inl i else Sum.inr i)
  invFun := Sum.elim (fun i => if ε i then Sum.inr i else Sum.inl i)
    (fun i => if ε i then Sum.inl i else Sum.inr i)
  left_inv x := by
    rcases x with i | i <;> cases h : ε i <;> simp [h]
  right_inv x := by
    rcases x with i | i <;> cases h : ε i <;> simp [h]

/-- The eight standard product charts as actual permutations in the global Grassmannian atlas. -/
def goodMixedChartPermutation (ε : Fin 3 → Bool) : Equiv.Perm (Fin 3 ⊕ Fin 3) :=
  (goodBlockSwapPermutation ε).trans goodChartPermutation

section
variable (R : Type*) [CommRing R]

lemma goodSplitBlockCoordinates_swap (ε : Fin 3 → Bool) (x : (Fin 3 → R) × (Fin 3 → R)) :
    goodSplitBlockCoordinates R (graphCoordinatePermutation R (goodBlockSwapPermutation ε) x) =
      goodBlockCoordinateSwap R ε (goodSplitBlockCoordinates R x) := by
  funext i j
  fin_cases j
  · change Sum.elim x.1 x.2 (if ε i then Sum.inr i else Sum.inl i) =
      (if ε i then ![x.2 i, x.1 i] else ![x.1 i, x.2 i]) 0
    cases h : ε i <;> simp [h]
  · change Sum.elim x.1 x.2 (if ε i then Sum.inl i else Sum.inr i) =
      (if ε i then ![x.2 i, x.1 i] else ![x.1 i, x.2 i]) 1
    cases h : ε i <;> simp [h]

lemma goodMixedChartPermutation_coordinates (ε : Fin 3 → Bool)
    (x : (Fin 3 → R) × (Fin 3 → R)) :
    goodSplitBlockCoordinates R (graphCoordinatePermutation R (goodMixedChartPermutation ε) x) =
      goodBlockCoordinateSwap R ε (goodAmbientBlockEquiv R x) := by
  have he : graphCoordinatePermutation R (goodMixedChartPermutation ε) =
      (graphCoordinatePermutation R goodChartPermutation).trans
        (graphCoordinatePermutation R (goodBlockSwapPermutation ε)) :=
    (graphCoordinatePermutation_trans (R := R) goodChartPermutation (goodBlockSwapPermutation ε)).symm
  rw [he]
  change goodSplitBlockCoordinates R (graphCoordinatePermutation R (goodBlockSwapPermutation ε)
    (graphCoordinatePermutation R goodChartPermutation x)) = _
  rw [goodSplitBlockCoordinates_swap, goodChartPermutation_coordinates]
  rfl

lemma goodBlockCoordinateSwap_involutive (ε : Fin 3 → Bool) :
    Function.Involutive (goodBlockCoordinateSwap R ε) :=
  (goodBlockCoordinateSwap R ε).left_inv

lemma goodMixedChart_inverse_coordinates (ε : Fin 3 → Bool)
    (x : (Fin 3 → R) × (Fin 3 → R)) :
    goodAmbientBlockEquiv R ((graphCoordinatePermutation R (goodMixedChartPermutation ε)).symm x) =
      goodBlockCoordinateSwap R ε (goodSplitBlockCoordinates R x) := by
  have h := goodMixedChartPermutation_coordinates R ε
    ((graphCoordinatePermutation R (goodMixedChartPermutation ε)).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact ((congrArg (goodBlockCoordinateSwap R ε) h).trans
    (goodBlockCoordinateSwap_involutive R ε _)).symm

end
section
variable {K : Type*} [Field K] [CharZero K]

/-- Every ambient three-space isotropic for the first two forms belongs to one of the eight
specified charts of the actual Grassmannian atlas. -/
theorem goodAmbientPair_exists_graph
    (W : Submodule K ((Fin 3 → K) × (Fin 3 → K))) (hdim : finrank K W = 3)
    (hiso : ∀ k : Fin 2, alternatingRestriction K _ W (goodAmbientAlternatingForm K (k.castLE (by decide))) = 0) :
    ∃ ε : Fin 3 → Bool, ∃ u : Fin 3 → K,
      W.map (graphCoordinatePermutation K (goodMixedChartPermutation ε)).toLinearMap =
        (Matrix.toLin' (Matrix.diagonal u)).graph := by
  let e := goodAmbientBlockEquiv K
  let U := W.map e.toLinearMap
  have hdimU : finrank K U = 3 := (e.finrank_map_eq W).trans hdim
  have hval (k : Fin 2) (a : (Fin 3 → K) × (Fin 3 → K)) (ha : a ∈ W)
      (b : (Fin 3 → K) × (Fin 3 → K)) (hb : b ∈ W) :
      goodAmbientAlternatingForm K (k.castLE (by decide)) ![a, b] = 0 :=
    alternatingRestriction_pair_zero K W _ (hiso k) a ha b hb
  have h0 : ∀ x ∈ U, ∀ y ∈ U, goodSymplecticForm K x y = 0 := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have he : goodAmbientAlternatingForm K 0 ![a, b] = goodSymplecticForm K (e a) (e b) :=
      (goodAmbientAlternatingForm_pair K 0 a b).trans (goodTriple_zero_block_form K _ _)
    exact he.symm.trans (hval 0 a ha b hb)
  have h1 : ∀ x ∈ U, ∀ y ∈ U,
      goodSymplecticForm K x (goodSpectralOperator K (Fin 2 → K) y) = 0 := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have he : goodAmbientAlternatingForm K 1 ![a, b] =
        goodSymplecticForm K (e a) (goodSpectralOperator K (Fin 2 → K) (e b)) :=
      (goodAmbientAlternatingForm_pair K 1 a b).trans (goodTriple_one_block_form K _ _)
    exact he.symm.trans (hval 1 a ha b hb)
  obtain ⟨ε, u, hu⟩ := goodCommonPair_exists_standard_chart U hdimU h0 h1
  refine ⟨ε, u, ?_⟩
  apply Submodule.map_injective_of_injective (goodSplitBlockCoordinates K).injective
  have he : (graphCoordinatePermutation K (goodMixedChartPermutation ε)).trans
      (goodSplitBlockCoordinates K) = e.trans (goodBlockCoordinateSwap K ε) := by
    apply LinearEquiv.ext
    exact goodMixedChartPermutation_coordinates K ε
  rw [← Submodule.map_comp]
  change W.map ((graphCoordinatePermutation K (goodMixedChartPermutation ε)).trans
    (goodSplitBlockCoordinates K)).toLinearMap = _
  rw [he]
  change W.map ((goodBlockCoordinateSwap K ε).toLinearMap.comp e.toLinearMap) = _
  rw [Submodule.map_comp]
  change U.map (goodBlockCoordinateSwap K ε).toLinearMap = _
  rw [hu, goodBlockMixedGraph_map_swap, goodSplitBlockCoordinates_diagonal_graph]

end
end PfaffianDescent

import PfaffianDescent.GoodTripleScheme

namespace PfaffianDescent
open Module
section
variable (R : Type*) [CommRing R]

noncomputable def goodAmbientBlockEquiv :
    ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] (Fin 3 → Fin 2 → R) :=
  (incidenceAmbientBasis R).equivFun.trans (goodBlockCoordinates R)

lemma goodAmbientBlockEquiv_chart : goodAmbientBlockEquiv R =
    (graphCoordinatePermutation R goodChartPermutation).trans (goodSplitBlockCoordinates R) := by
  apply LinearEquiv.ext
  intro x
  exact (goodChartPermutation_coordinates R x).symm

/-- A graph has the same module structure as its source. -/
def graphSourceEquiv (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) : f.graph ≃ₗ[R] (Fin 3 → R) where
  toFun x := x.1.1
  invFun x := ⟨(x, f x), rfl⟩
  left_inv x := Subtype.ext (Prod.ext rfl x.2.symm)
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

lemma alternatingRestriction_pair_zero
    (W : Submodule R ((Fin 3 → R) × (Fin 3 → R)))
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (h : alternatingRestriction R _ W B = 0)
    (x : (Fin 3 → R) × (Fin 3 → R)) (hx : x ∈ W)
    (y : (Fin 3 → R) × (Fin 3 → R)) (hy : y ∈ W) : B ![x, y] = 0 := by
  have hh := DFunLike.congr_fun h ![⟨x, hx⟩, ⟨y, hy⟩]
  change (B.compLinearMap W.subtype) _ = 0 at hh
  rw [alternating_comp_pair] at hh
  exact hh

end
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Every actual common-isotropic ambient three-space lies in the chosen global chart. -/
theorem goodAmbientIsotropic_exists_graph
    (W : Submodule K ((Fin 3 → K) × (Fin 3 → K))) (hdim : finrank K W = 3)
    (hiso : ∀ k, alternatingRestriction K _ W (goodAmbientAlternatingForm K k) = 0) :
    ∃ u : Fin 3 → K,
      W.map (graphCoordinatePermutation K goodChartPermutation).toLinearMap =
        (Matrix.toLin' (Matrix.diagonal u)).graph ∧ GoodFiberEquations (u 0) (u 1) (u 2) := by
  let e := goodAmbientBlockEquiv K
  let U := W.map e.toLinearMap
  have hdimU : finrank K U = 3 := (e.finrank_map_eq W).trans hdim
  have hval (k : Fin 3) (a : (Fin 3 → K) × (Fin 3 → K)) (ha : a ∈ W)
      (b : (Fin 3 → K) × (Fin 3 → K)) (hb : b ∈ W) :
      goodAmbientAlternatingForm K k ![a, b] = 0 :=
    alternatingRestriction_pair_zero K W _ (hiso k) a ha b hb
  have h0 : ∀ x ∈ U, ∀ y ∈ U, goodSymplecticForm K x y = 0 := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have hv := hval 0 a ha b hb
    rw [goodAmbientAlternatingForm_pair, goodTriple_zero_block_form] at hv
    exact hv
  have h1 : ∀ x ∈ U, ∀ y ∈ U,
      goodSymplecticForm K x (goodSpectralOperator K (Fin 2 → K) y) = 0 := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have hv := hval 1 a ha b hb
    rw [goodAmbientAlternatingForm_pair, goodTriple_one_block_form] at hv
    exact hv
  have h2 : ∀ x ∈ U, ∀ y ∈ U, goodThirdBlockForm K x y = 0 := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have hv := hval 2 a ha b hb
    rw [goodAmbientAlternatingForm_pair, goodTriple_two_block_form] at hv
    exact hv
  obtain ⟨u, hu, heq⟩ := goodCommonIsotropic_exists_affine_graph U hdimU h0 h1 h2
  refine ⟨u, ?_, heq⟩
  apply Submodule.map_injective_of_injective (goodSplitBlockCoordinates K).injective
  have hm : (W.map (graphCoordinatePermutation K goodChartPermutation).toLinearMap).map
      (goodSplitBlockCoordinates K).toLinearMap = U := by
    rw [← Submodule.map_comp]
    change W.map ((graphCoordinatePermutation K goodChartPermutation).trans
      (goodSplitBlockCoordinates K)).toLinearMap = W.map (goodAmbientBlockEquiv K).toLinearMap
    rw [goodAmbientBlockEquiv_chart]
  exact hm.trans (hu.trans (goodSplitBlockCoordinates_diagonal_graph K u).symm)

end
end PfaffianDescent

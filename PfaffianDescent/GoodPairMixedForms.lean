import PfaffianDescent.GoodPairMixedCoordinates
import PfaffianDescent.GoodPairTripleScheme
import PfaffianDescent.GoodChartForms

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

def goodBlockSwapSign (ε : Fin 3 → Bool) (i : Fin 3) : R := if ε i then -1 else 1

lemma goodBlockSwapSign_isUnit (ε : Fin 3 → Bool) (i : Fin 3) :
    IsUnit (goodBlockSwapSign R ε i) := by
  cases h : ε i <;> simp [goodBlockSwapSign, h]

lemma goodSpectralOperator_apply_eigen (x : Fin 3 → Fin 2 → R) (i : Fin 3) :
    goodSpectralOperator R (Fin 2 → R) x i = goodBlockEigenvalue R i • x i := by
  fin_cases i <;> simp [goodSpectralOperator, goodBlockEigenvalue]

lemma goodBlockCoordinateSwap_spectral (ε : Fin 3 → Bool) (x : Fin 3 → Fin 2 → R) :
    goodSpectralOperator R (Fin 2 → R) (goodBlockCoordinateSwap R ε x) =
      goodBlockCoordinateSwap R ε (goodSpectralOperator R (Fin 2 → R) x) := by
  funext i j
  rw [goodSpectralOperator_apply_eigen]
  cases h : ε i <;> fin_cases j <;>
    simp [goodBlockCoordinateSwap, h, goodSpectralOperator_apply_eigen]

lemma goodSymplecticForm_swapped (ε : Fin 3 → Bool) (x y : Fin 3 → Fin 2 → R) :
    goodSymplecticForm R (goodBlockCoordinateSwap R ε x) (goodBlockCoordinateSwap R ε y) =
      ∑ i : Fin 3, goodBlockSwapSign R ε i * (x i 0 * y i 1 - x i 1 * y i 0) := by
  rw [goodSymplecticForm_apply]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : ε i <;> simp [goodBlockCoordinateSwap, goodBlockSwapSign, h] <;> ring

lemma goodWeightedGraphEntry (s : Fin 3 → R) (T : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (∑ l : Fin 3, s l *
      ((goodMatrixGraphVector R T (Pi.single i 1)) l 0 *
          (goodMatrixGraphVector R T (Pi.single j 1)) l 1 -
        (goodMatrixGraphVector R T (Pi.single i 1)) l 1 *
          (goodMatrixGraphVector R T (Pi.single j 1)) l 0)) =
      s i * T i j - s j * T j i := by
  rw [goodMatrixGraphVector_basis, goodMatrixGraphVector_basis]
  simp [mul_sub, Finset.sum_sub_distrib, mul_ite, ite_mul]

noncomputable def goodMixedPairChartAlternatingForm (ε : Fin 3 → Bool) (k : Fin 3) :
    AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) :=
  alternatingTransport (graphCoordinatePermutation R (goodMixedChartPermutation ε))
    (goodPairAmbientAlternatingForm R k)

lemma goodMixedPairChartAlternatingForm_pair (ε : Fin 3 → Bool) (k : Fin 3)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodMixedPairChartAlternatingForm R ε k ![x, y] =
      goodPairAmbientAlternatingForm R k
        ![(graphCoordinatePermutation R (goodMixedChartPermutation ε)).symm x,
          (graphCoordinatePermutation R (goodMixedChartPermutation ε)).symm y] := by
  exact alternating_comp_pair _ _ _ _

lemma goodMixedPairChartAlternatingForm_zero (ε : Fin 3 → Bool)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodMixedPairChartAlternatingForm R ε 0 ![x, y] =
      goodSymplecticForm R
        (goodBlockCoordinateSwap R ε (goodSplitBlockCoordinates R x))
        (goodBlockCoordinateSwap R ε (goodSplitBlockCoordinates R y)) := by
  rw [goodMixedPairChartAlternatingForm_pair]
  change goodAmbientAlternatingForm R 0 _ = _
  rw [goodAmbientAlternatingForm_pair, goodTriple_zero_block_form]
  change goodSymplecticForm R
    (goodAmbientBlockEquiv R ((graphCoordinatePermutation R (goodMixedChartPermutation ε)).symm x))
    (goodAmbientBlockEquiv R ((graphCoordinatePermutation R (goodMixedChartPermutation ε)).symm y)) = _
  rw [goodMixedChart_inverse_coordinates, goodMixedChart_inverse_coordinates]

lemma goodMixedPairChartAlternatingForm_one (ε : Fin 3 → Bool)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodMixedPairChartAlternatingForm R ε 1 ![x, y] =
      goodSymplecticForm R
        (goodBlockCoordinateSwap R ε (goodSplitBlockCoordinates R x))
        (goodBlockCoordinateSwap R ε
          (goodSpectralOperator R (Fin 2 → R) (goodSplitBlockCoordinates R y))) := by
  rw [goodMixedPairChartAlternatingForm_pair]
  change goodAmbientAlternatingForm R 1 _ = _
  rw [goodAmbientAlternatingForm_pair, goodTriple_one_block_form]
  change goodSymplecticForm R
    (goodAmbientBlockEquiv R ((graphCoordinatePermutation R (goodMixedChartPermutation ε)).symm x))
    (goodSpectralOperator R (Fin 2 → R)
      (goodAmbientBlockEquiv R ((graphCoordinatePermutation R (goodMixedChartPermutation ε)).symm y))) = _
  rw [goodMixedChart_inverse_coordinates, goodMixedChart_inverse_coordinates,
    goodBlockCoordinateSwap_spectral]

lemma goodMixedPairChartAlternatingForm_two (ε : Fin 3 → Bool) :
    goodMixedPairChartAlternatingForm R ε 2 = 0 := by
  simp [goodMixedPairChartAlternatingForm, goodPairAmbientAlternatingForm]

lemma goodMixedPairChartAlternatingForm_zero_graph_entry (ε : Fin 3 → Bool)
    (T : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    goodMixedPairChartAlternatingForm R ε 0
      ![(Pi.single i 1, Matrix.toLin' T (Pi.single i 1)),
        (Pi.single j 1, Matrix.toLin' T (Pi.single j 1))] =
      goodBlockSwapSign R ε i * T i j - goodBlockSwapSign R ε j * T j i := by
  rw [goodMixedPairChartAlternatingForm_zero, goodSplitBlockCoordinates_graph_vector,
    goodSplitBlockCoordinates_graph_vector, goodSymplecticForm_swapped, goodWeightedGraphEntry]

lemma goodMixedPairChartAlternatingForm_one_graph_entry (ε : Fin 3 → Bool)
    (T : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    goodMixedPairChartAlternatingForm R ε 1
      ![(Pi.single i 1, Matrix.toLin' T (Pi.single i 1)),
        (Pi.single j 1, Matrix.toLin' T (Pi.single j 1))] =
      goodBlockEigenvalue R i * (goodBlockSwapSign R ε i * T i j) -
        goodBlockEigenvalue R j * (goodBlockSwapSign R ε j * T j i) := by
  rw [goodMixedPairChartAlternatingForm_one, goodSplitBlockCoordinates_graph_vector,
    goodSplitBlockCoordinates_graph_vector, goodSymplecticForm_swapped]
  have he : (∑ l : Fin 3, goodBlockSwapSign R ε l *
      ((goodMatrixGraphVector R T (Pi.single i 1)) l 0 *
          (goodSpectralOperator R (Fin 2 → R) (goodMatrixGraphVector R T (Pi.single j 1))) l 1 -
        (goodMatrixGraphVector R T (Pi.single i 1)) l 1 *
          (goodSpectralOperator R (Fin 2 → R) (goodMatrixGraphVector R T (Pi.single j 1))) l 0)) =
      ∑ l : Fin 3, (goodBlockEigenvalue R l * goodBlockSwapSign R ε l) *
        ((goodMatrixGraphVector R T (Pi.single i 1)) l 0 *
            (goodMatrixGraphVector R T (Pi.single j 1)) l 1 -
          (goodMatrixGraphVector R T (Pi.single i 1)) l 1 *
            (goodMatrixGraphVector R T (Pi.single j 1)) l 0) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [goodSpectralOperator_apply_eigen]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, goodWeightedGraphEntry]
  ring

/-- Over any ring with two invertible, every one of the eight chart equations forces
all off-diagonal graph coordinates to vanish. -/
theorem goodMixedPairChart_diagonal (h2 : IsUnit (2 : R)) (ε : Fin 3 → Bool)
    (T : Matrix (Fin 3) (Fin 3) R)
    (hT : ∀ k : Fin 3, alternatingRestriction R _ (Matrix.toLin' T).graph
      (goodMixedPairChartAlternatingForm R ε k) = 0) :
    T = Matrix.diagonal (fun i => T i i) := by
  let U : Matrix (Fin 3) (Fin 3) R := fun i j => goodBlockSwapSign R ε i * T i j
  have h0 (i j : Fin 3) : U i j - U j i = 0 := by
    have h := (alternatingRestriction_graph_eq_zero_iff _ _).mp (hT 0) i j
    exact (goodMixedPairChartAlternatingForm_zero_graph_entry R ε T i j).symm.trans h
  have h1 (i j : Fin 3) : goodBlockEigenvalue R i * U i j - goodBlockEigenvalue R j * U j i = 0 := by
    have h := (alternatingRestriction_graph_eq_zero_iff _ _).mp (hT 1) i j
    exact (goodMixedPairChartAlternatingForm_one_graph_entry R ε T i j).symm.trans h
  have hU := goodMatrixGraph_diagonal_of_entries R h2 U h0 h1
  funext i j
  by_cases hij : i = j
  · subst j
    simp
  · have hz : U i j = 0 := by
      have he := congrFun (congrFun hU i) j
      simpa [Matrix.diagonal, hij] using he
    have ht : T i j = 0 := (goodBlockSwapSign_isUnit R ε i).mul_right_eq_zero.mp hz
    simp [Matrix.diagonal, hij, ht]

end
end PfaffianDescent

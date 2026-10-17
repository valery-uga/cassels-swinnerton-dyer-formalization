import PfaffianDescent.GoodMatrixGraph

namespace PfaffianDescent
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodThirdBlockForm_map (φ : R →+* S) (x y : Fin 3 → Fin 2 → R) :
    goodThirdBlockForm S (fun i => φ ∘ x i) (fun i => φ ∘ y i) =
      φ (goodThirdBlockForm R x y) := by
  simp [goodThirdBlockForm, Matrix.toBilin'_apply, goodTriple, Fin.sum_univ_six,
    goodBlockCoordinates, map_add, map_mul, map_neg, map_ofNat]

lemma goodMatrixGraphVector_map (φ : R →+* S) (T : Matrix (Fin 3) (Fin 3) R)
    (x : Fin 3 → R) :
    goodMatrixGraphVector S (T.map φ) (φ ∘ x) =
      fun i => φ ∘ goodMatrixGraphVector R T x i := by
  funext i j
  fin_cases j <;>
    simp [goodMatrixGraphVector, Matrix.mulVec, dotProduct, map_sum, map_mul, Function.comp_def]

lemma goodBlockEigenvalue_map (φ : R →+* S) (i : Fin 3) :
    φ (goodBlockEigenvalue R i) = goodBlockEigenvalue S i := by
  fin_cases i <;> simp [goodBlockEigenvalue, map_ofNat]

end
section
variable (R : Type*) [CommRing R]

/-- A matrix entry of the restriction of the third form to a graph. -/
def goodGraphThirdEntry (T : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) : R :=
  goodThirdBlockForm R (goodMatrixGraphVector R T (Pi.single i 1))
    (goodMatrixGraphVector R T (Pi.single j 1))

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodGraphThirdEntry_map (φ : R →+* S) (T : Matrix (Fin 3) (Fin 3) R)
    (i j : Fin 3) : goodGraphThirdEntry S (T.map φ) i j = φ (goodGraphThirdEntry R T i j) := by
  have hs (i : Fin 3) : φ ∘ (Pi.single i (1 : R) : Fin 3 → R) = Pi.single i (1 : S) := by
    funext j
    by_cases h : i = j <;> simp [Pi.single_apply, Function.comp_def, h, eq_comm]
  unfold goodGraphThirdEntry
  rw [← hs i, ← hs j, goodMatrixGraphVector_map, goodMatrixGraphVector_map]
  exact goodThirdBlockForm_map φ _ _

end
section
variable (R : Type*) [CommRing R]

lemma goodGraphThirdEntry_diagonal01 (u : Fin 3 → R) :
    goodGraphThirdEntry R (Matrix.diagonal u) 0 1 = 1 + u 0 * u 1 := by
  unfold goodGraphThirdEntry
  rw [goodMatrixGraphVector_diagonal, goodMatrixGraphVector_diagonal]
  simpa using goodThirdBlockForm_line_evaluation R (fun _ => 1) u
    (Pi.single 0 1) (Pi.single 1 1)

lemma goodGraphThirdEntry_diagonal02 (u : Fin 3 → R) :
    goodGraphThirdEntry R (Matrix.diagonal u) 0 2 = 1 + u 0 * u 2 := by
  unfold goodGraphThirdEntry
  rw [goodMatrixGraphVector_diagonal, goodMatrixGraphVector_diagonal]
  simpa using goodThirdBlockForm_line_evaluation R (fun _ => 1) u
    (Pi.single 0 1) (Pi.single 2 1)

lemma goodGraphThirdEntry_diagonal12 (u : Fin 3 → R) :
    goodGraphThirdEntry R (Matrix.diagonal u) 1 2 = 1 + 2 * u 1 * u 2 := by
  unfold goodGraphThirdEntry
  rw [goodMatrixGraphVector_diagonal, goodMatrixGraphVector_diagonal]
  simpa using goodThirdBlockForm_line_evaluation R (fun _ => 1) u
    (Pi.single 1 1) (Pi.single 2 1)

end
end PfaffianDescent

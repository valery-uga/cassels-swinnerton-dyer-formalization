import PfaffianDescent.GoodMatrixGraph
import PfaffianDescent.IncidenceAmbientCoordinates

namespace PfaffianDescent

/-- The permutation listing the three even coordinates followed by the three odd coordinates. -/
def goodEvenOddPermutation : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 1, 3, 5]
  invFun := ![0, 3, 1, 4, 2, 5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The standard Grassmannian chart used by the displayed good fiber. -/
def goodChartPermutation : Equiv.Perm (Fin 3 ⊕ Fin 3) :=
  (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).trans
    (goodEvenOddPermutation.trans (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm)

section
variable (R : Type*) [CommRing R]

/-- Group a first-coordinate vector and a second-coordinate vector into three blocks. -/
def goodSplitBlockCoordinates : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] (Fin 3 → Fin 2 → R) where
  toFun x := fun i => ![x.1 i, x.2 i]
  invFun x := (fun i => x i 0, fun i => x i 1)
  left_inv x := rfl
  right_inv x := by funext i j; fin_cases j <;> rfl
  map_add' x y := by funext i j; fin_cases j <;> rfl
  map_smul' c x := by funext i j; fin_cases j <;> rfl

lemma incidenceAmbientBasis_coordinates (x : (Fin 3 → R) × (Fin 3 → R)) :
    (incidenceAmbientBasis R).equivFun x = ![x.1 0, x.1 1, x.1 2, x.2 0, x.2 1, x.2 2] := by
  funext i
  simp only [incidenceAmbientBasis, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply]
  fin_cases i
  · change ((Pi.basisFun R (Fin 3)).prod (Pi.basisFun R (Fin 3))).repr x
      (Sum.inl (0 : Fin 3)) = x.1 0
    simp
  · change ((Pi.basisFun R (Fin 3)).prod (Pi.basisFun R (Fin 3))).repr x
      (Sum.inl (1 : Fin 3)) = x.1 1
    simp
  · change ((Pi.basisFun R (Fin 3)).prod (Pi.basisFun R (Fin 3))).repr x
      (Sum.inl (2 : Fin 3)) = x.1 2
    simp
  · change ((Pi.basisFun R (Fin 3)).prod (Pi.basisFun R (Fin 3))).repr x
      (Sum.inr (0 : Fin 3)) = x.2 0
    simp
  · change ((Pi.basisFun R (Fin 3)).prod (Pi.basisFun R (Fin 3))).repr x
      (Sum.inr (1 : Fin 3)) = x.2 1
    simp
  · change ((Pi.basisFun R (Fin 3)).prod (Pi.basisFun R (Fin 3))).repr x
      (Sum.inr (2 : Fin 3)) = x.2 2
    simp

/-- The good fiber's block coordinates are precisely the chosen chart of the global atlas. -/
lemma goodChartPermutation_coordinates (x : (Fin 3 → R) × (Fin 3 → R)) :
    goodSplitBlockCoordinates R (graphCoordinatePermutation R goodChartPermutation x) =
      goodBlockCoordinates R ((incidenceAmbientBasis R).equivFun x) := by
  rw [incidenceAmbientBasis_coordinates]
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma goodSplitBlockCoordinates_graph_vector (T : Matrix (Fin 3) (Fin 3) R) (x : Fin 3 → R) :
    goodSplitBlockCoordinates R (x, Matrix.toLin' T x) = goodMatrixGraphVector R T x := rfl

lemma goodSplitBlockCoordinates_diagonal_graph (u : Fin 3 → R) :
    ((Matrix.toLin' (Matrix.diagonal u)).graph).map (goodSplitBlockCoordinates R).toLinearMap =
      goodBlockGraph R u := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hb, rfl⟩ i
    change b = (Matrix.diagonal u).mulVec a at hb
    simp [goodSplitBlockCoordinates, hb, Matrix.mulVec_diagonal]
  · intro hx
    refine ⟨(fun i => x i 0, fun i => x i 1), ?_, ?_⟩
    · change (fun i => x i 1) = (Matrix.diagonal u).mulVec (fun i => x i 0)
      funext i
      simpa [Matrix.mulVec_diagonal] using hx i
    · exact (goodSplitBlockCoordinates R).apply_symm_apply x

end
end PfaffianDescent

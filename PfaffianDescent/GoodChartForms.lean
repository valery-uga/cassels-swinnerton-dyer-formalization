import PfaffianDescent.GoodTripleScheme
import PfaffianDescent.GoodGraphFiberAlgebra
import PfaffianDescent.AlternatingGraphRestriction

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

/-- The displayed ambient triple transported into the chosen graph chart. -/
noncomputable def goodChartAlternatingForm (k : Fin 3) :
    AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) :=
  alternatingTransport (graphCoordinatePermutation R goodChartPermutation) (goodAmbientAlternatingForm R k)

lemma goodChartAlternatingForm_pair (k : Fin 3) (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodChartAlternatingForm R k ![x, y] =
      goodAmbientAlternatingForm R k
        ![(graphCoordinatePermutation R goodChartPermutation).symm x,
          (graphCoordinatePermutation R goodChartPermutation).symm y] := by
  change ((goodAmbientAlternatingForm R k).compLinearMap
    (graphCoordinatePermutation R goodChartPermutation).symm.toLinearMap) ![x, y] = _
  exact alternating_comp_pair _ _ _ _

lemma goodChart_inverse_coordinates (x : (Fin 3 → R) × (Fin 3 → R)) :
    goodBlockCoordinates R ((incidenceAmbientBasis R).equivFun
      ((graphCoordinatePermutation R goodChartPermutation).symm x)) =
      goodSplitBlockCoordinates R x := by
  have h := goodChartPermutation_coordinates R
    ((graphCoordinatePermutation R goodChartPermutation).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

lemma goodChartAlternatingForm_zero_pair (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodChartAlternatingForm R 0 ![x, y] =
      goodSymplecticForm R (goodSplitBlockCoordinates R x) (goodSplitBlockCoordinates R y) := by
  rw [goodChartAlternatingForm_pair, goodAmbientAlternatingForm_pair,
    goodTriple_zero_block_form, goodChart_inverse_coordinates, goodChart_inverse_coordinates]

lemma goodChartAlternatingForm_one_pair (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodChartAlternatingForm R 1 ![x, y] =
      goodSymplecticForm R (goodSplitBlockCoordinates R x)
        (goodSpectralOperator R (Fin 2 → R) (goodSplitBlockCoordinates R y)) := by
  rw [goodChartAlternatingForm_pair, goodAmbientAlternatingForm_pair,
    goodTriple_one_block_form, goodChart_inverse_coordinates, goodChart_inverse_coordinates]

lemma goodChartAlternatingForm_two_pair (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodChartAlternatingForm R 2 ![x, y] =
      goodThirdBlockForm R (goodSplitBlockCoordinates R x) (goodSplitBlockCoordinates R y) := by
  rw [goodChartAlternatingForm_pair, goodAmbientAlternatingForm_pair,
    goodTriple_two_block_form, goodChart_inverse_coordinates, goodChart_inverse_coordinates]

lemma goodChartAlternatingForm_original (k : Fin 3) :
    alternatingTransport (graphCoordinatePermutation R goodChartPermutation.symm)
      (goodChartAlternatingForm R k) = goodAmbientAlternatingForm R k := by
  unfold goodChartAlternatingForm
  rw [← graphCoordinatePermutation_symm]
  exact (alternatingTransport (graphCoordinatePermutation R goodChartPermutation)).symm_apply_apply _

/-- The polynomial restrictions are the entries of the actual alternating forms. -/
lemma goodChartAlternatingForm_graph_entry (T : Matrix (Fin 3) (Fin 3) R)
    (k i j : Fin 3) :
    goodChartAlternatingForm R k
      ![(Pi.single i 1, Matrix.toLin' T (Pi.single i 1)),
        (Pi.single j 1, Matrix.toLin' T (Pi.single j 1))] =
      goodGraphRelation R T (k, i, j) := by
  fin_cases k
  · change goodChartAlternatingForm R 0
      ![(Pi.single i 1, Matrix.toLin' T (Pi.single i 1)),
        (Pi.single j 1, Matrix.toLin' T (Pi.single j 1))] = goodGraphRelation R T (0, i, j)
    rw [goodChartAlternatingForm_zero_pair R, goodSplitBlockCoordinates_graph_vector,
      goodSplitBlockCoordinates_graph_vector, goodSymplecticForm_graph_basis]
    rfl
  · change goodChartAlternatingForm R 1
      ![(Pi.single i 1, Matrix.toLin' T (Pi.single i 1)),
        (Pi.single j 1, Matrix.toLin' T (Pi.single j 1))] = goodGraphRelation R T (1, i, j)
    rw [goodChartAlternatingForm_one_pair R, goodSplitBlockCoordinates_graph_vector,
      goodSplitBlockCoordinates_graph_vector, goodSpectralForm_graph_basis]
    rfl
  · change goodChartAlternatingForm R 2
      ![(Pi.single i 1, Matrix.toLin' T (Pi.single i 1)),
        (Pi.single j 1, Matrix.toLin' T (Pi.single j 1))] = goodGraphRelation R T (2, i, j)
    rw [goodChartAlternatingForm_two_pair R, goodSplitBlockCoordinates_graph_vector,
      goodSplitBlockCoordinates_graph_vector]
    rfl

/-- The full quotient equations express exactly membership in the incidence restriction kernels. -/
theorem goodChartAlternatingForm_restriction_iff (T : Matrix (Fin 3) (Fin 3) R) :
    (∀ k : Fin 3, alternatingRestriction R _ (Matrix.toLin' T).graph (goodChartAlternatingForm R k) = 0) ↔
      ∀ k, goodGraphRelation R T k = 0 := by
  constructor
  · intro h k
    rw [← goodChartAlternatingForm_graph_entry]
    exact (alternatingRestriction_graph_eq_zero_iff _ _).mp (h k.1) k.2.1 k.2.2
  · intro h k
    apply (alternatingRestriction_graph_eq_zero_iff _ _).mpr
    intro i j
    rw [goodChartAlternatingForm_graph_entry]
    exact h (k, i, j)

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodChartAlternatingForm_map (φ : R →+* S) (k : Fin 3)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodChartAlternatingForm S k ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
      φ (goodChartAlternatingForm R k ![x, y]) :=
  alternatingTransport_permutation_map φ goodChartPermutation _ _
    (goodAmbientAlternatingForm_map φ k) x y

end
section
variable (K : Type*) [CommRing K]

/-- The universal point of the full graph-fiber quotient is an actual common-isotropic graph. -/
noncomputable def goodGraphFiberIncidencePoint : IncidenceGraphPoints (GoodGraphFiberAlgebra K) :=
  ⟨Matrix.toLin' (goodGraphFiberX K), fun k =>
    ⟨goodChartAlternatingForm (GoodGraphFiberAlgebra K) k,
      (goodChartAlternatingForm_restriction_iff _ _).mpr (goodGraphFiberX_relation K) k⟩⟩

lemma goodGraphFiberIncidencePoint_original (k : Fin 3) :
    incidenceOriginalForm goodChartPermutation (goodGraphFiberIncidencePoint K) k =
      goodAmbientAlternatingForm (GoodGraphFiberAlgebra K) k := by
  exact goodChartAlternatingForm_original (GoodGraphFiberAlgebra K) k

lemma goodGraphFiberIncidencePoint_coefficients (k : AlternatingTripleIndex) :
    incidenceOriginalCoefficients goodChartPermutation (goodGraphFiberIncidencePoint K) k =
      goodTripleSchemeCoefficients (GoodGraphFiberAlgebra K) k := by
  unfold incidenceOriginalCoefficients goodTripleSchemeCoefficients
  rw [goodGraphFiberIncidencePoint_original]

end
end PfaffianDescent

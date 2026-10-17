import PfaffianDescent.GoodPairTripleScheme
import PfaffianDescent.GoodPairGraphAlgebra
import PfaffianDescent.GoodChartForms

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

noncomputable def goodPairChartAlternatingForm (k : Fin 3) :
    AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) :=
  if k = 2 then 0 else goodChartAlternatingForm R k

lemma goodPairChartAlternatingForm_original (k : Fin 3) :
    alternatingTransport (graphCoordinatePermutation R goodChartPermutation.symm)
      (goodPairChartAlternatingForm R k) = goodPairAmbientAlternatingForm R k := by
  by_cases h : k = 2
  · simp [goodPairChartAlternatingForm, goodPairAmbientAlternatingForm, h]
  · simpa only [goodPairChartAlternatingForm, goodPairAmbientAlternatingForm, if_neg h] using
      goodChartAlternatingForm_original R k

lemma goodPairChartAlternatingForm_graph_entry (T : Matrix (Fin 3) (Fin 3) R)
    (k i j : Fin 3) :
    goodPairChartAlternatingForm R k
      ![(Pi.single i 1, Matrix.toLin' T (Pi.single i 1)),
        (Pi.single j 1, Matrix.toLin' T (Pi.single j 1))] =
      if k = 2 then 0 else goodGraphRelation R T (k, i, j) := by
  by_cases h : k = 2
  · simp [goodPairChartAlternatingForm, h]
  · simpa only [goodPairChartAlternatingForm, if_neg h] using
      goodChartAlternatingForm_graph_entry R T k i j

/-- On arbitrary rings, the actual first two restrictions are exactly the eighteen equations. -/
theorem goodPairChartAlternatingForm_restriction_iff (T : Matrix (Fin 3) (Fin 3) R) :
    (∀ k : Fin 3, alternatingRestriction R _ (Matrix.toLin' T).graph (goodPairChartAlternatingForm R k) = 0) ↔
      ∀ k, goodPairGraphRelation R T k = 0 := by
  constructor
  · intro h
    rintro ⟨b, i, j⟩
    fin_cases b
    · have hz := (alternatingRestriction_graph_eq_zero_iff _ _).mp (h 0) i j
      rw [goodPairChartAlternatingForm_graph_entry] at hz
      simpa [goodPairGraphRelation, goodGraphRelation] using hz
    · have hz := (alternatingRestriction_graph_eq_zero_iff _ _).mp (h 1) i j
      rw [goodPairChartAlternatingForm_graph_entry] at hz
      simpa [goodPairGraphRelation, goodGraphRelation] using hz
  · intro h k
    apply (alternatingRestriction_graph_eq_zero_iff _ _).mpr
    intro i j
    rw [goodPairChartAlternatingForm_graph_entry]
    fin_cases k
    · simpa [goodPairGraphRelation, goodGraphRelation] using h (0, i, j)
    · simpa [goodPairGraphRelation, goodGraphRelation] using h (1, i, j)
    · simp

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodPairChartAlternatingForm_map (φ : R →+* S) (k : Fin 3)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    goodPairChartAlternatingForm S k ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
      φ (goodPairChartAlternatingForm R k ![x, y]) := by
  by_cases h : k = 2
  · simp [goodPairChartAlternatingForm, h]
  · simpa only [goodPairChartAlternatingForm, if_neg h] using goodChartAlternatingForm_map φ k x y

end
section
variable (K : Type*) [CommRing K]

noncomputable def goodPairGraphIncidencePoint : IncidenceGraphPoints (GoodPairGraphAlgebra K) :=
  ⟨Matrix.toLin' (goodPairGraphX K), fun k =>
    ⟨goodPairChartAlternatingForm (GoodPairGraphAlgebra K) k,
      (goodPairChartAlternatingForm_restriction_iff _ _).mpr (goodPairGraphX_relation K) k⟩⟩

lemma goodPairGraphIncidencePoint_original (k : Fin 3) :
    incidenceOriginalForm goodChartPermutation (goodPairGraphIncidencePoint K) k =
      goodPairAmbientAlternatingForm (GoodPairGraphAlgebra K) k :=
  goodPairChartAlternatingForm_original (GoodPairGraphAlgebra K) k

lemma goodPairGraphIncidencePoint_coefficients (k : AlternatingTripleIndex) :
    incidenceOriginalCoefficients goodChartPermutation (goodPairGraphIncidencePoint K) k =
      goodPairTripleSchemeCoefficients (GoodPairGraphAlgebra K) k := by
  unfold incidenceOriginalCoefficients goodPairTripleSchemeCoefficients
  rw [goodPairGraphIncidencePoint_original]

end
end PfaffianDescent

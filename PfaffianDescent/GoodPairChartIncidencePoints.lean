import PfaffianDescent.GoodPairChartForms
import PfaffianDescent.GoodChartIncidencePoints

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

/-- Equality of the original triple coefficients identifies the three actual chart forms. -/
lemma goodPairChartIncidence_forms (p : IncidenceGraphPoints R)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodPairTripleSchemeCoefficients R)
    (k : Fin 3) : (p.2 k).1 = goodPairChartAlternatingForm R k := by
  have hb : incidenceOriginalForm goodChartPermutation p k = goodPairAmbientAlternatingForm R k := by
    apply (alternatingCoordinates (incidenceAmbientBasis R)).injective
    funext s
    exact congrFun hc (k, s)
  apply (alternatingTransport (graphCoordinatePermutation R goodChartPermutation.symm)).injective
  exact hb.trans (goodPairChartAlternatingForm_original R k).symm

lemma goodPairChartIncidence_relations (p : IncidenceGraphPoints R)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodPairTripleSchemeCoefficients R) :
    ∀ k, goodPairGraphRelation R (LinearMap.toMatrix' p.1) k = 0 := by
  apply (goodPairChartAlternatingForm_restriction_iff R _).mp
  intro k
  rw [Matrix.toLin'_toMatrix', ← goodPairChartIncidence_forms p hc k]
  exact (p.2 k).2

end
section
variable (K : Type*) [CommRing K] {A : Type*} [CommRing A] [Algebra K A]

/-- The graph matrix of any actual incidence point over the displayed triple factors
through the full graph-fiber coordinate algebra. -/
noncomputable def goodPairChartIncidenceLift (p : IncidenceGraphPoints A)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodPairTripleSchemeCoefficients A) :
    GoodPairGraphAlgebra K →ₐ[K] A :=
  goodPairGraphLift K (LinearMap.toMatrix' p.1) (goodPairChartIncidence_relations p hc)

lemma goodPairChartIncidenceLift_x (p : IncidenceGraphPoints A)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodPairTripleSchemeCoefficients A)
    (i j : Fin 3) : goodPairChartIncidenceLift K p hc (goodPairGraphX K i j) = LinearMap.toMatrix' p.1 i j :=
  goodPairGraphLift_x K _ _ i j

/-- Evaluating the universal quotient point recovers the entire incidence point,
including all three forms, over arbitrary coefficient algebras. -/
theorem goodPairChartIncidenceLift_recovers (p : IncidenceGraphPoints A)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodPairTripleSchemeCoefficients A) :
    incidenceGraphPointMap (goodPairChartIncidenceLift K p hc).toRingHom
      (goodPairGraphIncidencePoint K) = p := by
  let φ : GoodPairGraphAlgebra K →+* A := (goodPairChartIncidenceLift K p hc).toRingHom
  have hT : Matrix.map (goodPairGraphX K) φ = LinearMap.toMatrix' p.1 := by
    funext i j
    exact goodPairChartIncidenceLift_x K p hc i j
  have hfg (a : Fin 3 → GoodPairGraphAlgebra K) :
      p.1 (φ ∘ a) = φ ∘ (goodPairGraphIncidencePoint K).1 a := by
    have h := matrix_toLin_map_apply φ (goodPairGraphX K) a
    rw [hT, Matrix.toLin'_toMatrix'] at h
    exact h
  have hB (k : Fin 3) (x y : (Fin 3 → GoodPairGraphAlgebra K) × (Fin 3 → GoodPairGraphAlgebra K)) :
      (p.2 k).1 ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
        φ (((goodPairGraphIncidencePoint K).2 k).1 ![x, y]) := by
    rw [goodPairChartIncidence_forms p hc k]
    exact goodPairChartAlternatingForm_map φ k x y
  apply (incidenceGraphPointCoordinates A).injective
  rw [incidenceGraphPointMap_coordinates]
  exact (incidenceGraphPointCoordinates_of_compatible φ (goodPairGraphIncidencePoint K) p hfg hB).symm

end
end PfaffianDescent

import PfaffianDescent.GoodChartForms

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

/-- Equality of the original triple coefficients identifies the three actual chart forms. -/
lemma goodChartIncidence_forms (p : IncidenceGraphPoints R)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodTripleSchemeCoefficients R)
    (k : Fin 3) : (p.2 k).1 = goodChartAlternatingForm R k := by
  have hb : incidenceOriginalForm goodChartPermutation p k = goodAmbientAlternatingForm R k := by
    apply (alternatingCoordinates (incidenceAmbientBasis R)).injective
    funext s
    exact congrFun hc (k, s)
  apply (alternatingTransport (graphCoordinatePermutation R goodChartPermutation.symm)).injective
  exact hb.trans (goodChartAlternatingForm_original R k).symm

lemma goodChartIncidence_relations (p : IncidenceGraphPoints R)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodTripleSchemeCoefficients R) :
    ∀ k, goodGraphRelation R (LinearMap.toMatrix' p.1) k = 0 := by
  apply (goodChartAlternatingForm_restriction_iff R _).mp
  intro k
  rw [Matrix.toLin'_toMatrix', ← goodChartIncidence_forms p hc k]
  exact (p.2 k).2

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma matrix_toLin_map_apply (φ : R →+* S) (T : Matrix (Fin 3) (Fin 3) R) (x : Fin 3 → R) :
    Matrix.toLin' (T.map φ) (φ ∘ x) = φ ∘ Matrix.toLin' T x := by
  change (T.map φ).mulVec (φ ∘ x) = φ ∘ T.mulVec x
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end
section
variable (K : Type*) [CommRing K] {A : Type*} [CommRing A] [Algebra K A]

/-- The graph matrix of any actual incidence point over the displayed triple factors
through the full graph-fiber coordinate algebra. -/
noncomputable def goodChartIncidenceLift (p : IncidenceGraphPoints A)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodTripleSchemeCoefficients A) :
    GoodGraphFiberAlgebra K →ₐ[K] A :=
  goodGraphFiberLift K (LinearMap.toMatrix' p.1) (goodChartIncidence_relations p hc)

lemma goodChartIncidenceLift_x (p : IncidenceGraphPoints A)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodTripleSchemeCoefficients A)
    (i j : Fin 3) : goodChartIncidenceLift K p hc (goodGraphFiberX K i j) = LinearMap.toMatrix' p.1 i j :=
  goodGraphFiberLift_x K _ _ i j

/-- Evaluating the universal quotient point recovers the entire incidence point,
including all three forms, over arbitrary coefficient algebras. -/
theorem goodChartIncidenceLift_recovers (p : IncidenceGraphPoints A)
    (hc : incidenceOriginalCoefficients goodChartPermutation p = goodTripleSchemeCoefficients A) :
    incidenceGraphPointMap (goodChartIncidenceLift K p hc).toRingHom
      (goodGraphFiberIncidencePoint K) = p := by
  let φ : GoodGraphFiberAlgebra K →+* A := (goodChartIncidenceLift K p hc).toRingHom
  have hT : Matrix.map (goodGraphFiberX K) φ = LinearMap.toMatrix' p.1 := by
    funext i j
    exact goodChartIncidenceLift_x K p hc i j
  have hfg (a : Fin 3 → GoodGraphFiberAlgebra K) :
      p.1 (φ ∘ a) = φ ∘ (goodGraphFiberIncidencePoint K).1 a := by
    have h := matrix_toLin_map_apply φ (goodGraphFiberX K) a
    rw [hT, Matrix.toLin'_toMatrix'] at h
    exact h
  have hB (k : Fin 3) (x y : (Fin 3 → GoodGraphFiberAlgebra K) × (Fin 3 → GoodGraphFiberAlgebra K)) :
      (p.2 k).1 ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
        φ (((goodGraphFiberIncidencePoint K).2 k).1 ![x, y]) := by
    rw [goodChartIncidence_forms p hc k]
    exact goodChartAlternatingForm_map φ k x y
  apply (incidenceGraphPointCoordinates A).injective
  rw [incidenceGraphPointMap_coordinates]
  exact (incidenceGraphPointCoordinates_of_compatible φ (goodGraphFiberIncidencePoint K) p hfg hB).symm

end
end PfaffianDescent

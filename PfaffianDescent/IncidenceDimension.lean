import PfaffianDescent.SchemeDimensionFromCharts
import PfaffianDescent.IncidenceRelativeDimension

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [Field K]

lemma grassmannianChart_dimension (m n : ℕ) :
    topologicalKrullDim (grassmannianChartScheme K m n) = (n * m : WithBot ℕ∞) := by
  change topologicalKrullDim (Spec (.of (MvPolynomial (Fin n × Fin m) K))) = _
  simpa only [Nat.card_prod, Nat.card_fin, Nat.cast_mul] using
    polynomialSpec_dimension K (Fin n × Fin m)

/-- The actual Grassmannian scheme has dimension `n*m`. -/
theorem grassmannian_dimension (m n : ℕ) :
    topologicalKrullDim (grassmannianScheme K m n) = (n * m : WithBot ℕ∞) := by
  apply scheme_dimension_eq_of_openCover (grassmannianGlueData K m n).openCover
    ⟨Equiv.refl (Fin m ⊕ Fin n)⟩
  intro i
  exact grassmannianChart_dimension K m n

lemma incidenceGraph_dimension : topologicalKrullDim (incidenceGraphScheme K) = 45 := by
  change topologicalKrullDim (Spec (.of (MvPolynomial IncidenceGraphIndex K))) = _
  have hc : Nat.card IncidenceGraphIndex = 45 := by
    rw [Nat.card_eq_fintype_card, incidenceGraphIndex_card]
  rw [polynomialSpec_dimension, hc]
  norm_num

/-- The closed isotropic incidence has dimension forty-five. -/
theorem incidence_dimension : topologicalKrullDim (incidenceScheme K) = 45 := by
  apply scheme_dimension_eq_of_openCover (incidenceGlueData K).openCover
    ⟨Equiv.refl (Fin 3 ⊕ Fin 3)⟩
  intro i
  exact incidenceGraph_dimension K

/-- The parameter scheme of ordered alternating triples has dimension forty-five. -/
theorem alternatingTriple_dimension : topologicalKrullDim (alternatingTripleScheme K) = 45 := by
  change topologicalKrullDim (Spec (.of (MvPolynomial AlternatingTripleIndex K))) = _
  have hc : Nat.card AlternatingTripleIndex = 45 := by
    rw [Nat.card_eq_fintype_card, alternatingTripleIndex_card]
  rw [polynomialSpec_dimension, hc]
  norm_num

end
end PfaffianDescent

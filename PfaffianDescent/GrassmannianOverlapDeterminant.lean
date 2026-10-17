import PfaffianDescent.GrassmannianTransition
import Mathlib.LinearAlgebra.Determinant

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R] {m n : ℕ}

/-- The determinant whose nonvanishing defines a Grassmannian-chart overlap. -/
noncomputable def graphOverlapDeterminant
    (e : ((Fin m → R) × (Fin n → R)) ≃ₗ[R] ((Fin m → R) × (Fin n → R)))
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) : R :=
  LinearMap.det (graphTransitionFirst e f)

lemma graphOverlapDeterminant_isUnit_iff
    (e : ((Fin m → R) × (Fin n → R)) ≃ₗ[R] ((Fin m → R) × (Fin n → R)))
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) :
    IsUnit (graphOverlapDeterminant e f) ↔ Function.Bijective (graphTransitionFirst e f) := by
  rw [graphOverlapDeterminant, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]

/-- The overlap condition is an invertible determinant over any coefficient ring. -/
theorem grassmannian_overlap_determinant_iff
    (e : ((Fin m → R) × (Fin n → R)) ≃ₗ[R] ((Fin m → R) × (Fin n → R)))
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) :
    IsUnit (graphOverlapDeterminant e f) ↔
      Function.Bijective (graphChartQuotientMap (f.graph.map e.toLinearMap)) :=
  (graphOverlapDeterminant_isUnit_iff e f).trans (graphTransition_overlap_iff e f)

end
end PfaffianDescent

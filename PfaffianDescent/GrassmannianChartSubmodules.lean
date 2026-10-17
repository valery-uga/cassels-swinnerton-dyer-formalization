import PfaffianDescent.GrassmannianPointOverlap

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

lemma submodule_map_linearEquiv_symm_map (e : M ≃ₗ[R] N) (W : Submodule R N) :
    (W.map e.symm.toLinearMap).map e.toLinearMap = W := by
  rw [← Submodule.map_comp]
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    ext x
    exact e.apply_symm_apply x
  rw [he, Submodule.map_id]

end
section
variable (R : Type*) [CommRing R] {m n : ℕ}

/-- The actual ambient submodule represented by a matrix in an arbitrary Grassmannian chart. -/
def grassmannianChartSubmodule (i : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    Submodule R ((Fin m → R) × (Fin n → R)) :=
  (Matrix.toLin' T).graph.map (graphCoordinatePermutation R i.symm).toLinearMap

lemma grassmannianChartSubmodule_change (i j : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) :
    (grassmannianChartSubmodule R i T).map (graphCoordinatePermutation R j).toLinearMap =
      (Matrix.toLin' T).graph.map
        (graphCoordinatePermutation R (grassmannianChartChange i j)).toLinearMap := by
  rw [grassmannianChartSubmodule, ← Submodule.map_comp]
  change (Matrix.toLin' T).graph.map ((graphCoordinatePermutation R i.symm).trans
    (graphCoordinatePermutation R j)).toLinearMap = _
  rw [graphCoordinatePermutation_trans]
  rfl

lemma grassmannianChartSubmodule_own_chart (i : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) :
    (grassmannianChartSubmodule R i T).map (graphCoordinatePermutation R i).toLinearMap =
      (Matrix.toLin' T).graph := by
  unfold grassmannianChartSubmodule
  rw [← graphCoordinatePermutation_symm]
  exact submodule_map_linearEquiv_symm_map _ _

lemma grassmannianChartSubmodule_eq_transition (i j : Equiv.Perm (Fin m ⊕ Fin n))
    (T U : Matrix (Fin n) (Fin m) R) (hW : grassmannianChartSubmodule R i T = grassmannianChartSubmodule R j U) :
    ∃ h : Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation R (grassmannianChartChange i j)) (Matrix.toLin' T)),
      graphTransitionMatrix (grassmannianChartChange i j) T h = U := by
  have he : (Matrix.toLin' T).graph.map
      (graphCoordinatePermutation R (grassmannianChartChange i j)).toLinearMap = (Matrix.toLin' U).graph := by
    rw [← grassmannianChartSubmodule_change, hW, grassmannianChartSubmodule_own_chart]
  have h : Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation R (grassmannianChartChange i j)) (Matrix.toLin' T)) := by
    apply (graphTransition_overlap_iff _ _).mpr
    rw [he]
    exact graphChartQuotientMap_graph_bijective _
  refine ⟨h, ?_⟩
  apply Matrix.toLin'.injective
  change Matrix.toLin' (LinearMap.toMatrix' (graphTransition
    (graphCoordinatePermutation R (grassmannianChartChange i j)) (Matrix.toLin' T) h)) = Matrix.toLin' U
  rw [Matrix.toLin'_toMatrix']
  apply linearMap_graph_injective
  exact (graphTransition_map_graph _ _ h).symm.trans he

/-- The graph-transition matrix represents the same ambient submodule in the
two Grassmannian charts.  This is the algebraic form of the chart-overlap
identification used when gluing relative projective coordinate spaces. -/
lemma grassmannianChartSubmodule_eq_transitionMatrix
    (i j : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R)
    (h : Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation R (grassmannianChartChange i j))
      (Matrix.toLin' T))) :
    grassmannianChartSubmodule R i T =
      grassmannianChartSubmodule R j
        (LinearMap.toMatrix' (graphTransition
          (graphCoordinatePermutation R (grassmannianChartChange i j))
          (Matrix.toLin' T) h)) := by
  apply Submodule.map_injective_of_injective
    (graphCoordinatePermutation R j).injective
  rw [grassmannianChartSubmodule_change,
    grassmannianChartSubmodule_own_chart, Matrix.toLin'_toMatrix']
  exact graphTransition_map_graph _ _ h

end
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}

/-- Actual scheme-valued chart points agree exactly when their ambient submodules agree.
The equivalence holds over arbitrary coefficient algebras. -/
theorem grassmannianChartEvaluation_eq_iff_submodule
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) (T U : Matrix (Fin n) (Fin m) A) :
    (grassmannianChartEvaluation K T ≫ grassmannianChartι K i =
      grassmannianChartEvaluation K U ≫ grassmannianChartι K j) ↔
        grassmannianChartSubmodule A i T = grassmannianChartSubmodule A j U := by
  constructor
  · intro he
    obtain ⟨h, hT⟩ := grassmannianChartEvaluation_eq_transition K i j T U he
    apply Submodule.map_injective_of_injective (graphCoordinatePermutation A j).injective
    rw [grassmannianChartSubmodule_change, grassmannianChartSubmodule_own_chart,
      graphTransition_map_graph _ _ h]
    have ht : graphTransition (graphCoordinatePermutation A (grassmannianChartChange i j))
        (Matrix.toLin' T) h = Matrix.toLin' U := by
      have hh := congrArg Matrix.toLin' hT
      change Matrix.toLin' (LinearMap.toMatrix' _) = Matrix.toLin' U at hh
      exact (Matrix.toLin'_toMatrix' _).symm.trans hh
    rw [ht]
  · intro hW
    obtain ⟨h, hT⟩ := grassmannianChartSubmodule_eq_transition A i j T U hW
    exact (grassmannianChartEvaluation_glue K i j T h).trans
      (congrArg (fun V => grassmannianChartEvaluation K V ≫ grassmannianChartι K j) hT)

end
end PfaffianDescent

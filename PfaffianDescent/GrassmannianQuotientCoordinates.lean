import PfaffianDescent.GrassmannianLocalCharts

namespace PfaffianDescent
open Module
section
variable (R : Type*) [CommRing R] {m n : ℕ}

/-- The quotient map on the coordinate block selected by a Grassmannian chart. -/
def grassmannianQuotientCoordinateMap (W : Submodule R ((Fin m → R) × (Fin n → R)))
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (Fin n → R) →ₗ[R] (((Fin m → R) × (Fin n → R)) ⧸ W) :=
  W.mkQ.comp ((graphCoordinatePermutation R σ).symm.toLinearMap.comp
    (LinearMap.inr R (Fin m → R) (Fin n → R)))

lemma grassmannianQuotientCoordinateMap_bijective_iff
    (W : Submodule R ((Fin m → R) × (Fin n → R))) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Function.Bijective (grassmannianQuotientCoordinateMap R W σ) ↔
      Function.Bijective (graphChartQuotientMap (W.map (graphCoordinatePermutation R σ).toLinearMap)) := by
  let e := graphCoordinatePermutation R σ
  let W' := W.map e.toLinearMap
  let E := (Submodule.Quotient.equiv W W' e rfl).symm
  have he (x : Fin n → R) : E (graphChartQuotientMap W' x) = grassmannianQuotientCoordinateMap R W σ x := rfl
  constructor
  · intro h
    constructor
    · intro x y hxy
      apply h.injective
      rw [← he, ← he, hxy]
    · intro y
      obtain ⟨x, hx⟩ := h.surjective (E y)
      exact ⟨x, E.injective ((he x).trans hx)⟩
  · intro h
    constructor
    · intro x y hxy
      apply h.injective
      apply E.injective
      rw [he, he, hxy]
    · intro y
      obtain ⟨z, rfl⟩ := E.surjective y
      obtain ⟨x, hx⟩ := h.surjective z
      exact ⟨x, (he x).symm.trans (congrArg E hx)⟩

/-- The usual nonvanishing-minor chart condition is exactly invertibility of the selected quotient coordinates. -/
theorem grassmannianQuotientCoordinateMap_iff_graph
    (W : Submodule R ((Fin m → R) × (Fin n → R))) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Function.Bijective (grassmannianQuotientCoordinateMap R W σ) ↔
      ∃ T : Matrix (Fin n) (Fin m) R, W = grassmannianChartSubmodule R σ T := by
  rw [grassmannianQuotientCoordinateMap_bijective_iff]
  constructor
  · intro h
    obtain ⟨f, hf, _⟩ := (graphChartQuotientMap_bijective_iff _).mp h
    refine ⟨LinearMap.toMatrix' f, ?_⟩
    apply Submodule.map_injective_of_injective (graphCoordinatePermutation R σ).injective
    rw [grassmannianChartSubmodule_own_chart, Matrix.toLin'_toMatrix']
    exact hf
  · rintro ⟨T, rfl⟩
    rw [grassmannianChartSubmodule_own_chart]
    exact graphChartQuotientMap_graph_bijective _

variable [IsLocalRing R]

lemma grassmannian_local_quotient_coordinates
    (W : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n) :
    ∃ σ : Equiv.Perm (Fin m ⊕ Fin n), Function.Bijective (grassmannianQuotientCoordinateMap R W.toSubmodule σ) := by
  obtain ⟨σ, T, hT⟩ := grassmannian_local_exists_graph R W
  exact ⟨σ, (grassmannianQuotientCoordinateMap_iff_graph R W.toSubmodule σ).mpr ⟨T, hT⟩⟩

end
end PfaffianDescent

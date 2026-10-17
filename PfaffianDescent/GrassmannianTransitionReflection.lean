import PfaffianDescent.GrassmannianTransitionScalar
import PfaffianDescent.GrassmannianTransitionCocycle
import PfaffianDescent.AlternatingTransport

namespace PfaffianDescent
section
variable {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}

lemma matrix_graph_mem_map_iff (φ : R →+* S) (hφ : Function.Injective φ)
    (T : Matrix (Fin n) (Fin m) R) (x : (Fin m → R) × (Fin n → R)) :
    (φ ∘ x.1, φ ∘ x.2) ∈ (Matrix.toLin' (T.map φ)).graph ↔ x ∈ (Matrix.toLin' T).graph := by
  change (φ ∘ x.2) = Matrix.toLin' (T.map φ) (φ ∘ x.1) ↔ x.2 = Matrix.toLin' T x.1
  have hm : Matrix.toLin' (T.map φ) (φ ∘ x.1) = φ ∘ Matrix.toLin' T x.1 := by
    funext i
    exact (RingHom.map_mulVec φ T x.1 i).symm
  rw [hm]
  constructor
  · intro h
    funext i
    exact hφ (congrFun h i)
  · intro h
    exact congrArg (fun x => φ ∘ x) h

lemma graph_permutation_map_le_reflect (φ : R →+* S) (hφ : Function.Injective φ)
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T U : Matrix (Fin n) (Fin m) R)
    (h : (Matrix.toLin' (T.map φ)).graph.map (graphCoordinatePermutation S σ).toLinearMap ≤
      (Matrix.toLin' (U.map φ)).graph) :
    (Matrix.toLin' T).graph.map (graphCoordinatePermutation R σ).toLinearMap ≤ (Matrix.toLin' U).graph := by
  rintro z ⟨x, hx, rfl⟩
  have hxS := (matrix_graph_mem_map_iff φ hφ T x).mpr hx
  have hz : graphCoordinatePermutation S σ (φ ∘ x.1, φ ∘ x.2) ∈ (Matrix.toLin' (U.map φ)).graph :=
    h ⟨(φ ∘ x.1, φ ∘ x.2), hxS, rfl⟩
  rw [graphCoordinatePermutation_map] at hz
  exact (matrix_graph_mem_map_iff φ hφ U (graphCoordinatePermutation R σ x)).mp hz

/-- Equality of the actual permuted graph submodules descends along every injective ring homomorphism. -/
lemma graph_permutation_map_eq_reflect (φ : R →+* S) (hφ : Function.Injective φ)
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T U : Matrix (Fin n) (Fin m) R)
    (h : (Matrix.toLin' (T.map φ)).graph.map (graphCoordinatePermutation S σ).toLinearMap =
      (Matrix.toLin' (U.map φ)).graph) :
    (Matrix.toLin' T).graph.map (graphCoordinatePermutation R σ).toLinearMap = (Matrix.toLin' U).graph := by
  apply le_antisymm (graph_permutation_map_le_reflect φ hφ σ T U h.le)
  have hr : (Matrix.toLin' (U.map φ)).graph.map (graphCoordinatePermutation S σ.symm).toLinearMap =
      (Matrix.toLin' (T.map φ)).graph := by
    rw [← graphCoordinatePermutation_symm]
    exact submodule_map_equiv_reverse _ _ _ h
  have hrR := graph_permutation_map_le_reflect φ hφ σ.symm U T hr.le
  intro y hy
  have hmem : (graphCoordinatePermutation R σ).symm y ∈ (Matrix.toLin' T).graph := by
    rw [graphCoordinatePermutation_symm]
    exact hrR ⟨y, hy, rfl⟩
  exact ⟨(graphCoordinatePermutation R σ).symm y, hmem, (graphCoordinatePermutation R σ).apply_symm_apply y⟩

/-- An integral graph transition existing after an injective coefficient extension already exists before extension. -/
theorem graphTransitionMatrix_reflect (φ : R →+* S) (hφ : Function.Injective φ)
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T U : Matrix (Fin n) (Fin m) R)
    (hS : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation S σ) (Matrix.toLin' (T.map φ))))
    (hU : graphTransitionMatrix σ (T.map φ) hS = U.map φ) :
    ∃ hR : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)),
      graphTransitionMatrix σ T hR = U := by
  have hL : (Matrix.toLin' (T.map φ)).graph.map (graphCoordinatePermutation S σ).toLinearMap =
      (Matrix.toLin' (U.map φ)).graph := by
    have he := congrArg Matrix.toLin' hU
    rw [graphTransitionMatrix, Matrix.toLin'_toMatrix'] at he
    exact (graphTransition_map_graph (graphCoordinatePermutation S σ) (Matrix.toLin' (T.map φ)) hS).trans
      (congrArg LinearMap.graph he)
  have hR := graph_permutation_map_eq_reflect φ hφ σ T U hL
  have hb : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)) := by
    apply (graphTransition_overlap_iff _ _).mpr
    rw [hR]
    exact graphChartQuotientMap_graph_bijective _
  refine ⟨hb, ?_⟩
  have he : graphTransition (graphCoordinatePermutation R σ) (Matrix.toLin' T) hb = Matrix.toLin' U :=
    linearMap_graph_injective ((graphTransition_map_graph _ _ hb).symm.trans hR)
  exact (congrArg LinearMap.toMatrix' he).trans (LinearMap.toMatrix'_toLin' U)

end
end PfaffianDescent

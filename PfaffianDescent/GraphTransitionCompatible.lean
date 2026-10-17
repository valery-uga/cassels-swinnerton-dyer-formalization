import PfaffianDescent.GrassmannianTransitionScalar

namespace PfaffianDescent
section
variable {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}

lemma graphTransition_blocks_map_of_compatible (φ : R →+* S)
    (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) (g : (Fin m → S) →ₗ[S] (Fin n → S))
    (hfg : ∀ a, g (φ ∘ a) = φ ∘ f a) (a : Fin m → R) :
    (graphTransitionFirst (graphCoordinatePermutation S σ) g (φ ∘ a),
     graphTransitionSecond (graphCoordinatePermutation S σ) g (φ ∘ a)) =
    (φ ∘ graphTransitionFirst (graphCoordinatePermutation R σ) f a,
     φ ∘ graphTransitionSecond (graphCoordinatePermutation R σ) f a) := by
  change graphCoordinatePermutation S σ (φ ∘ a, g (φ ∘ a)) = _
  rw [hfg]
  exact graphCoordinatePermutation_map φ σ (a, f a)

/-- Graph normalization commutes with coefficient maps for any compatible linear maps. -/
lemma graphTransition_map_of_compatible (φ : R →+* S)
    (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) (g : (Fin m → S) →ₗ[S] (Fin n → S))
    (hfg : ∀ a, g (φ ∘ a) = φ ∘ f a)
    (hR : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) f))
    (hS : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation S σ) g))
    (a : Fin m → R) :
    graphTransition (graphCoordinatePermutation S σ) g hS (φ ∘ a) =
      φ ∘ graphTransition (graphCoordinatePermutation R σ) f hR a := by
  obtain ⟨b, rfl⟩ := hR.surjective a
  have hp := congrArg Prod.fst (graphTransition_blocks_map_of_compatible φ σ f g hfg b)
  have hq := congrArg Prod.snd (graphTransition_blocks_map_of_compatible φ σ f g hfg b)
  dsimp only [Prod.fst, Prod.snd] at hp hq
  rw [← hp, graphTransition_apply_first, graphTransition_apply_first]
  exact hq

end
end PfaffianDescent

import PfaffianDescent.GrassmannianMinor

namespace PfaffianDescent
section
variable {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}

lemma graphCoordinatePermutation_symm (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (graphCoordinatePermutation R σ).symm = graphCoordinatePermutation R σ.symm := by
  apply LinearEquiv.ext
  intro x
  rfl

lemma graphCoordinatePermutation_map (φ : R →+* S) (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (x : (Fin m → R) × (Fin n → R)) :
    graphCoordinatePermutation S σ (φ ∘ x.1, φ ∘ x.2) =
      (φ ∘ (graphCoordinatePermutation R σ x).1, φ ∘ (graphCoordinatePermutation R σ x).2) := by
  apply Prod.ext
  · funext i
    rw [graphCoordinatePermutation_fst]
    change Sum.elim (φ ∘ x.1) (φ ∘ x.2) (σ (Sum.inl i)) =
      φ (Sum.elim x.1 x.2 (σ (Sum.inl i)))
    rcases σ (Sum.inl i) with a | a <;> rfl
  · funext i
    rw [graphCoordinatePermutation_snd]
    change Sum.elim (φ ∘ x.1) (φ ∘ x.2) (σ (Sum.inr i)) =
      φ (Sum.elim x.1 x.2 (σ (Sum.inr i)))
    rcases σ (Sum.inr i) with a | a <;> rfl

lemma graphTransition_blocks_map (φ : R →+* S) (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) (a : Fin m → R) :
    (graphTransitionFirst (graphCoordinatePermutation S σ) (Matrix.toLin' (T.map φ)) (φ ∘ a),
     graphTransitionSecond (graphCoordinatePermutation S σ) (Matrix.toLin' (T.map φ)) (φ ∘ a)) =
    (φ ∘ graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T) a,
     φ ∘ graphTransitionSecond (graphCoordinatePermutation R σ) (Matrix.toLin' T) a) := by
  have hm : Matrix.toLin' (T.map φ) (φ ∘ a) = φ ∘ Matrix.toLin' T a := by
    funext i
    exact (RingHom.map_mulVec φ T a i).symm
  change graphCoordinatePermutation S σ (φ ∘ a, Matrix.toLin' (T.map φ) (φ ∘ a)) = _
  rw [hm]
  exact graphCoordinatePermutation_map φ σ (a, Matrix.toLin' T a)

/-- The normalized transition formula is compatible with arbitrary ring maps. -/
lemma graphTransition_map (φ : R →+* S) (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R)
    (hR : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)))
    (hS : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation S σ)
      (Matrix.toLin' (T.map φ)))) (a : Fin m → R) :
    graphTransition (graphCoordinatePermutation S σ) (Matrix.toLin' (T.map φ)) hS (φ ∘ a) =
      φ ∘ graphTransition (graphCoordinatePermutation R σ) (Matrix.toLin' T) hR a := by
  obtain ⟨b, rfl⟩ := hR.surjective a
  have hp := congrArg Prod.fst (graphTransition_blocks_map φ σ T b)
  have hq := congrArg Prod.snd (graphTransition_blocks_map φ σ T b)
  dsimp only [Prod.fst, Prod.snd] at hp hq
  rw [← hp, graphTransition_apply_first, graphTransition_apply_first]
  exact hq

lemma graphTransition_matrix_map (φ : R →+* S) (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R)
    (hR : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)))
    (hS : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation S σ)
      (Matrix.toLin' (T.map φ)))) :
    (LinearMap.toMatrix' (graphTransition (graphCoordinatePermutation R σ) (Matrix.toLin' T) hR)).map φ =
      LinearMap.toMatrix' (graphTransition (graphCoordinatePermutation S σ)
        (Matrix.toLin' (T.map φ)) hS) := by
  ext i j
  have h := congrFun (graphTransition_map φ σ T hR hS (Pi.single j 1)) i
  have hs : φ ∘ Pi.single j (1 : R) = Pi.single j (1 : S) := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [hs] at h
  exact h.symm

/-- A version of scalar compatibility with an explicitly named target matrix. -/
lemma graphTransition_matrix_map_of_eq (φ : R →+* S)
    (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) (U : Matrix (Fin n) (Fin m) S)
    (hU : T.map φ = U)
    (hR : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)))
    (hS : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation S σ) (Matrix.toLin' U))) :
    (LinearMap.toMatrix' (graphTransition (graphCoordinatePermutation R σ) (Matrix.toLin' T) hR)).map φ =
      LinearMap.toMatrix' (graphTransition (graphCoordinatePermutation S σ) (Matrix.toLin' U) hS) := by
  subst U
  exact graphTransition_matrix_map φ σ T hR hS

lemma graphTransition_matrix_inverse (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)))
    (hb : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ.symm)
      (Matrix.toLin' (LinearMap.toMatrix'
        (graphTransition (graphCoordinatePermutation R σ) (Matrix.toLin' T) h))))) :
    LinearMap.toMatrix' (graphTransition (graphCoordinatePermutation R σ.symm)
      (Matrix.toLin' (LinearMap.toMatrix'
        (graphTransition (graphCoordinatePermutation R σ) (Matrix.toLin' T) h))) hb) = T := by
  have hi := congrArg LinearMap.toMatrix'
    (graphTransition_inverse (graphCoordinatePermutation R σ) (Matrix.toLin' T) h)
  simpa only [graphCoordinatePermutation_symm, Matrix.toLin'_toMatrix',
    LinearMap.toMatrix'_toLin'] using hi

end
end PfaffianDescent

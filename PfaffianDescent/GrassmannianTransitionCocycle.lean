import PfaffianDescent.GrassmannianTransitionScalar

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R] {m n : ℕ}

lemma graphCoordinatePermutation_refl :
    graphCoordinatePermutation R (Equiv.refl (Fin m ⊕ Fin n)) = LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro x
  rfl

/-- Coordinate pullback reverses the order of permutation composition. -/
lemma graphCoordinatePermutation_trans (σ τ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (graphCoordinatePermutation R σ).trans (graphCoordinatePermutation R τ) =
      graphCoordinatePermutation R (τ.trans σ) := by
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · funext i
    change Sum.elim
      (fun j => Sum.elim x.1 x.2 (σ (Sum.inl j)))
      (fun j => Sum.elim x.1 x.2 (σ (Sum.inr j))) (τ (Sum.inl i)) =
        Sum.elim x.1 x.2 (σ (τ (Sum.inl i)))
    cases τ (Sum.inl i) <;> rfl
  · funext i
    change Sum.elim
      (fun j => Sum.elim x.1 x.2 (σ (Sum.inl j)))
      (fun j => Sum.elim x.1 x.2 (σ (Sum.inr j))) (τ (Sum.inr i)) =
        Sum.elim x.1 x.2 (σ (τ (Sum.inr i)))
    cases τ (Sum.inr i) <;> rfl

lemma graphTransitionFirst_refl (f : (Fin m → R) →ₗ[R] (Fin n → R)) :
    graphTransitionFirst (LinearEquiv.refl R _) f = LinearMap.id := rfl

lemma graphTransition_refl (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (h : Function.Bijective (graphTransitionFirst (LinearEquiv.refl R _) f)) :
    graphTransition (LinearEquiv.refl R _) f h = f := by
  apply LinearMap.ext
  intro a
  exact graphTransition_apply_first (LinearEquiv.refl R _) f h a

/-- The determinant transformation rule on a triple chart intersection. -/
lemma graphOverlapDeterminant_comp
    (e d : ((Fin m → R) × (Fin n → R)) ≃ₗ[R] ((Fin m → R) × (Fin n → R)))
    (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (he : Function.Bijective (graphTransitionFirst e f)) :
    graphOverlapDeterminant (e.trans d) f =
      graphOverlapDeterminant d (graphTransition e f he) * graphOverlapDeterminant e f := by
  unfold graphOverlapDeterminant
  rw [graphTransitionFirst_comp e d f he, LinearMap.det_comp]

/-- The two tests for a triple overlap are equivalent after entering the second chart. -/
lemma graphTransition_overlap_after
    (e d : ((Fin m → R) × (Fin n → R)) ≃ₗ[R] ((Fin m → R) × (Fin n → R)))
    (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (he : Function.Bijective (graphTransitionFirst e f)) :
    Function.Bijective (graphTransitionFirst d (graphTransition e f he)) ↔
      Function.Bijective (graphTransitionFirst (e.trans d) f) := by
  rw [graphTransitionFirst_comp e d f he]
  exact (Function.Bijective.of_comp_iff _ he).symm

/-- Normalized matrix coordinates for a Grassmannian transition. -/
noncomputable def graphTransitionMatrix (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T))) :
    Matrix (Fin n) (Fin m) R :=
  LinearMap.toMatrix' (graphTransition (graphCoordinatePermutation R σ) (Matrix.toLin' T) h)

lemma graphTransitionMatrix_refl (T : Matrix (Fin n) (Fin m) R)
    (h : Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation R (Equiv.refl _)) (Matrix.toLin' T))) :
    graphTransitionMatrix (Equiv.refl _) T h = T := by
  have hr : Function.Bijective (graphTransitionFirst (LinearEquiv.refl R _) (Matrix.toLin' T)) :=
    Function.bijective_id
  have hi := congrArg LinearMap.toMatrix' (graphTransition_refl (Matrix.toLin' T) hr)
  simpa only [graphTransitionMatrix, graphCoordinatePermutation_refl,
    LinearMap.toMatrix'_toLin'] using hi

lemma graphTransitionMatrix_overlap_after (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T))) :
    Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R τ)
      (Matrix.toLin' (graphTransitionMatrix σ T h))) ↔
      Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R (τ.trans σ))
        (Matrix.toLin' T)) := by
  simpa only [graphTransitionMatrix, Matrix.toLin'_toMatrix', graphCoordinatePermutation_trans] using
    graphTransition_overlap_after (graphCoordinatePermutation R σ)
      (graphCoordinatePermutation R τ) (Matrix.toLin' T) h

/-- The cocycle identity in actual matrix coordinates, over arbitrary commutative rings. -/
theorem graphTransitionMatrix_cocycle (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R)
    (hσ : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)))
    (hτ : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R τ)
      (Matrix.toLin' (graphTransitionMatrix σ T hσ))))
    (hστ : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R (τ.trans σ))
      (Matrix.toLin' T))) :
    graphTransitionMatrix τ (graphTransitionMatrix σ T hσ) hτ =
      graphTransitionMatrix (τ.trans σ) T hστ := by
  have hd : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R τ)
      (graphTransition (graphCoordinatePermutation R σ) (Matrix.toLin' T) hσ)) := by
    simpa only [graphTransitionMatrix, Matrix.toLin'_toMatrix'] using hτ
  have hed := graphTransition_comp_overlap (graphCoordinatePermutation R σ)
    (graphCoordinatePermutation R τ) (Matrix.toLin' T) hσ hd
  have hc := congrArg LinearMap.toMatrix' (graphTransition_cocycle
    (graphCoordinatePermutation R σ) (graphCoordinatePermutation R τ) (Matrix.toLin' T) hσ hd hed)
  simpa only [graphTransitionMatrix, Matrix.toLin'_toMatrix', graphCoordinatePermutation_trans] using hc

lemma graphTransitionMatrix_congr (σ : Equiv.Perm (Fin m ⊕ Fin n))
    {T U : Matrix (Fin n) (Fin m) R} (hTU : T = U)
    (hT : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)))
    (hU : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' U))) :
    graphTransitionMatrix σ T hT = graphTransitionMatrix σ U hU := by
  subst U
  rfl

end
end PfaffianDescent

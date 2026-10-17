import PfaffianDescent.GrassmannianTransitionCocycle
import PfaffianDescent.ValuationFiniteRatios

namespace PfaffianDescent
open Matrix
section
variable {R : Type*} [CommRing R] {m n : ℕ}

/-- The complementary rows after the ambient coordinate permutation. -/
def graphComplementMatrix (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    Matrix (Fin n) (Fin m) R :=
  fun i j => graphColumnEntry T (σ (Sum.inr i)) j

lemma graphComplementMatrix_toLin (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) :
    Matrix.toLin' (graphComplementMatrix σ T) =
      graphTransitionSecond (graphCoordinatePermutation R σ) (Matrix.toLin' T) := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_toLin']
  funext i j
  rw [LinearMap.toMatrix'_apply]
  change graphColumnEntry T (σ (Sum.inr i)) j =
    Sum.elim (Pi.single j 1) (T *ᵥ Pi.single j 1) (σ (Sum.inr i))
  cases h : σ (Sum.inr i) with
  | inl k => simp [graphColumnEntry, Pi.single_apply, eq_comm]
  | inr k => simp [graphColumnEntry]

lemma graphTransitionMatrix_mul_overlap (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T))) :
    graphTransitionMatrix σ T h * graphOverlapMatrix σ T = graphComplementMatrix σ T := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, graphOverlapMatrix_toLin, graphComplementMatrix_toLin]
  rw [graphTransitionMatrix, Matrix.toLin'_toMatrix']
  change (graphTransition (graphCoordinatePermutation R σ) (Matrix.toLin' T) h).comp
    (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)) = _
  apply LinearMap.ext
  intro a
  exact graphTransition_apply_first _ _ h a

lemma graphOverlapMatrix_swap (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) (i : Fin n) (j : Fin m) :
    graphOverlapMatrix ((Equiv.swap (Sum.inl j) (Sum.inr i)).trans σ) T =
      (graphOverlapMatrix σ T).updateRow j (graphComplementMatrix σ T i) := by
  funext a b
  by_cases h : a = j
  · subst a
    simp [graphOverlapMatrix, graphComplementMatrix]
  · simp [graphOverlapMatrix, graphComplementMatrix, Matrix.updateRow, Function.update,
      Equiv.swap_apply_def, h]

/-- Replacing one pivot row computes the corresponding normalized graph entry times the pivot minor. -/
lemma graphTransitionMatrix_minor_mul (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T)))
    (i : Fin n) (j : Fin m) :
    (graphOverlapMatrix ((Equiv.swap (Sum.inl j) (Sum.inr i)).trans σ) T).det =
      graphTransitionMatrix σ T h i j * (graphOverlapMatrix σ T).det := by
  have he : graphComplementMatrix σ T i =
      ∑ k, (graphTransitionMatrix σ T h i k) • (graphOverlapMatrix σ T k) := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (congrFun (congrFun (graphTransitionMatrix_mul_overlap σ T h) i) b).symm
  rw [graphOverlapMatrix_swap, he]
  exact Matrix.det_updateRow_sum _ j _

lemma graphOverlapMatrix_refl (T : Matrix (Fin n) (Fin m) R) :
    graphOverlapMatrix (Equiv.refl _) T = 1 := by
  funext i j
  simp [graphOverlapMatrix, graphColumnEntry, Matrix.one_apply]

end
section
variable {L : Type*} [Field L] {m n : ℕ}

lemma graphTransitionMatrix_minor_ratio (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) L)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation L σ) (Matrix.toLin' T)))
    (i : Fin n) (j : Fin m) :
    graphTransitionMatrix σ T h i j =
      (graphOverlapMatrix ((Equiv.swap (Sum.inl j) (Sum.inr i)).trans σ) T).det /
        (graphOverlapMatrix σ T).det := by
  have hu : IsUnit (graphOverlapMatrix σ T).det := by
    rw [graphOverlapMatrix_det]
    exact (graphOverlapDeterminant_isUnit_iff _ _).mpr h
  apply (eq_div_iff hu.ne_zero).mpr
  exact (graphTransitionMatrix_minor_mul σ T h i j).symm

end
section
variable (R : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
    {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L] {m n : ℕ}

/-- Every fraction-field graph admits a coordinate chart with integral normalized graph entries. -/
theorem graph_exists_integral_normalization (T : Matrix (Fin n) (Fin m) L) :
    ∃ (σ : Equiv.Perm (Fin m ⊕ Fin n))
      (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation L σ) (Matrix.toLin' T))),
      ∀ i j, IsLocalization.IsInteger R (graphTransitionMatrix σ T h i j) := by
  classical
  have hn : ∃ σ : Equiv.Perm (Fin m ⊕ Fin n), (graphOverlapMatrix σ T).det ≠ 0 := by
    refine ⟨Equiv.refl _, ?_⟩
    rw [graphOverlapMatrix_refl, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨σ, hσ, hrat⟩ := valuation_finite_integral_ratios R (fun σ => (graphOverlapMatrix σ T).det) hn
  have hb : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation L σ) (Matrix.toLin' T)) := by
    apply (graphOverlapDeterminant_isUnit_iff _ _).mp
    rw [← graphOverlapMatrix_det]
    exact isUnit_iff_ne_zero.mpr hσ
  refine ⟨σ, hb, fun i j => ?_⟩
  rw [graphTransitionMatrix_minor_ratio]
  exact hrat _

end
end PfaffianDescent

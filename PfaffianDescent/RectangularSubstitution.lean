import PfaffianDescent.PolynomialLinearChange

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [CommRing K] {l m n : ℕ}

/-- Linear homogeneous coordinates for a rectangular linear map. -/
noncomputable def rectangularLinearCoordinate (M : Matrix (Fin m) (Fin n) K) (i : Fin m) :
    MvPolynomial (Fin n) K := (M.map MvPolynomial.C).mulVec MvPolynomial.X i

/-- Evaluating a matrix-defined linear coordinate gives the corresponding
matrix-vector product after scalar extension. -/
theorem eval₂_rectangularLinearCoordinate {L : Type*} [CommRing L]
    (M : Matrix (Fin m) (Fin n) K) (i : Fin m) (f : K →+* L) (c : Fin n → L) :
    (rectangularLinearCoordinate M i).eval₂ f c = (M.map f).mulVec c i := by
  simp [rectangularLinearCoordinate, Matrix.mulVec, dotProduct]

noncomputable def rectangularSubstitution (M : Matrix (Fin m) (Fin n) K) :
    MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (rectangularLinearCoordinate M)

@[simp] lemma rectangularSubstitution_X (M : Matrix (Fin m) (Fin n) K) (i : Fin m) :
    rectangularSubstitution M (X i) = rectangularLinearCoordinate M i := aeval_X _ _

lemma rectangularLinearCoordinate_homogeneous (M : Matrix (Fin m) (Fin n) K) (i : Fin m) :
    (rectangularLinearCoordinate M i).IsHomogeneous 1 := by
  change (∑ j, C (M i j) * X j) ∈ homogeneousSubmodule (Fin n) K 1
  exact Submodule.sum_mem _ (fun j _ => isHomogeneous_C_mul_X (M i j) j)

lemma rectangularSubstitution_homogeneous (M : Matrix (Fin m) (Fin n) K)
    {f : MvPolynomial (Fin m) K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (rectangularSubstitution M f).IsHomogeneous d := by
  change (MvPolynomial.aeval (rectangularLinearCoordinate M) f).IsHomogeneous d
  simpa only [one_mul] using
    hf.aeval (rectangularLinearCoordinate M) (rectangularLinearCoordinate_homogeneous M)

lemma rectangularSubstitution_coordinate (M : Matrix (Fin m) (Fin n) K)
    (N : Matrix (Fin l) (Fin m) K) (i : Fin l) :
    rectangularSubstitution M (rectangularLinearCoordinate N i) =
      rectangularLinearCoordinate (N*M) i := by
  calc
    _ = (N.map MvPolynomial.C).mulVec (rectangularLinearCoordinate M) i := by
      change aeval (rectangularLinearCoordinate M) (∑ j, C (N i j) * X j) =
        ∑ j, C (N i j) * rectangularLinearCoordinate M j
      simp only [map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
    _ = rectangularLinearCoordinate (N*M) i := by
      unfold rectangularLinearCoordinate
      rw [Matrix.mulVec_mulVec, Matrix.map_mul]

lemma rectangularSubstitution_comp (M : Matrix (Fin m) (Fin n) K)
    (N : Matrix (Fin l) (Fin m) K) :
    (rectangularSubstitution M).comp (rectangularSubstitution N) =
      rectangularSubstitution (N*M) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, rectangularSubstitution_X, rectangularSubstitution_coordinate,
    rectangularSubstitution_X]

lemma rectangularSubstitution_one : rectangularSubstitution (1 : Matrix (Fin n) (Fin n) K) =
    AlgHom.id K (MvPolynomial (Fin n) K) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [rectangularSubstitution_X]
  change ((1 : Matrix (Fin n) (Fin n) K).map MvPolynomial.C).mulVec MvPolynomial.X i = X i
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

/-- Extending coefficients commutes with a matrix-defined homogeneous
coordinate substitution. -/
lemma rectangularSubstitution_map_comm
    {L : Type*} [CommRing L] (f : K →+* L)
    (M : Matrix (Fin m) (Fin n) K) :
    (MvPolynomial.map f).comp (rectangularSubstitution M).toRingHom =
      (rectangularSubstitution (M.map f)).toRingHom.comp (MvPolynomial.map f) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [rectangularSubstitution]
  · intro i
    simp only [RingHom.comp_apply, map_X]
    unfold rectangularSubstitution
    change MvPolynomial.map f ((MvPolynomial.aeval (rectangularLinearCoordinate M)) (X i)) =
      (MvPolynomial.aeval (rectangularLinearCoordinate (M.map f))) (X i)
    rw [aeval_X, aeval_X]
    unfold rectangularLinearCoordinate
    simp [Matrix.mulVec, dotProduct]

/-- The coordinate restriction to a split linear subspace is surjective. -/
theorem rectangularSubstitution_surjective (M : Matrix (Fin m) (Fin n) K)
    (N : Matrix (Fin n) (Fin m) K) (hNM : N*M = 1) :
    Function.Surjective (rectangularSubstitution M) := by
  intro p
  refine ⟨rectangularSubstitution N p, ?_⟩
  have h := AlgHom.congr_fun (rectangularSubstitution_comp M N) p
  rw [hNM, rectangularSubstitution_one] at h
  exact h

end
end PfaffianDescent

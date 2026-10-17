import PfaffianDescent.PolynomialLinearChange
import PfaffianDescent.VoisinSectionRestriction
import PfaffianDescent.CubicLinear
import PfaffianDescent.MultivariateCubic
import PfaffianDescent.VoisinCubicCoordinateNormalization

/-!
# Homogeneous evaluation under a linear coordinate change

An invertible linear change of projective coordinates preserves the
independence of the conditions imposed on homogeneous forms by a finite
ordered family of points.  This is the evaluation-map transport needed to
return the explicit split four-line witness to the original cubic surface.
-/

namespace PfaffianDescent

open MvPolynomial

universe u v w

/-- Evaluating a polynomial with coordinates in a function ring and then at
one component is ordinary evaluation at the corresponding point. -/
lemma eval₂_pi_apply
    {K : Type u} [Field K] {I : Type v} {σ : Type w}
    (x : σ → I → K) (P : MvPolynomial σ K) (i : I) :
    MvPolynomial.eval₂ (algebraMap K (I → K)) x P i =
      MvPolynomial.eval₂ (RingHom.id K) (fun j => x j i) P := by
  let ev : (I → K) →+* K := Pi.evalRingHom (fun _ : I => K) i
  have h : ev.comp (MvPolynomial.eval₂Hom (algebraMap K (I → K)) x) =
      MvPolynomial.eval₂Hom (RingHom.id K) (fun j => x j i) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ev]
    · intro j
      simp [ev]
  exact DFunLike.congr_fun h P

/-- An invertible linear change applied simultaneously to finitely many
points preserves surjectivity of homogeneous section evaluation. -/
theorem homogeneousSectionRestriction_surjective_linearChange
    {K : Type u} [Field K] {n d : ℕ} {I : Type} [Fintype I]
    (M : Matrix (Fin n) (Fin n) K) (hM : IsUnit M.det)
    (y : I → Fin n → K)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := K)
        (fun (j : Fin n) (i : I) => y i j) d)) :
    Function.Surjective
      (homogeneousSectionRestriction (K := K)
        (fun (j : Fin n) (i : I) => M.mulVec (y i) j) d) := by
  intro a
  obtain ⟨Q, hQ⟩ := hsurj a
  let P : homogeneousSubmodule (Fin n) K d :=
    ⟨linearSubstitution M⁻¹ Q.1,
      linearSubstitution_homogeneous M⁻¹ Q.2⟩
  refine ⟨P, ?_⟩
  funext i
  have hQi := congrFun hQ i
  rw [homogeneousSectionRestriction_apply]
  change MvPolynomial.eval₂ (algebraMap K (I → K))
      (fun j i => M.mulVec (y i) j) (linearSubstitution M⁻¹ Q.1) i = a i
  rw [eval₂_pi_apply]
  change MvPolynomial.aeval (fun j => M.mulVec (y i) j)
      (linearSubstitution M⁻¹ Q.1) = a i
  rw [linearSubstitution_eval, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
  rw [homogeneousSectionRestriction_apply] at hQi
  change MvPolynomial.eval₂ (algebraMap K (I → K))
      (fun j i => y i j) Q.1 i = a i at hQi
  rw [eval₂_pi_apply] at hQi
  change MvPolynomial.aeval (y i) Q.1 = a i at hQi
  exact hQi

/-- Mapping the coefficients of a cubic by the identity homomorphism does
nothing. -/
lemma Cubic.map_id
    {K : Type u} [Field K] {n : ℕ} (c : Cubic K n) :
    c.map (RingHom.id K) = c := by
  funext i
  rfl

/-- Evaluation of a coordinate-changed cubic after scalar extension is
evaluation of the original cubic at the changed point. -/
lemma Cubic.compLinear_map_toMvPolynomial_eval
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    {n m : ℕ} (c : Cubic K n) (M : Matrix (Fin n) (Fin m) K)
    (y : Fin m → L) :
    ((c.compLinear M).map f).toMvPolynomial.eval y =
      (c.map f).toMvPolynomial.eval ((M.map f).mulVec y) := by
  have hleft := Cubic.eval_toMvPolynomial (RingHom.id L)
    ((c.compLinear M).map f) y
  rw [Cubic.map_id] at hleft
  have hright := Cubic.eval_toMvPolynomial (RingHom.id L)
    (c.map f) ((M.map f).mulVec y)
  rw [Cubic.map_id] at hright
  calc
    ((c.compLinear M).map f).toMvPolynomial.eval y =
        ((c.compLinear M).map f).eval y := hleft
    _ = (c.map f).eval ((M.map f).mulVec y) := by
      rw [Cubic.compLinear_map, Cubic.eval_compLinear]
    _ = (c.map f).toMvPolynomial.eval ((M.map f).mulVec y) := hright.symm

/-- A square matrix whose determinant is a unit remains a unit after a
field homomorphism is applied entrywise. -/
lemma Matrix.map_isUnit_of_isUnit_det
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : IsUnit M.det) :
    IsUnit (M.map f) := by
  rw [← RingHom.mapMatrix_apply]
  exact ((Matrix.isUnit_iff_isUnit_det M).mpr hM).map (RingHom.mapMatrix f)

/-- An invertible linear change preserves nonzero representatives. -/
lemma linearChange_points_nonzero
    {K : Type u} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : IsUnit M) {I : Type} (y : I → Fin n → K)
    (hy : ∀ i, y i ≠ 0) : ∀ i, M.mulVec (y i) ≠ 0 := by
  intro i hzero
  apply hy i
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hM)
  simpa using hzero

/-- An invertible linear change preserves pairwise projective
distinctness. -/
lemma linearChange_points_projectivelyDistinct
    {K : Type u} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : IsUnit M) {I : Type} (y : I → Fin n → K)
    (hy : ∀ i j, i ≠ j → ∀ a : K, a • y i ≠ y j) :
    ∀ i j, i ≠ j → ∀ a : K,
      a • M.mulVec (y i) ≠ M.mulVec (y j) := by
  intro i j hij a h
  apply hy i j hij a
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hM)
  simpa [Matrix.mulVec_smul] using h

/-- Pulling a form back by the inverse matrix and evaluating at the forward
image recovers its original value. -/
lemma linearSubstitution_nonsing_inv_eval_mulVec
    {K : Type u} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : IsUnit M.det)
    (P : MvPolynomial (Fin n) K) (y : Fin n → K) :
    (linearSubstitution M⁻¹ P).eval (M.mulVec y) = P.eval y := by
  change MvPolynomial.aeval (M.mulVec y) (linearSubstitution M⁻¹ P) =
    MvPolynomial.aeval y P
  rw [linearSubstitution_eval, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]

/-- Applying the inverse scalar-extended coordinate change to the changed
cubic equation recovers the original scalar-extended equation. -/
lemma Cubic.linearSubstitution_nonsing_inv_compLinear_map_toMvPolynomial
    {K L : Type u} [Field K] [Field L] [Infinite L] (f : K →+* L)
    (c : Cubic K 4) (M : Matrix (Fin 4) (Fin 4) K)
    (hM : IsUnit (M.map f).det) :
    linearSubstitution (M.map f)⁻¹
      (((c.compLinear M).map f).toMvPolynomial) =
        (c.map f).toMvPolynomial := by
  rw [Cubic.compLinear_map, Cubic.toMvPolynomial_compLinear]
  change ((linearSubstitution (M.map f)⁻¹).comp
    (linearSubstitution (M.map f))) ((c.map f).toMvPolynomial) = _
  rw [linearSubstitution_comp, Matrix.mul_nonsing_inv (M.map f) hM,
    linearSubstitution_one]
  rfl

end PfaffianDescent

import PfaffianDescent.HomogeneousProjection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K] {n : ℕ}

noncomputable def linearCoordinate (M : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    MvPolynomial (Fin n) K := (M.map MvPolynomial.C).mulVec MvPolynomial.X i

noncomputable def linearSubstitution (M : Matrix (Fin n) (Fin n) K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (linearCoordinate M)

@[simp] lemma linearSubstitution_X (M : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    linearSubstitution M (X i) = linearCoordinate M i := MvPolynomial.aeval_X _ _

lemma linearCoordinate_homogeneous (M : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    (linearCoordinate M i).IsHomogeneous 1 := by
  change (∑ j, C (M i j) * X j) ∈ homogeneousSubmodule (Fin n) K 1
  exact Submodule.sum_mem _ (fun j _ => isHomogeneous_C_mul_X (M i j) j)

lemma linearSubstitution_homogeneous (M : Matrix (Fin n) (Fin n) K)
    {f : MvPolynomial (Fin n) K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (linearSubstitution M f).IsHomogeneous d := by
  change (MvPolynomial.aeval (linearCoordinate M) f).IsHomogeneous d
  have h := hf.aeval (linearCoordinate M) (linearCoordinate_homogeneous M)
  simpa only [one_mul] using h

lemma linearSubstitution_coordinate (M N : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    linearSubstitution M (linearCoordinate N i) = linearCoordinate (N*M) i := by
  calc
    _ = (N.map MvPolynomial.C).mulVec (linearCoordinate M) i := by
      change MvPolynomial.aeval (linearCoordinate M) (∑ j, C (N i j) * X j) =
        ∑ j, C (N i j) * linearCoordinate M j
      simp only [map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
    _ = linearCoordinate (N*M) i := by
      unfold linearCoordinate
      rw [Matrix.mulVec_mulVec, Matrix.map_mul]

lemma linearSubstitution_comp (M N : Matrix (Fin n) (Fin n) K) :
    (linearSubstitution M).comp (linearSubstitution N) = linearSubstitution (N*M) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, linearSubstitution_X, linearSubstitution_coordinate, linearSubstitution_X]

/-- Extending coefficients commutes with a linear coordinate polynomial. -/
lemma linearCoordinate_map {L : Type*} [Field L] (f : K →+* L)
    (M : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    MvPolynomial.map f (linearCoordinate M i) = linearCoordinate (M.map f) i := by
  simp [linearCoordinate, Matrix.mulVec, dotProduct]

/-- Extending coefficients commutes with a linear coordinate substitution
whose matrix is already defined over the ground field. -/
lemma linearSubstitution_map {L : Type*} [Field L] (f : K →+* L)
    (M : Matrix (Fin n) (Fin n) K) (P : MvPolynomial (Fin n) K) :
    MvPolynomial.map f (linearSubstitution M P) =
      linearSubstitution (M.map f) (MvPolynomial.map f P) := by
  have h : (MvPolynomial.map f).comp (linearSubstitution M).toRingHom =
      (linearSubstitution (M.map f)).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      change MvPolynomial.map f (linearSubstitution M (X i)) =
        linearSubstitution (M.map f) (MvPolynomial.map f (X i))
      rw [linearSubstitution_X, MvPolynomial.map_X, linearSubstitution_X]
      exact linearCoordinate_map f M i
  exact DFunLike.congr_fun h P

/-- Extending coefficients commutes with mapping an ideal after a linear
coordinate substitution. -/
theorem ideal_map_linearSubstitution_map {L : Type*} [Field L] (f : K →+* L)
    (I : Ideal (MvPolynomial (Fin n) K)) (M : Matrix (Fin n) (Fin n) K) :
    (I.map (linearSubstitution M).toRingHom).map (MvPolynomial.map f) =
      (I.map (MvPolynomial.map f)).map
        (linearSubstitution (M.map f)).toRingHom := by
  have hcomp : (MvPolynomial.map f).comp (linearSubstitution M).toRingHom =
      (linearSubstitution (M.map f)).toRingHom.comp (MvPolynomial.map f) := by
    apply RingHom.ext
    intro P
    exact linearSubstitution_map f M P
  calc
    (I.map (linearSubstitution M).toRingHom).map (MvPolynomial.map f) =
        I.map ((MvPolynomial.map f).comp (linearSubstitution M).toRingHom) :=
      Ideal.map_map _ _
    _ = I.map ((linearSubstitution (M.map f)).toRingHom.comp
          (MvPolynomial.map f)) := by rw [hcomp]
    _ = (I.map (MvPolynomial.map f)).map
          (linearSubstitution (M.map f)).toRingHom := (Ideal.map_map _ _).symm

lemma linearSubstitution_one : linearSubstitution (1 : Matrix (Fin n) (Fin n) K) =
    AlgHom.id K (MvPolynomial (Fin n) K) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [linearSubstitution_X]
  change ((1 : Matrix (Fin n) (Fin n) K).map MvPolynomial.C).mulVec MvPolynomial.X i = X i
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

/-- An invertible linear coordinate change induces an actual polynomial algebra isomorphism. -/
noncomputable def linearSubstitutionEquiv (M : Matrix (Fin n) (Fin n) K) (hM : IsUnit M.det) :
    MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K :=
  AlgEquiv.ofAlgHom (linearSubstitution M) (linearSubstitution M⁻¹)
    (by rw [linearSubstitution_comp, Matrix.nonsing_inv_mul M hM, linearSubstitution_one])
    (by rw [linearSubstitution_comp, Matrix.mul_nonsing_inv M hM, linearSubstitution_one])

lemma linearCoordinate_eval (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) (i : Fin n) :
    MvPolynomial.aeval x (linearCoordinate M i) = M.mulVec x i := by
  change MvPolynomial.aeval x (∑ j, C (M i j) * X j) = ∑ j, M i j * x j
  simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

lemma linearSubstitution_eval (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K)
    (f : MvPolynomial (Fin n) K) :
    MvPolynomial.aeval x (linearSubstitution M f) = MvPolynomial.aeval (M.mulVec x) f := by
  have h : (MvPolynomial.aeval x).comp (linearSubstitution M) =
      MvPolynomial.aeval (M.mulVec x) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, linearSubstitution_X, linearCoordinate_eval, aeval_X]
  exact AlgHom.congr_fun h f

/-- Evaluation of a linear coordinate after extending its coefficients to an
arbitrary commutative `K`-algebra. -/
lemma linearCoordinate_aeval {A : Type*} [CommRing A] [Algebra K A]
    (M : Matrix (Fin n) (Fin n) K) (x : Fin n → A) (i : Fin n) :
    MvPolynomial.aeval x (linearCoordinate M i) =
      (M.map (algebraMap K A)).mulVec x i := by
  simp [linearCoordinate, Matrix.mulVec, dotProduct]

/-- Evaluation commutes with a ground-field linear coordinate substitution
after extending its matrix entries to an arbitrary commutative `K`-algebra. -/
lemma linearSubstitution_aeval {A : Type*} [CommRing A] [Algebra K A]
    (M : Matrix (Fin n) (Fin n) K) (x : Fin n → A)
    (P : MvPolynomial (Fin n) K) :
    MvPolynomial.aeval x (linearSubstitution M P) =
      MvPolynomial.aeval ((M.map (algebraMap K A)).mulVec x) P := by
  have h : (MvPolynomial.aeval x).comp (linearSubstitution M) =
      MvPolynomial.aeval ((M.map (algebraMap K A)).mulVec x) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, linearSubstitution_X, linearCoordinate_aeval,
      MvPolynomial.aeval_X]
  exact DFunLike.congr_fun h P

end
end PfaffianDescent

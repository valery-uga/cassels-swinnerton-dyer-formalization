import PfaffianDescent.HomogeneousProjection
import PfaffianDescent.ProjectiveFiniteOfHilbertBound
import PfaffianDescent.ProjectiveLengthOfHilbert

/-!
# Length of a binary projective hypersurface

A nonzero homogeneous binary form of degree `n` cuts out a finite projective
scheme of rank `n`.  The proof calculates the homogeneous quotient directly,
then invokes the existing projective Hilbert-length interface.
-/

namespace PfaffianDescent

open MvPolynomial Module AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u

section

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev BinaryHomogeneous (K : Type u) [Field K] (d : ℕ) :=
  homogeneousSubmodule (Fin 2) K d

noncomputable def binaryProjectiveProjection
    (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous n) (d : ℕ) :
    BinaryHomogeneous K d →ₗ[K] CoordinateRing (equationIdeal P hP) :=
  (Ideal.Quotient.mkₐ K (equationIdeal P hP).toIdeal).toLinearMap.comp
    (BinaryHomogeneous K d).subtype

lemma binaryProjectiveProjection_range
    (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous n) (d : ℕ) :
    LinearMap.range (binaryProjectiveProjection P hP d) = grading (equationIdeal P hP) d := by
  rw [binaryProjectiveProjection, LinearMap.range_comp, Submodule.range_subtype]
  rfl

noncomputable def binaryProjectiveRelation
    (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous n) (d : ℕ) :
    BinaryHomogeneous K d →ₗ[K] BinaryHomogeneous K (d + n) where
  toFun q := ⟨q.val * P, q.property.mul hP⟩
  map_add' a b := by
    apply Subtype.ext
    exact add_mul a.val b.val P
  map_smul' r a := by
    apply Subtype.ext
    exact smul_mul_assoc r a.val P

lemma binaryProjectiveRelation_injective
    (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous n) (hP0 : P ≠ 0) (d : ℕ) :
    Function.Injective (binaryProjectiveRelation P hP d) := by
  intro a b hab
  apply Subtype.ext
  exact mul_right_cancel₀ hP0 (congrArg Subtype.val hab)

theorem binaryProjectiveRelation_range_eq_projection_ker
    (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous n) (hP0 : P ≠ 0) (d : ℕ) :
    LinearMap.range (binaryProjectiveRelation P hP d) =
      LinearMap.ker (binaryProjectiveProjection P hP (d + n)) := by
  apply le_antisymm
  · rintro v ⟨q, rfl⟩
    change Ideal.Quotient.mk (equationIdeal P hP).toIdeal (q.val * P) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mul_mem_left
    exact Ideal.subset_span (Set.mem_singleton P)
  · intro v hv
    change Ideal.Quotient.mk (equationIdeal P hP).toIdeal v.val = 0 at hv
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hv
    change v.val ∈ Ideal.span ({P} : Set (MvPolynomial (Fin 2) K)) at hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨q, hq⟩ := hmem
    have hqP : q * P = v.val := by
      rw [mul_comm]
      exact hq.symm
    have hqhom : q.IsHomogeneous d := homogeneous_of_mul_right hP hP0 (by
      rw [hqP]
      exact v.property)
    exact ⟨⟨q, hqhom⟩, Subtype.ext hqP⟩

lemma binary_homogeneous_finrank (d : ℕ) :
    finrank K (BinaryHomogeneous K d) = d + 1 := by
  rw [homogeneous_polynomial_finrank]
  have h : 2 + d - 1 = d + 1 := by omega
  rw [h]
  exact (Nat.choose_symm_add (a := d) (b := 1)).trans (Nat.choose_one_right _)

theorem binary_projective_grade_finrank
    (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous n) (hP0 : P ≠ 0) (d : ℕ) :
    finrank K (grading (equationIdeal P hP) (d + n)) = n := by
  have hdim := (binaryProjectiveProjection P hP (d + n)).finrank_range_add_finrank_ker
  rw [binaryProjectiveProjection_range,
    ← binaryProjectiveRelation_range_eq_projection_ker P hP hP0 d,
    LinearMap.finrank_range_of_inj (binaryProjectiveRelation_injective P hP hP0 d),
    binary_homogeneous_finrank, binary_homogeneous_finrank] at hdim
  omega

theorem binary_projective_isFinite [Infinite K]
    (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous n) (hP0 : P ≠ 0) :
    IsFinite (toBase (equationIdeal P hP)) := by
  apply projective_finite_of_hilbert_bound (equationIdeal P hP) n n
  intro d hd
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hd
  rw [hm]
  rw [Nat.add_comm n m]
  exact (binary_projective_grade_finrank P hP hP0 m).le

theorem binary_projective_finiteSchemeRank [Infinite K]
    (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous n) (hP0 : P ≠ 0)
    [IsFinite (toBase (equationIdeal P hP))] :
    AllCharacteristics.finiteSchemeRank (toBase (equationIdeal P hP)) = n := by
  apply projective_length_of_eventual_hilbert (equationIdeal P hP) n n
  intro d hd
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hd
  rw [hm]
  rw [Nat.add_comm n m]
  exact binary_projective_grade_finrank P hP hP0 m

end

end PfaffianDescent

import PfaffianDescent.ProjectiveRadical
import PfaffianDescent.ProjectiveFiniteOfHilbertBound

namespace PfaffianDescent
open Module
open AllCharacteristics.HomogeneousProjective
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] {z : A} (hz : z ∈ 𝒜 1)

/-- Multiplication by a degree-one element between consecutive graded pieces. -/
noncomputable def homogeneousGradeMul (n : ℕ) : 𝒜 n →ₗ[K] 𝒜 (n+1) where
  toFun a := ⟨a.val * z, SetLike.mul_mem_graded a.2 hz⟩
  map_add' a b := Subtype.ext (add_mul _ _ _)
  map_smul' r a := Subtype.ext (smul_mul_assoc _ _ _)

/-- Divisibility of a whole homogeneous piece gives surjectivity from the
preceding piece; projection extracts a homogeneous quotient. -/
theorem homogeneousGradeMul_surjective (n : ℕ)
    (hdiv : ∀ a ∈ 𝒜 (n+1), a ∈ Ideal.span {z}) :
    Function.Surjective (homogeneousGradeMul 𝒜 hz n) := by
  intro a
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hdiv a a.2)
  refine ⟨DirectSum.decompose 𝒜 b n, Subtype.ext ?_⟩
  change (DirectSum.decompose 𝒜 b n : A) * z = a.val
  rw [← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hz]
  rw [mul_comm b z, ← hb]
  exact DirectSum.decompose_of_mem_same 𝒜 a.2

end

section
universe u
variable {K : Type u} [Field K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For an eventually constant Hilbert function, a linear form avoiding the
projective scheme induces isomorphisms between all sufficiently high grades. -/
theorem quotient_grade_eventually_bijective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hnz : ∀ x : ProjectiveSpectrum (grading I), z ∉ x.asHomogeneousIdeal)
    (M D : ℕ) (hdim : ∀ n, M ≤ n → finrank K (grading I n) = D) :
    ∃ N : ℕ, M ≤ N ∧ ∀ n, N ≤ n →
      Function.Bijective (homogeneousGradeMul (grading I) hz n) := by
  have : ∀ n, Module.Finite K (grading I n) := polynomialQuotientGrade_finite I
  obtain ⟨N, hN⟩ := quotient_grade_eventually_mem_span I z hz hnz
  refine ⟨max N M, le_max_right _ _, fun n hn => ?_⟩
  have hs := homogeneousGradeMul_surjective (grading I) hz n (hN (n+1) (by omega))
  have he : finrank K (grading I n) = finrank K (grading I (n+1)) := by
    rw [hdim n (by omega), hdim (n+1) (by omega)]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mpr hs, hs⟩

end
end PfaffianDescent

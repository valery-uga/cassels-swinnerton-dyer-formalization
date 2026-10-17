import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

/-! Source only. An actual finite polynomial algebra quotient has a monomial
basis containing the unit, without a separability or primitive-element premise. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
universe u v w
variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
variable {σ : Type w}

theorem polynomialImageMonomials_span284
    (π : MvPolynomial σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    Submodule.span K (Set.range (fun e : σ →₀ ℕ => π (monomial e 1))) = ⊤ := by
  calc
    _ = (Submodule.span K (Set.range (basisMonomials σ K))).map π.toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = ⊤ := by
      rw [(basisMonomials σ K).span_eq, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr hπ

/-- The SAME polynomial images form an actual basis, indexed by the full
dimension. The distinguished exponent is literally zero and its basis vector
is literally one; no reduction of the original algebra is used. -/
theorem exists_polynomialImageMonomialBasis_containing_one284
    [Nontrivial A] [Module.Finite K A]
    (π : MvPolynomial σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    ∃ (B : Fin (Module.finrank K A) → (σ →₀ ℕ))
      (k : Fin (Module.finrank K A))
      (b : Basis (Fin (Module.finrank K A)) K A),
      B k = 0 ∧ b k = 1 ∧ ∀ j, b j = π (monomial (B j) 1) := by
  classical
  let S : Set A := Set.range (fun e : σ →₀ ℕ => π (monomial e 1))
  have hli : LinearIndepOn K id ({1} : Set A) :=
    (linearIndepOn_singleton_iff K).mpr one_ne_zero
  have hsub : ({1} : Set A) ⊆ S := by
    intro x hx
    have hx' : x = 1 := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨0, by simp⟩
  have hspan : ⊤ ≤ Submodule.span K S :=
    (polynomialImageMonomials_span284 π hπ).ge
  let b₀ := Basis.extendLe hli hsub hspan
  let e := b₀.indexEquiv (Module.finBasis K A)
  let b := b₀.reindex e
  have hrange : Set.range b = Set.range b₀ := b₀.range_reindex e
  have hunit : (1 : A) ∈ Set.range b := by
    rw [hrange]
    exact Basis.subset_extendLe hli hsub hspan (Set.mem_singleton 1)
  obtain ⟨k, hk⟩ := hunit
  have hmon : ∀ j, ∃ a : σ →₀ ℕ, π (monomial a 1) = b j := by
    intro j
    apply Basis.extendLe_subset hli hsub hspan
    rw [← hrange]
    exact Set.mem_range_self j
  let B : Fin (Module.finrank K A) → (σ →₀ ℕ) :=
    fun j => if j = k then 0 else Classical.choose (hmon j)
  refine ⟨B, k, b, ?_, hk, ?_⟩
  · simp [B]
  · intro j
    by_cases hj : j = k
    · subst j
      simpa [B] using hk
    · simpa [B, hj] using (Classical.choose_spec (hmon j)).symm

end PfaffianDescent

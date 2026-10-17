import AllCharacteristics.GaloisEmbeddingEnumeration

/-!
# Multiplicities invariant under a finite Galois group

For a finite separable extension `E/K` inside a finite Galois extension
`L/K`, the Galois group of `L/K` acts transitively on the `K`-embeddings of
`E` into `L`.  Consequently, a multiplicity function on those embeddings
which is invariant under postcomposition is constant, and its total is the
degree `[E : K]` times any one of its values.

This is the finite-field combinatorics needed to descend a Galois-stable
multiset of geometric points to an effective zero-cycle over `K`.
-/

open scoped BigOperators

namespace AllCharacteristics
universe u

section

variable (K E L : Type u) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [FiniteDimensional K L] [IsGalois K L]

/-- Any two `K`-embeddings of a finite separable extension into a finite
Galois target differ by postcomposition with a Galois automorphism of the
target. -/
theorem exists_galoisAlgEquiv_postcomp_eq
    (e₁ e₂ : E →ₐ[K] L) :
    ∃ g : L ≃ₐ[K] L, g.toAlgHom.comp e₁ = e₂ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  have hmin : minpoly K (e₂ α) = minpoly K (e₁ α) :=
    (minpoly.algHom_eq e₂ e₂.injective α).trans
      (minpoly.algHom_eq e₁ e₁.injective α).symm
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit L).mp hmin
  have hα' : Algebra.adjoin K ({α} : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsIntegral.of_finite K α).isAlgebraic, hα]
    rfl
  refine ⟨g, AlgHom.ext_of_adjoin_eq_top hα' ?_⟩
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  change g (e₁ α) = e₂ α
  exact hg

/-- The postcomposition action of the Galois group on the embeddings of
`E` into `L` is transitive. -/
theorem galoisEmbeddingPostcomp_transitive
    (e₁ e₂ : E →ₐ[K] L) :
    ∃ g : L ≃ₐ[K] L, g.toAlgHom.comp e₁ = e₂ :=
  exists_galoisAlgEquiv_postcomp_eq K E L e₁ e₂

/-- A multiplicity on the embeddings of `E` into `L` which is invariant
under the Galois group is constant. -/
theorem galoisInvariantMultiplicity_eq
    (m : (E →ₐ[K] L) → ℕ)
    (hm : ∀ (g : L ≃ₐ[K] L) (e : E →ₐ[K] L),
      m (g.toAlgHom.comp e) = m e)
    (e₁ e₂ : E →ₐ[K] L) :
    m e₁ = m e₂ := by
  obtain ⟨g, hg⟩ := exists_galoisAlgEquiv_postcomp_eq K E L e₁ e₂
  rw [← hg, hm]

/-- The total of a Galois-invariant embedding multiplicity is the residue
degree times its value at any chosen embedding. -/
theorem sum_galoisInvariantMultiplicity
    (m : (E →ₐ[K] L) → ℕ)
    (hm : ∀ (g : L ≃ₐ[K] L) (e : E →ₐ[K] L),
      m (g.toAlgHom.comp e) = m e)
    (e₀ : E →ₐ[K] L) :
    ∑ e : E →ₐ[K] L, m e = Module.finrank K E * m e₀ := by
  rw [← AlgHom.card_of_splits K E L (galoisTarget_splits_minpoly K E L)]
  exact Finset.sum_const_nat (fun e _ ↦
    galoisInvariantMultiplicity_eq K E L m hm e e₀)

/-- In the chosen enumeration of all embeddings, every index can be carried
to every other index by one of the induced Galois permutations. -/
theorem galoisEmbeddingPermutation_transitive
    (n : ℕ) (hn : Module.finrank K E = n) (i j : Fin n) :
    ∃ g : L ≃ₐ[K] L, galoisEmbeddingPermutation K E L n hn g i = j := by
  obtain ⟨g, hg⟩ := exists_galoisAlgEquiv_postcomp_eq K E L
    (galoisEmbeddingIndex K E L n hn i)
    (galoisEmbeddingIndex K E L n hn j)
  refine ⟨g, (galoisEmbeddingIndex K E L n hn).injective ?_⟩
  rw [galoisEmbeddingIndex_permutation]
  exact hg

/-- A function on the chosen embedding indices which is invariant under all
induced Galois permutations is constant. -/
theorem galoisEmbeddingIndex_invariant_eq
    (n : ℕ) (hn : Module.finrank K E = n)
    (m : Fin n → ℕ)
    (hm : ∀ (g : L ≃ₐ[K] L) (i : Fin n),
      m (galoisEmbeddingPermutation K E L n hn g i) = m i)
    (i j : Fin n) :
    m i = m j := by
  obtain ⟨g, hg⟩ := galoisEmbeddingPermutation_transitive K E L n hn i j
  rw [← hg, hm]

end

end AllCharacteristics

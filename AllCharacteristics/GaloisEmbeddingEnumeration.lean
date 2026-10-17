import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Enumerating embeddings inside a finite Galois extension

If a finite separable extension `E/K` embeds in a finite Galois extension
`L/K`, its `K`-embeddings into `L` are exactly `[E : K]` in number.  We choose
an enumeration and record the permutation induced by postcomposition with a
Galois automorphism.
-/

namespace AllCharacteristics
universe u

section
variable (K E L : Type u) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [FiniteDimensional K E] [Algebra.IsSeparable K E] [IsGalois K L]

lemma galoisTarget_splits_minpoly (x : E) :
    ((minpoly K x).map (algebraMap K L)).Splits := by
  have h := IsGalois.splits K (algebraMap E L x)
  rw [minpoly.algebraMap_eq (algebraMap E L).injective x] at h
  exact h

/-- A chosen enumeration of all embeddings of `E` in the Galois target `L`. -/
noncomputable def galoisEmbeddingIndex (n : ℕ) (hn : Module.finrank K E = n) :
    Fin n ≃ (E →ₐ[K] L) :=
  (Fintype.equivFinOfCardEq
    ((AlgHom.card_of_splits K E L (galoisTarget_splits_minpoly K E L)).trans hn)).symm

/-- Postcomposition by a Galois automorphism permutes the embeddings. -/
noncomputable def galoisEmbeddingPostcomp (g : L ≃ₐ[K] L) :
    (E →ₐ[K] L) ≃ (E →ₐ[K] L) where
  toFun e := g.toAlgHom.comp e
  invFun e := g.symm.toAlgHom.comp e
  left_inv e := by
    ext x
    simp
  right_inv e := by
    ext x
    simp

/-- The permutation of a chosen embedding enumeration induced by a Galois
automorphism. -/
noncomputable def galoisEmbeddingPermutation (n : ℕ)
    (hn : Module.finrank K E = n) (g : L ≃ₐ[K] L) : Equiv.Perm (Fin n) :=
  (galoisEmbeddingIndex K E L n hn).trans
    ((galoisEmbeddingPostcomp K E L g).trans
      (galoisEmbeddingIndex K E L n hn).symm)

lemma galoisEmbeddingIndex_permutation (n : ℕ)
    (hn : Module.finrank K E = n) (g : L ≃ₐ[K] L) (i : Fin n) :
    galoisEmbeddingIndex K E L n hn (galoisEmbeddingPermutation K E L n hn g i) =
      g.toAlgHom.comp (galoisEmbeddingIndex K E L n hn i) := by
  simp [galoisEmbeddingPermutation, galoisEmbeddingPostcomp]

end
end AllCharacteristics

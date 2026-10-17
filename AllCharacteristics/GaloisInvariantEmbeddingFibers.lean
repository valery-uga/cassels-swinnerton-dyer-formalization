import AllCharacteristics.GaloisInvariantMultiplicity

/-!
# Finite Galois-stable families of residue embeddings

A finite family of embeddings into a finite Galois field may contain
repetitions.  If postcomposition by every Galois automorphism permutes the
family, every embedding occurs with the same multiplicity.  Consequently the
size of the family is its residue degree times that multiplicity.
-/

open scoped BigOperators

namespace AllCharacteristics

universe u v

section

variable (K F E : Type u) [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E]
  [FiniteDimensional K F] [Algebra.IsSeparable K F]
  [FiniteDimensional K E] [IsGalois K E]
variable {J : Type v} [Fintype J]

/-- The number of indices in a finite family which realize a specified
embedding. -/
noncomputable def embeddingFiberMultiplicity
    (e : J → (F →ₐ[K] E)) (phi : F →ₐ[K] E) : ℕ :=
  by
    classical
    exact Fintype.card {j : J // e j = phi}

/-- A permutation which postcomposes every member of the family by `g`
induces an equivalence between the corresponding embedding fibers. -/
noncomputable def embeddingFiberEquiv
    (e : J → (F →ₐ[K] E))
    (g : E ≃ₐ[K] E) (phi : F →ₐ[K] E)
    (tau : J ≃ J)
    (htau : ∀ j : J, e (tau j) = g.toAlgHom.comp (e j)) :
    {j : J // e j = phi} ≃
      {j : J // e j = g.toAlgHom.comp phi} where
  toFun j := ⟨tau j.1, by rw [htau, j.2]⟩
  invFun j := ⟨tau.symm j.1, by
    have h := htau (tau.symm j.1)
    rw [tau.apply_symm_apply] at h
    apply AlgHom.ext
    intro x
    apply g.injective
    have hfun := DFunLike.congr_fun h x
    have hjfun := DFunLike.congr_fun j.2 x
    exact hfun.symm.trans hjfun⟩
  left_inv j := by
    apply Subtype.ext
    exact tau.symm_apply_apply j.1
  right_inv j := by
    apply Subtype.ext
    exact tau.apply_symm_apply j.1

/-- The fiber multiplicity is invariant under Galois postcomposition when
the whole finite family is permuted accordingly. -/
theorem embeddingFiberMultiplicity_galoisInvariant
    (e : J → (F →ₐ[K] E))
    (hstable : ∀ g : E ≃ₐ[K] E, ∃ tau : J ≃ J,
      ∀ j : J, e (tau j) = g.toAlgHom.comp (e j))
    (g : E ≃ₐ[K] E) (phi : F →ₐ[K] E) :
    embeddingFiberMultiplicity K F E e (g.toAlgHom.comp phi) =
      embeddingFiberMultiplicity K F E e phi := by
  classical
  obtain ⟨tau, htau⟩ := hstable g
  exact (Fintype.card_congr
    (embeddingFiberEquiv K F E e g phi tau htau)).symm

/-- Summing all embedding-fiber multiplicities counts every index exactly
once. -/
theorem sum_embeddingFiberMultiplicity
    (e : J → (F →ₐ[K] E)) :
    ∑ phi : F →ₐ[K] E, embeddingFiberMultiplicity K F E e phi =
      Fintype.card J := by
  classical
  let equiv : (Σ phi : F →ₐ[K] E, {j : J // e j = phi}) ≃ J :=
    { toFun := fun z ↦ z.2.1
      invFun := fun j ↦ ⟨e j, ⟨j, rfl⟩⟩
      left_inv := by
        rintro ⟨phi, j, hj⟩
        subst phi
        rfl
      right_inv := fun _ ↦ rfl }
  calc
    ∑ phi : F →ₐ[K] E, embeddingFiberMultiplicity K F E e phi =
        Fintype.card (Σ phi : F →ₐ[K] E, {j : J // e j = phi}) := by
          simp only [embeddingFiberMultiplicity, Fintype.card_sigma]
    _ = Fintype.card J := Fintype.card_congr equiv

/-- A nonempty finite Galois-stable family of embeddings has cardinality
equal to the residue degree times the common embedding multiplicity. -/
theorem card_eq_finrank_mul_embeddingFiberMultiplicity
    (e : J → (F →ₐ[K] E))
    (hstable : ∀ g : E ≃ₐ[K] E, ∃ tau : J ≃ J,
      ∀ j : J, e (tau j) = g.toAlgHom.comp (e j))
    (j0 : J) :
    Fintype.card J = Module.finrank K F *
      embeddingFiberMultiplicity K F E e (e j0) := by
  letI : Algebra F E := (e j0).toRingHom.toAlgebra
  letI : IsScalarTower K F E := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact ((e j0).commutes r).symm
  rw [← sum_embeddingFiberMultiplicity K F E e]
  exact sum_galoisInvariantMultiplicity K F E
    (embeddingFiberMultiplicity K F E e)
    (embeddingFiberMultiplicity_galoisInvariant K F E e hstable)
    (e j0)

end

end AllCharacteristics

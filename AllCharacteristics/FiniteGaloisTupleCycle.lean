import AllCharacteristics.FiniteGaloisTupleMultiplicity

/-!
# The effective cycle of a finite Galois-stable tuple

The coordinates of a finite Galois-stable tuple are grouped by their closed
support points.  The common residue-embedding multiplicity is used as the
coefficient of each support point.  The resulting effective zero-cycle has
degree equal to the number of tuple coordinates.
-/

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace AllCharacteristics

universe u

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
  [IsSeparated f] [LocallyOfFiniteType f]
variable {n : ℕ}

/-- The integral coefficient of a closed support point in a finite
Galois-stable tuple.  Off the finite support it is zero. -/
noncomputable def finiteGaloisTupleMultiplicity
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (x : closedPoints X) : ℕ := by
  classical
  let J := {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x}
  letI : Fintype J := Fintype.ofFinite _
  letI : Algebra K (X.residueField x.1) := pointAlgebra f x.1
  exact if hx : Nonempty J then
    embeddingFiberMultiplicity K (X.residueField x.1) E
      (finiteGaloisTupleResidueEmbedding f a ha x)
      (finiteGaloisTupleResidueEmbedding f a ha x (Classical.choice hx))
  else 0

/-- At a support point, the coordinate-fiber cardinality is the residue
degree times the chosen cycle multiplicity. -/
theorem finiteGaloisTuple_support_card_eq_residueDegree_mul_multiplicity
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (hstable : ∀ g : E ≃ₐ[K] E, ∃ tau : Equiv.Perm (Fin n),
      ∀ i, Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a i = a (tau i))
    (x : closedPoints X)
    (hx : Nonempty
      {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x}) :
    Nat.card {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x} =
      f.residueDegree x.1 * finiteGaloisTupleMultiplicity f a ha x := by
  classical
  let J := {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x}
  letI : Fintype J := Fintype.ofFinite _
  letI : Algebra K (X.residueField x.1) := pointAlgebra f x.1
  have hcard := finiteGaloisTuple_support_card_eq_residueDegree_mul
    f a ha hstable x (Classical.choice hx)
  simpa only [finiteGaloisTupleMultiplicity, dif_pos hx] using hcard

/-- The effective zero-cycle obtained by grouping the tuple coordinates by
their closed support and retaining their Galois-invariant multiplicities. -/
noncomputable def finiteGaloisTupleCycle
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    EffectiveZeroCycle X := by
  classical
  exact ∑ x ∈ Finset.univ.image
      (finiteGaloisTupleSupportPoint f a ha),
    Finsupp.single x (finiteGaloisTupleMultiplicity f a ha x)

/-- The degree of a finite sum of effective closed points is the corresponding
weighted sum of their residue degrees. -/
theorem EffectiveZeroCycle.degree_sum_single
    {Y : Scheme.{u}} (g : X ⟶ Y)
    (s : Finset (closedPoints X)) (m : closedPoints X → ℕ) :
    EffectiveZeroCycle.degree g
        (∑ x ∈ s, Finsupp.single x (m x)) =
      ∑ x ∈ s, m x * g.residueDegree x.1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [EffectiveZeroCycle.degree]
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      change EffectiveZeroCycle.degree g
        (Finsupp.single x (m x) + ∑ y ∈ s, Finsupp.single y (m y)) = _
      unfold EffectiveZeroCycle.degree
      rw [Finsupp.sum_add_index']
      · rw [Finsupp.sum_single_index]
        exact congrArg (m x * g.residueDegree x.1 + ·) ih
        exact Nat.zero_mul _
      · intro y
        exact Nat.zero_mul _
      · intro y p q
        exact Nat.add_mul p q _

/-- A finite Galois-stable ordered tuple determines an effective zero-cycle
over the ground field whose degree is exactly the tuple length. -/
theorem finiteGaloisTupleCycle_degree
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (hstable : ∀ g : E ≃ₐ[K] E, ∃ tau : Equiv.Perm (Fin n),
      ∀ i, Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a i = a (tau i)) :
    EffectiveZeroCycle.degree f (finiteGaloisTupleCycle f a ha) = n := by
  classical
  let support : Fin n → closedPoints X :=
    finiteGaloisTupleSupportPoint f a ha
  let s : Finset (closedPoints X) := Finset.univ.image support
  let m : closedPoints X → ℕ := finiteGaloisTupleMultiplicity f a ha
  change EffectiveZeroCycle.degree f
    (∑ x ∈ s, Finsupp.single x (m x)) = n
  rw [EffectiveZeroCycle.degree_sum_single]
  have hpartition := Finset.card_eq_sum_card_image support Finset.univ
  calc
    ∑ x ∈ s, m x * f.residueDegree x.1 =
        ∑ x ∈ s,
          (Finset.univ.filter (fun i : Fin n ↦ support i = x)).card := by
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
      have hxnonempty : Nonempty
          {j : Fin n // finiteGaloisTupleSupportPoint f a ha j = x} :=
        ⟨⟨i, hi⟩⟩
      have hcard :=
        finiteGaloisTuple_support_card_eq_residueDegree_mul_multiplicity
          f a ha hstable x hxnonempty
      let J := {j : Fin n // finiteGaloisTupleSupportPoint f a ha j = x}
      letI : Fintype J := Fintype.ofFinite _
      let fiber := {j ∈ (Finset.univ : Finset (Fin n)) | support j = x}
      let equiv : J ≃ fiber :=
        { toFun := fun j ↦ ⟨j.1, by
            simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
            exact j.2⟩
          invFun := fun j ↦ ⟨j.1, by
            simpa only [support, fiber, Finset.mem_filter, Finset.mem_univ,
              true_and] using j.2⟩
          left_inv := fun j ↦ by ext; rfl
          right_inv := fun j ↦ by ext; rfl }
      have hfiber : fiber.card = Nat.card J := by
        rw [Nat.card_eq_fintype_card]
        exact (Fintype.card_coe fiber).symm.trans
          (Fintype.card_congr equiv).symm
      change m x * f.residueDegree x.1 = fiber.card
      rw [hfiber, hcard]
      exact Nat.mul_comm _ _
    _ = Finset.univ.card := hpartition.symm
    _ = n := Finset.card_fin n

end AllCharacteristics

import AllCharacteristics.FiniteFieldPointResidueEmbedding
import AllCharacteristics.GaloisInvariantEmbeddingFibers

/-!
# Multiplicities of a finite Galois-stable tuple

For a tuple of points over a finite Galois extension, every coordinate has a
closed image over the ground field.  If every Galois automorphism permutes the
tuple, the number of coordinates above each closed support point is its
residue degree times an integral multiplicity.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
  [IsSeparated f] [LocallyOfFiniteType f]
variable {n : ℕ}

/-- The closed support point of one coordinate in a finite field-valued
tuple. -/
noncomputable def finiteGaloisTupleSupportPoint
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (i : Fin n) : closedPoints X :=
  finiteFieldPointClosedPoint f (a i) (ha i)

@[simp]
theorem finiteGaloisTupleSupportPoint_val
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (i : Fin n) :
    (finiteGaloisTupleSupportPoint f a ha i).1 =
      a i (IsLocalRing.closedPoint E) := rfl

/-- The residue embedding attached to a coordinate whose closed support is
the specified point. -/
noncomputable def finiteGaloisTupleResidueEmbedding
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (x : closedPoints X)
    (i : {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x}) :
    letI := pointAlgebra f x.1
    X.residueField x.1 →ₐ[K] E := by
  letI : Algebra K (X.residueField x.1) := pointAlgebra f x.1
  apply fieldPointResidueAlgHomAt f (a i.1) (ha i.1) x.1
  have h := congrArg Subtype.val i.2
  simpa only [finiteGaloisTupleSupportPoint_val] using h

/-- Galois precomposition does not change the closed support of a coordinate
which is carried to another coordinate. -/
theorem finiteGaloisTupleSupportPoint_permute
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (g : E ≃ₐ[K] E) (tau : Equiv.Perm (Fin n))
    (htau : ∀ i, Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a i =
      a (tau i)) (i : Fin n) :
    finiteGaloisTupleSupportPoint f a ha (tau i) =
      finiteGaloisTupleSupportPoint f a ha i := by
  apply Subtype.ext
  simp only [finiteGaloisTupleSupportPoint_val]
  have hpoint := congrArg
    (fun m : Spec (.of E) ⟶ X ↦ m (IsLocalRing.closedPoint E))
    (htau i)
  have hclosed : Spec.map (CommRingCat.ofHom g.toRingHom)
      (IsLocalRing.closedPoint E) = IsLocalRing.closedPoint E :=
    Subsingleton.elim _ _
  change a i (Spec.map (CommRingCat.ofHom g.toRingHom)
      (IsLocalRing.closedPoint E)) =
    a (tau i) (IsLocalRing.closedPoint E) at hpoint
  rw [hclosed] at hpoint
  exact hpoint.symm

/-- The coordinate indices above a fixed closed support point form a
Galois-stable finite family of residue embeddings. -/
theorem finiteGaloisTupleResidueEmbedding_stable
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (hstable : ∀ g : E ≃ₐ[K] E, ∃ tau : Equiv.Perm (Fin n),
      ∀ i, Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a i = a (tau i))
    (x : closedPoints X) :
    letI := pointAlgebra f x.1
    ∀ g : E ≃ₐ[K] E,
      ∃ tau :
        {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x} ≃
          {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x},
        ∀ i,
          finiteGaloisTupleResidueEmbedding f a ha x (tau i) =
            g.toAlgHom.comp
              (finiteGaloisTupleResidueEmbedding f a ha x i) := by
  classical
  letI : Algebra K (X.residueField x.1) := pointAlgebra f x.1
  intro g
  obtain ⟨tau, htau⟩ := hstable g
  let tauX :
      {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x} ≃
        {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x} :=
    { toFun := fun i ↦ ⟨tau i.1, by
        rw [finiteGaloisTupleSupportPoint_permute f a ha g tau htau i.1,
          i.2]⟩
      invFun := fun i ↦ ⟨tau.symm i.1, by
        have hs := finiteGaloisTupleSupportPoint_permute
          f a ha g tau htau (tau.symm i.1)
        rw [tau.apply_symm_apply] at hs
        exact hs.symm.trans i.2⟩
      left_inv := fun i ↦ by
        apply Subtype.ext
        exact tau.symm_apply_apply i.1
      right_inv := fun i ↦ by
        apply Subtype.ext
        exact tau.apply_symm_apply i.1 }
  refine ⟨tauX, ?_⟩
  intro i
  let hax : a i.1 (IsLocalRing.closedPoint E) = x.1 := by
    have h := congrArg Subtype.val i.2
    simpa only [finiteGaloisTupleSupportPoint_val] using h
  have hs : finiteGaloisTupleSupportPoint f a ha (tau i.1) = x := by
    rw [finiteGaloisTupleSupportPoint_permute f a ha g tau htau i.1,
      i.2]
  let hbx : a (tau i.1) (IsLocalRing.closedPoint E) = x.1 := by
    have h := congrArg Subtype.val hs
    simpa only [finiteGaloisTupleSupportPoint_val] using h
  have h := fieldPointResidueAlgHomAt_precomp f x
    (a i.1) (a (tau i.1)) (ha i.1) (ha (tau i.1))
    hax hbx g (htau i.1)
  change fieldPointResidueAlgHomAt f (a (tau i.1)) (ha (tau i.1)) x.1 _ =
    g.toAlgHom.comp
      (fieldPointResidueAlgHomAt f (a i.1) (ha i.1) x.1 _)
  exact h

/-- Above each support point, the number of tuple coordinates is the residue
degree times an integral multiplicity. -/
theorem finiteGaloisTuple_support_card_eq_residueDegree_mul
    (a : Fin n → (Spec (.of E) ⟶ X))
    (ha : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (hstable : ∀ g : E ≃ₐ[K] E, ∃ tau : Equiv.Perm (Fin n),
      ∀ i, Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a i = a (tau i))
    (x : closedPoints X)
    (i0 : {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x}) :
    letI := pointAlgebra f x.1
    letI : Fintype
        {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x} :=
      Fintype.ofFinite _
    Nat.card
        {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x} =
      f.residueDegree x.1 *
        embeddingFiberMultiplicity K (X.residueField x.1) E
          (finiteGaloisTupleResidueEmbedding f a ha x)
          (finiteGaloisTupleResidueEmbedding f a ha x i0) := by
  classical
  letI : Algebra K (X.residueField x.1) := pointAlgebra f x.1
  letI : Fintype
      {i : Fin n // finiteGaloisTupleSupportPoint f a ha i = x} :=
    Fintype.ofFinite _
  letI : Module.Finite K (X.residueField x.1) :=
    closedPoint_moduleFinite f x
  letI : Algebra.IsSeparable K (X.residueField x.1) := inferInstance
  have hcard := card_eq_finrank_mul_embeddingFiberMultiplicity
    K (X.residueField x.1) E
      (finiteGaloisTupleResidueEmbedding f a ha x)
      (finiteGaloisTupleResidueEmbedding_stable f a ha hstable x) i0
  rw [closedPoint_finrank_eq_residueDegree f x] at hcard
  simpa only [Nat.card_eq_fintype_card] using hcard

end AllCharacteristics

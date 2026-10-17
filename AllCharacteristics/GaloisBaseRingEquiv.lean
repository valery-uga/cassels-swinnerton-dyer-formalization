import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Transporting finite Galois extensions across an isomorphism of base fields

Invariant-quotient residue theory naturally produces an extension over the
residue field of the quotient prime.  A rational quotient point identifies
that field with the original ground field.  The definitions and lemmas here
make that change of base field explicit while leaving the extension field
unchanged.
-/

namespace AllCharacteristics

universe u

variable (F K E : Type u) [Field F] [Field K] [Field E] [Algebra F E]

/-- Regard an `F`-algebra as a `K`-algebra along a ring equivalence
`F ≃+* K`. -/
@[instance_reducible]
noncomputable def algebraOfBaseRingEquiv (e : F ≃+* K) : Algebra K E :=
  ((algebraMap F E).comp e.symm.toRingHom).toAlgebra

@[simp]
theorem algebraMap_algebraOfBaseRingEquiv (e : F ≃+* K) (x : K) :
    letI := algebraOfBaseRingEquiv F K E e
    algebraMap K E x = algebraMap F E (e.symm x) := rfl

/-- An automorphism over the transported base field is the same underlying
ring automorphism over the original base field. -/
noncomputable def algEquivOfBaseRingEquiv (e : F ≃+* K)
    (g : @AlgEquiv K E E _ _ _
      (algebraOfBaseRingEquiv F K E e)
      (algebraOfBaseRingEquiv F K E e)) : E ≃ₐ[F] E := by
  letI : Algebra K E := algebraOfBaseRingEquiv F K E e
  exact AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (by
    intro x
    have hg := g.commutes (e x)
    rw [algebraMap_algebraOfBaseRingEquiv F K E e] at hg
    simpa using hg)

/-- Module-finiteness is preserved when the base field is replaced by an
isomorphic field. -/
theorem moduleFinite_algebraOfBaseRingEquiv
    (e : F ≃+* K) [Module.Finite F E] :
    letI := algebraOfBaseRingEquiv F K E e
    Module.Finite K E := by
  letI : Algebra K E := algebraOfBaseRingEquiv F K E e
  let t : E →ₛₗ[e.toRingHom] E :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        simp [Algebra.smul_def, algebraOfBaseRingEquiv] }
  exact Module.Finite.of_surjective t Function.surjective_id

/-- The extension degree is unchanged by replacing the base field with an
isomorphic field. -/
theorem finrank_algebraOfBaseRingEquiv
    (e : F ≃+* K) [FiniteDimensional F E] :
    letI := algebraOfBaseRingEquiv F K E e
    Module.finrank K E = Module.finrank F E := by
  letI : Algebra K E := algebraOfBaseRingEquiv F K E e
  letI : Module.Finite K E := moduleFinite_algebraOfBaseRingEquiv F K E e
  symm
  apply Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl E)
  ext x
  simp [algebraOfBaseRingEquiv]

/-- A Galois extension remains Galois after replacing its base field by an
isomorphic field. -/
theorem isGalois_algebraOfBaseRingEquiv
    (e : F ≃+* K) [IsGalois F E] :
    letI := algebraOfBaseRingEquiv F K E e
    IsGalois K E := by
  letI : Algebra K E := algebraOfBaseRingEquiv F K E e
  apply IsGalois.of_equiv_equiv
    (F := F) (E := E) (M := K) (N := E)
    (f := e) (g := RingEquiv.refl E)
  ext x
  simp [algebraOfBaseRingEquiv]

end AllCharacteristics

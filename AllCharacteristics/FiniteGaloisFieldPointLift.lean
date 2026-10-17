import AllCharacteristics.FiniteSurjectiveFieldPointLift
import Mathlib.FieldTheory.Galois.Basic

/-!
# Galois splitting fields for finite-extension point lifts

In characteristic zero, the finite extension which lifts a point through a
finite surjective morphism embeds in a finite Galois extension of the ground
field.  Base-changing the lift to that normal closure preserves its exact
quotient equation.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics
universe u

/-- Spectrum maps associated with a scalar tower compose as expected. -/
theorem specMap_algebraMap_comp
    (K E L : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] :
    Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (IsScalarTower.algebraMap_apply K E L x).symm

/-- A finite-extension lift of a point admits a finite Galois splitting
field in characteristic zero, and the resulting point still lies over the
original ground-field point. -/
theorem FiniteFieldPointLift.exists_finiteGaloisPointLift
    {K : Type u} [Field K] [CharZero K]
    {Y Q : Scheme.{u}} {q : Y ⟶ Q} {c : Spec (.of K) ⟶ Q}
    (d : FiniteFieldPointLift q c) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra d.E L)
      (_ : IsScalarTower K d.E L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (a : Spec (.of L) ⟶ Y),
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ c = a ≫ q ∧
      Spec.map (CommRingCat.ofHom (algebraMap d.E L)) ≫ d.point = a := by
  let Omega : Type u := AlgebraicClosure K
  letI : Field Omega := inferInstanceAs (Field (AlgebraicClosure K))
  letI : Algebra K Omega := inferInstanceAs (Algebra K (AlgebraicClosure K))
  let emb : d.E →ₐ[K] Omega := IsAlgClosed.lift
  letI : Algebra d.E Omega := emb.toRingHom.toAlgebra
  letI : IsScalarTower K d.E Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (emb.commutes r).symm
  let L : Type u := IntermediateField.normalClosure K d.E Omega
  letI : Field L := inferInstanceAs
    (Field (IntermediateField.normalClosure K d.E Omega))
  letI : Algebra K L := inferInstanceAs
    (Algebra K (IntermediateField.normalClosure K d.E Omega))
  letI : Algebra d.E L := inferInstanceAs
    (Algebra d.E (IntermediateField.normalClosure K d.E Omega))
  letI : IsScalarTower K d.E L := inferInstanceAs
    (IsScalarTower K d.E (IntermediateField.normalClosure K d.E Omega))
  letI : FiniteDimensional K L := inferInstanceAs
    (FiniteDimensional K (IntermediateField.normalClosure K d.E Omega))
  letI : IsGalois K L := inferInstanceAs
    (IsGalois K (IntermediateField.normalClosure K d.E Omega))
  let a : Spec (.of L) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap d.E L)) ≫ d.point
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, a, ?_, rfl⟩
  calc
    Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ c =
        (Spec.map (CommRingCat.ofHom (algebraMap d.E L)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K d.E))) ≫ c := by
      rw [specMap_algebraMap_comp K d.E L]
    _ = Spec.map (CommRingCat.ofHom (algebraMap d.E L)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap K d.E)) ≫ c) :=
      Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom (algebraMap d.E L)) ≫
        (d.point ≫ q) := congrArg
          (Spec.map (CommRingCat.ofHom (algebraMap d.E L)) ≫ ·) d.quotient_eq
    _ = a ≫ q := Category.assoc _ _ _ |>.symm

end AllCharacteristics

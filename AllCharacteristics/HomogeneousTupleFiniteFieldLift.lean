import AllCharacteristics.FiniteGaloisFieldPointLift
import AllCharacteristics.HomogeneousTupleQuotient

/-!
# Finite-field ordered lifts of unordered homogeneous tuples

A rational point of the full unordered-tuple quotient has an ordered lift
after a finite field extension.  Besides the quotient equation, the lift is
proved to lie in the original projective fiber over that extension.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics
namespace HomogeneousProjective
universe u

variable {K : Type u} [Field K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (n : ℕ)

/-- The canonical finite-extension ordered lift attached to a rational point
of the full unordered-tuple quotient. -/
noncomputable def tupleQuotientFiniteFieldOrderedLift
    (c : Spec (.of K) ⟶ tupleQuotient I n) :
    FiniteFieldPointLift (tupleQuotientMap I n) c :=
  finiteFieldPointLiftOfFiniteSurjective (tupleQuotientMap I n) c

/-- The ordered lift lies over the scalar extension of the original ground
field point. -/
theorem tupleQuotientFiniteFieldOrderedLift_toBase
    (c : Spec (.of K) ⟶ tupleQuotient I n)
    (hc : c ≫ tupleQuotientToBase I n = 𝟙 _) :
    let d := tupleQuotientFiniteFieldOrderedLift I n c
    d.point ≫ (orderedFamilyPowerOver (toBase I) n).hom =
      Spec.map (CommRingCat.ofHom (algebraMap K d.E)) := by
  let d := tupleQuotientFiniteFieldOrderedLift I n c
  let π : Spec (.of d.E) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K d.E))
  have hquot := congrArg (· ≫ tupleQuotientToBase I n) d.quotient_eq
  dsimp only [π]
  rw [Category.assoc, hc, Category.comp_id,
    Category.assoc, tupleQuotientMap_toBase] at hquot
  exact hquot.symm

/-- Every marked coordinate of the ordered lift is a point of the original
homogeneous projective scheme over the same finite extension. -/
theorem tupleQuotientFiniteFieldOrderedLift_coordinate_toBase
    (c : Spec (.of K) ⟶ tupleQuotient I n)
    (hc : c ≫ tupleQuotientToBase I n = 𝟙 _)
    (i : Fin n) :
    let d := tupleQuotientFiniteFieldOrderedLift I n c
    d.point ≫ (orderedFamilyCoordinate (toBase I) n i).left ≫ toBase I =
      Spec.map (CommRingCat.ofHom (algebraMap K d.E)) := by
  let d := tupleQuotientFiniteFieldOrderedLift I n c
  calc
    d.point ≫ (orderedFamilyCoordinate (toBase I) n i).left ≫ toBase I =
        d.point ≫ (orderedFamilyPowerOver (toBase I) n).hom := by
      have hw := (orderedFamilyCoordinate (toBase I) n i).w
      change (orderedFamilyCoordinate (toBase I) n i).left ≫ toBase I =
        (orderedFamilyPowerOver (toBase I) n).hom at hw
      simpa only [Category.assoc] using congrArg (d.point ≫ ·) hw
    _ = Spec.map (CommRingCat.ofHom (algebraMap K d.E)) :=
      tupleQuotientFiniteFieldOrderedLift_toBase I n c hc

/-- In characteristic zero, the ordered lift may be taken over a finite
Galois extension of the ground field.  Its quotient is the scalar extension
of the original rational unordered tuple, and it remains in the correct
projective fiber. -/
theorem tupleQuotient_exists_finiteGalois_orderedLift
    [CharZero K]
    (c : Spec (.of K) ⟶ tupleQuotient I n)
    (hc : c ≫ tupleQuotientToBase I n = 𝟙 _) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (a : Spec (.of L) ⟶ (orderedFamilyPowerOver (toBase I) n).left),
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ c =
          a ≫ tupleQuotientMap I n ∧
      a ≫ (orderedFamilyPowerOver (toBase I) n).hom =
          Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  let d := tupleQuotientFiniteFieldOrderedLift I n c
  obtain ⟨L, _, _, _, _, _, _, a, hquot, -⟩ :=
    d.exists_finiteGaloisPointLift
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    a, hquot, ?_⟩
  have h := congrArg (· ≫ tupleQuotientToBase I n) hquot
  rw [Category.assoc, hc, Category.comp_id,
    Category.assoc, tupleQuotientMap_toBase] at h
  exact h.symm

end HomogeneousProjective
end AllCharacteristics

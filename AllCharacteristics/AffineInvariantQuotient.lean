import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Affine quotients by finite groups

The spectrum of the actual invariant subalgebra supplies the affine quotient.
For a finite group the quotient map is integral and surjective, with its
underlying topological map a quotient map. For a finitely generated original
algebra the quotient morphism is finite and proper. The original coefficient
ring is retained throughout.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Pointwise
namespace AllCharacteristics
universe u v
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (G : Type v) [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- The actual fixed subalgebra contains every invariant element. -/
instance isInvariant_fixedSubalgebra :
    Algebra.IsInvariant (FixedPoints.subalgebra R A G) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩

/-- A ring is integral over the invariants of any finite group of automorphisms. -/
instance isIntegral_fixedSubalgebra [Finite G] :
    Algebra.IsIntegral (FixedPoints.subalgebra R A G) A :=
  Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R A G) A G

/-- A finitely generated algebra is finite as a module over its finite-group invariants. -/
instance finite_fixedSubalgebra [Finite G] [Algebra.FiniteType R A] :
    Module.Finite (FixedPoints.subalgebra R A G) A := by
  have : Algebra.FiniteType (FixedPoints.subalgebra R A G) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (FixedPoints.subalgebra R A G) A
  exact Algebra.IsIntegral.finite

/-- The actual affine scheme defined by the invariant subalgebra. -/
noncomputable def affineInvariantQuotient : Scheme.{u} :=
  Spec (.of (FixedPoints.subalgebra R A G))

/-- The canonical morphism from the original affine scheme to its invariant spectrum. -/
noncomputable def affineInvariantQuotientMap : Spec (.of A) ⟶ affineInvariantQuotient R A G :=
  Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A))

/-- The invariant spectrum retains its structure morphism over the original ring. -/
noncomputable def affineInvariantQuotientToBase : affineInvariantQuotient R A G ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))

/-- The affine quotient map preserves the original coefficient-ring structure. -/
theorem affineInvariantQuotientMap_toBase :
    affineInvariantQuotientMap R A G ≫ affineInvariantQuotientToBase R A G =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G))) = _
  rw [← Spec.map_comp]
  rfl

/-- The actual affine quotient map for a finite group is integral. -/
instance isIntegralHom_affineInvariantQuotientMap [Finite G] :
    IsIntegralHom (affineInvariantQuotientMap R A G) := by
  change IsIntegralHom (Spec.map
    (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A)))
  exact IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)

/-- Every point of the invariant spectrum has a preimage on the original spectrum. -/
instance surjective_affineInvariantQuotientMap [Finite G] :
    Surjective (affineInvariantQuotientMap R A G) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R A G) A))
  exact Algebra.IsIntegral.comap_surjective (FixedPoints.subalgebra R A G) A

/-- For a finitely generated original algebra the actual affine quotient map is finite. -/
instance isFinite_affineInvariantQuotientMap [Finite G] [Algebra.FiniteType R A] :
    IsFinite (affineInvariantQuotientMap R A G) := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A)))
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The finite quotient morphism is proper over its actual invariant spectrum. -/
instance isProper_affineInvariantQuotientMap [Finite G] [Algebra.FiniteType R A] :
    IsProper (affineInvariantQuotientMap R A G) := by
  infer_instance

/-- The underlying map of the actual affine quotient is a topological quotient map. -/
theorem isQuotientMap_affineInvariantQuotientMap [Finite G] :
    Topology.IsQuotientMap (affineInvariantQuotientMap R A G) :=
  (affineInvariantQuotientMap R A G).isClosedMap.isQuotientMap
    (affineInvariantQuotientMap R A G).continuous (affineInvariantQuotientMap R A G).surjective

/-- Two prime ideals have the same image in the invariant spectrum exactly
when they belong to the same group orbit. -/
theorem affineInvariantQuotientMap_eq_iff [Finite G] (p q : PrimeSpectrum A) :
    affineInvariantQuotientMap R A G p = affineInvariantQuotientMap R A G q ↔
      ∃ g : G, q.asIdeal = g • p.asIdeal := by
  constructor
  · intro h
    apply Algebra.IsInvariant.exists_smul_of_under_eq (FixedPoints.subalgebra R A G) A G
    exact congrArg PrimeSpectrum.asIdeal h
  · rintro ⟨g, hg⟩
    apply PrimeSpectrum.ext
    change p.asIdeal.under (FixedPoints.subalgebra R A G) =
      q.asIdeal.under (FixedPoints.subalgebra R A G)
    rw [hg, Ideal.under_smul]

end AllCharacteristics

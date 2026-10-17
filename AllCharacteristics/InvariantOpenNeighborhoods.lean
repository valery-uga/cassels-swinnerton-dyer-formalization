import AllCharacteristics.EquivariantAffineOpenGeometry
import AllCharacteristics.AffineInvariantOpenDescent

/-!
# Invariant principal neighborhoods for equivariant affine open immersions

Every point of the source quotient has a principal neighborhood defined by
an invariant on the target, whose original principal open lies in the image
of the given open immersion. No averaging or restriction on the group order
is required.
-/

open AlgebraicGeometry CategoryTheory
open scoped Pointwise
namespace AllCharacteristics
universe u v
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [SMulCommClass G R A] [SMulCommClass G R B]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)
variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))]

/-- Every source quotient point lies above an invariant principal open contained
in the image of the original affine open immersion. -/
theorem exists_invariant_basicOpen_at_source_quotient
    (x : affineInvariantQuotient R B G) :
    ∃ t : FixedPoints.subalgebra R A G,
      x ∈ PrimeSpectrum.basicOpen (equivariantInvariantMap R A B G φ hφ t) ∧
        (PrimeSpectrum.basicOpen t.val : Set (PrimeSpectrum A)) ⊆
          Set.range (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨p, rfl⟩ := (affineInvariantQuotientMap R B G).surjective x
  let W := (Spec.map (CommRingCat.ofHom φ)).opensRange
  have hW : ∀ (a b : PrimeSpectrum A) (g : G),
      b.asIdeal = g • a.asIdeal → a ∈ W → b ∈ W :=
    SpecMap_range_stable A B G φ hφ
  obtain ⟨t, ht, hsub⟩ := exists_invariant_basicOpen_inside R A G W hW
    (Spec.map (CommRingCat.ofHom φ) p) ⟨p, rfl⟩
  exact ⟨t, ht, hsub⟩

end AllCharacteristics

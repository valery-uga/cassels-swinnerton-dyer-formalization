import AllCharacteristics.InvariantQuotientOpenImmersion

/-!
# Cartesian quotient squares for equivariant affine open immersions

The descended open immersion has exactly the quotient image of the original
open as its range. Stability of the original open then makes the actual
quotient square Cartesian.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [SMulCommClass G R A] [SMulCommClass G R B]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)

/-- The range of the actual induced invariant quotient map is the quotient image
of the original spectrum map. -/
theorem affineInvariantQuotientMorphism_range :
    Set.range (affineInvariantQuotientMorphism R A B G φ hφ) =
      (affineInvariantQuotientMap R A G) '' Set.range (Spec.map (CommRingCat.ofHom φ)) := by
  have he (p : Spec (.of B)) :
      affineInvariantQuotientMorphism R A B G φ hφ (affineInvariantQuotientMap R B G p) =
        affineInvariantQuotientMap R A G (Spec.map (CommRingCat.ofHom φ) p) :=
    congrArg (fun m : Spec (.of B) ⟶ affineInvariantQuotient R A G ↦ m p)
      (affineInvariantQuotientMorphism_square R A B G φ hφ)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨p, rfl⟩ := (affineInvariantQuotientMap R B G).surjective y
    exact ⟨_, ⟨p, rfl⟩, (he p).symm⟩
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨affineInvariantQuotientMap R B G p, he p⟩

/-- An equivariant affine open immersion and its actual invariant quotient
morphism form a Cartesian square. -/
theorem isPullback_affineInvariantQuotientMorphism
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))] :
    IsPullback (Spec.map (CommRingCat.ofHom φ)) (affineInvariantQuotientMap R B G)
      (affineInvariantQuotientMap R A G) (affineInvariantQuotientMorphism R A B G φ hφ) := by
  have : IsOpenImmersion (affineInvariantQuotientMorphism R A B G φ hφ) :=
    isOpenImmersion_affineInvariantQuotientMorphism R A B G φ hφ
  apply (IsOpenImmersion.isPullback (affineInvariantQuotientMap R B G)
    (Spec.map (CommRingCat.ofHom φ)) (affineInvariantQuotientMorphism R A B G φ hφ)
    (affineInvariantQuotientMap R A G)
    (affineInvariantQuotientMorphism_square R A B G φ hφ).symm ?_).flip
  apply SetLike.coe_injective
  change (affineInvariantQuotientMap R A G) ⁻¹'
    Set.range (affineInvariantQuotientMorphism R A B G φ hφ) =
      Set.range (Spec.map (CommRingCat.ofHom φ))
  rw [affineInvariantQuotientMorphism_range]
  exact preimage_image_affineInvariantOpen R A G
    (Spec.map (CommRingCat.ofHom φ)).opensRange (SpecMap_range_stable A B G φ hφ)

end AllCharacteristics
